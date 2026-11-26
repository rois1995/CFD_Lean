import CFDLean.Exec.MusclKernel

/-! Burgers E0c-K, the limiter kernel: an executable array implementation of the periodic MUSCL-Rusanov scheme for the
1D Burgers equation with a choice of slope limiter (none = the unlimited central slope, minmod, MC, superbee,
van Leer, van Albada), with Forward Euler and SSPRK2/SSPRK3 in Shu-Osher form. Generic over the arithmetic `α` of
`CFDLean.Exec.Kernel`; no Mathlib. Minmod, MC and superbee are comparison-free (`max`, negation, zero, addition);
van Leer and van Albada divide by `a + b` and `a² + b²` and need the sign test of the class `ScalarSign`. -/
namespace CFDLean.Exec

/-- Sign test for the limiters that need a branch. -/
class ScalarSign (α : Type) [Scalar α] where
  /-- `true` exactly when the argument is strictly positive. -/
  isPos : α → Bool

/-- `Float` sign test: `0 < x` (IEEE comparison; `false` for `NaN`). -/
instance : ScalarSign Float where
  isPos x := decide (0 < x)

/-- The slope limiters of the kernel. `none` is the unlimited central slope. -/
inductive Limiter where
  | none | minmod | mc | superbee | vanLeer | vanAlbada
  deriving DecidableEq, Repr

/-- `false` only for the unlimited central slope. -/
def Limiter.isLimited : Limiter → Bool
  | .none => false
  | _ => true

namespace Scalar

variable {α : Type} [Scalar α]

/-- maxmod of two numbers of the same sign (or zero), comparison-free: `max 0 (max x y) + min 0 (min x y)`. -/
def maxmodSame (x y : α) : α := Scalar.max 0 (Scalar.max x y) + Scalar.min 0 (Scalar.min x y)

end Scalar

open Scalar

variable {α : Type} [Scalar α] [ScalarSign α]

/-- The kernel slope of limiter `L` from the backward difference `a` and the forward difference `b`. -/
def limiterSlope (L : Limiter) (a b : α) : α :=
  match L with
  | .none => (a + b) / two
  | .minmod => Scalar.minmod a b
  | .mc => Scalar.minmod (Scalar.minmod (two * a) (two * b)) ((a + b) / two)
  | .superbee => Scalar.maxmodSame (Scalar.minmod (two * a) b) (Scalar.minmod a (two * b))
  | .vanLeer => if ScalarSign.isPos (a * b) then two * (a * b) / (a + b) else 0
  | .vanAlbada => if ScalarSign.isPos (a * b) then a * b * (a + b) / (a * a + b * b) else 0

/-- Slope of cell `i` with limiter `L`: `limiterSlope L (u[i] - u[i-1]) (u[i+1] - u[i])`, periodic indices. -/
def limSlopeAt (L : Limiter) (u : Array α) (i : Fin u.size) : α :=
  limiterSlope L (u[i] - u[prevIdx i]) (u[nextIdx i] - u[i])

/-- Reconstructed state at the right face of cell `i`. -/
def limFacePlus (L : Limiter) (u : Array α) (i : Fin u.size) : α := u[i] + limSlopeAt L u i / two

/-- Reconstructed state at the left face of cell `i`. -/
def limFaceMinus (L : Limiter) (u : Array α) (i : Fin u.size) : α := u[i] - limSlopeAt L u i / two

/-- One Forward-Euler step of the MUSCL-Rusanov scheme with limiter `L`; entry `i` is
`u[i] + dt * (-(F(u⁺_i, u⁻_{i+1}) - F(u⁺_{i-1}, u⁻_i)) / dx)` with periodic indices. Same size as `u`. -/
def limiterEulerStepArray (L : Limiter) (dx dt : α) (u : Array α) : Array α :=
  Array.ofFn fun i : Fin u.size =>
    u[i] + dt * (-(rusanov (limFacePlus L u i) (limFaceMinus L u (nextIdx i)) -
      rusanov (limFacePlus L u (prevIdx i)) (limFaceMinus L u i)) / dx)

/-- SSPRK2 in Shu-Osher form over the limiter Euler step: `½ u + ½ E(E u)`. -/
def limiterSsprk2StepArray (L : Limiter) (dx dt : α) (u : Array α) : Array α :=
  axpby half u half (limiterEulerStepArray L dx dt (limiterEulerStepArray L dx dt u))

/-- SSPRK3 in Shu-Osher form over the limiter Euler step: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def limiterSsprk3StepArray (L : Limiter) (dx dt : α) (u : Array α) : Array α :=
  axpby third u twoThirds (limiterEulerStepArray L dx dt
    (axpby threeQuarters u quarter (limiterEulerStepArray L dx dt (limiterEulerStepArray L dx dt u))))

end CFDLean.Exec
