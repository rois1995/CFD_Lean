import CFDLean.Exec.Kernel

/-! Burgers E0b-K, the MUSCL kernel: an executable array implementation of the second-order periodic MUSCL scheme with
the minmod limiter and the Rusanov flux for the 1D Burgers equation, with Forward Euler and SSPRK2/SSPRK3 in Shu-Osher
form. Generic over the arithmetic `α` of `CFDLean.Exec.Kernel`; no Mathlib. The minmod limiter is written without a
comparison, with `max`, negation, zero and addition only, so that `Scalar` needs no order relation. -/
namespace CFDLean.Exec

namespace Scalar

variable {α : Type} [Scalar α]

/-- `min` from `max`: `min a b = -max (-a) (-b)`. -/
def min (a b : α) : α := -Scalar.max (-a) (-b)

/-- The minmod limiter without a comparison: `max 0 (min a b) + min 0 (max a b)`. -/
def minmod (a b : α) : α := Scalar.max 0 (Scalar.min a b) + Scalar.min 0 (Scalar.max a b)

end Scalar

open Scalar

variable {α : Type} [Scalar α]

/-- Periodic successor index `(i + 1) % n`. -/
def nextIdx {n : Nat} (i : Fin n) : Fin n := ⟨(i.val + 1) % n, succ_mod_lt i⟩

/-- Periodic predecessor index `(i + n - 1) % n`. -/
def prevIdx {n : Nat} (i : Fin n) : Fin n := ⟨(i.val + n - 1) % n, pred_mod_lt i⟩

/-- Limited slope of cell `i`: `minmod(u[i] - u[i-1], u[i+1] - u[i])` with periodic indices. -/
def slopeAt (u : Array α) (i : Fin u.size) : α := minmod (u[i] - u[prevIdx i]) (u[nextIdx i] - u[i])

/-- Reconstructed state at the right face of cell `i`. -/
def facePlus (u : Array α) (i : Fin u.size) : α := u[i] + slopeAt u i / two

/-- Reconstructed state at the left face of cell `i`. -/
def faceMinus (u : Array α) (i : Fin u.size) : α := u[i] - slopeAt u i / two

/-- One Forward-Euler step of the MUSCL-minmod-Rusanov scheme; entry `i` is
`u[i] + dt * (-(F(u⁺_i, u⁻_{i+1}) - F(u⁺_{i-1}, u⁻_i)) / dx)` with periodic indices. Same size as `u`. -/
def musclEulerStepArray (dx dt : α) (u : Array α) : Array α :=
  Array.ofFn fun i : Fin u.size =>
    u[i] + dt * (-(rusanov (facePlus u i) (faceMinus u (nextIdx i)) -
      rusanov (facePlus u (prevIdx i)) (faceMinus u i)) / dx)

/-- SSPRK2 in Shu-Osher form over the MUSCL Euler step: `½ u + ½ E(E u)`. -/
def musclSsprk2StepArray (dx dt : α) (u : Array α) : Array α :=
  axpby half u half (musclEulerStepArray dx dt (musclEulerStepArray dx dt u))

/-- SSPRK3 in Shu-Osher form over the MUSCL Euler step: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def musclSsprk3StepArray (dx dt : α) (u : Array α) : Array α :=
  axpby third u twoThirds (musclEulerStepArray dx dt
    (axpby threeQuarters u quarter (musclEulerStepArray dx dt (musclEulerStepArray dx dt u))))

end CFDLean.Exec
