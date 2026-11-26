import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Function.Iterate
import CFDLean.Exec.Kernel
import CFDLean.Exec.RealScalar
import CFDLean.Exec.MusclKernel
import CFDLean.Exec.LimiterKernel
import CFDLean.Exec.RealScalarSign

/-! Trusted Burgers E0c statements (`specifications/Burgers-E0c.md`). The statements are about the executable limiter
kernel `CFDLean.Exec.LimiterKernel` (which uses `CFDLean.Exec.MusclKernel` and `CFDLean.Exec.Kernel`) with the
real-number arithmetic of `CFDLean.Exec.RealScalar` and the real sign test of `CFDLean.Exec.RealScalarSign`; these
five modules are the object under verification and are imported here. Everything else comes from Mathlib and is
restated in this file: the slope function of each limiter in classical form, the MUSCL scheme on `n` periodic cells
(`Fin n`, cyclic indices `i + 1` and `i - 1`), the SSPRK3 step, and the relation between an array and a cell function.
`a` is the backward difference `u_i - u_{i-1}`, `b` the forward difference `u_{i+1} - u_i`. No mathematical
implementation module is imported. -/
noncomputable section
namespace CFDLean.Verification.BurgersE0cChallenge

open scoped BigOperators
open CFDLean.Exec

/-- E0c-L: with real arithmetic the kernel sign test is true exactly for strictly positive numbers. -/
def RealSignIsStandard : Prop :=
  ∀ x : ℝ, ScalarSign.isPos x = true ↔ 0 < x

/-- Burgers physical flux `f(u) = u² / 2`. -/
def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

/-- Rusanov wave speed `a(uL, uR) = max(|uL|, |uR|)`. -/
def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

/-- Rusanov (local Lax-Friedrichs) flux for Burgers. -/
def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

/-- Sign of `a`, used only for `a ≠ 0`. -/
def sgn (a : ℝ) : ℝ := if 0 < a then 1 else -1

/-- The slope function of each limiter, in classical form. `none` is the unlimited central slope `(a + b) / 2`. All
others are zero unless `a` and `b` have the same strict sign. -/
def slopeOf : Limiter → ℝ → ℝ → ℝ
  | .none, a, b => (a + b) / 2
  | .minmod, a, b => if 0 < a ∧ 0 < b then min a b else if a < 0 ∧ b < 0 then max a b else 0
  | .mc, a, b => if 0 < a * b then sgn a * min (|a + b| / 2) (min (2 * |a|) (2 * |b|)) else 0
  | .superbee, a, b => if 0 < a * b then sgn a * max (min (2 * |a|) |b|) (min |a| (2 * |b|)) else 0
  | .vanLeer, a, b => if 0 < a * b then 2 * (a * b) / (a + b) else 0
  | .vanAlbada, a, b => if 0 < a * b then a * b * (a + b) / (a ^ 2 + b ^ 2) else 0

/-- The bound constant `θ` of each limiter (`|slope| ≤ θ|a|`, `|slope| ≤ θ|b|`). It is not used for `none`. -/
def thetaOf : Limiter → ℝ
  | .none => 0
  | .minmod => 1
  | .mc => 2
  | .superbee => 2
  | .vanLeer => 2
  | .vanAlbada => 5 / 4

/-- E0c-L: with real arithmetic the kernel slope of each limiter is its classical slope function. -/
def KernelSlopeIsLimiter : Prop :=
  ∀ (L : Limiter) (a b : ℝ), limiterSlope L a b = slopeOf L a b

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Three-stage SSP Runge-Kutta step over a one-step map `E`: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

end Generic

/-- Slope of cell `i` for the slope function `φ`: `σ_i = φ(u_i - u_{i-1}, u_{i+1} - u_i)`, indices modulo `n`. -/
def slope {n : ℕ} [NeZero n] (φ : ℝ → ℝ → ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  φ (u i - u (i - 1)) (u (i + 1) - u i)

/-- Reconstructed state at the right face of cell `i`: `u_i + σ_i / 2`. -/
def facePlus {n : ℕ} [NeZero n] (φ : ℝ → ℝ → ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ := u i + slope φ u i / 2

/-- Reconstructed state at the left face of cell `i`: `u_i - σ_i / 2`. -/
def faceMinus {n : ℕ} [NeZero n] (φ : ℝ → ℝ → ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ := u i - slope φ u i / 2

/-- One Forward-Euler step of the MUSCL scheme with the slope function `φ` and the Rusanov flux on `n` periodic
cells: `v_i = u_i - (dt/dx) (F(u_i⁺, u_{i+1}⁻) - F(u_{i-1}⁺, u_i⁻))`. -/
def musclEulerStep {n : ℕ} [NeZero n] (φ : ℝ → ℝ → ℝ) (dx dt : ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => u i + dt *
    (-(rusanov (facePlus φ u i) (faceMinus φ u (i + 1)) - rusanov (facePlus φ u (i - 1)) (faceMinus φ u i)) / dx)

/-- The array `a` stores the cell values of `u`: it has `n` entries and entry `i` is `u i`. -/
def Represents {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) : Prop :=
  a.size = n ∧ ∀ (i : Fin n) (hi : i.val < a.size), a[i.val] = u i

/-- E0c-S: for every limiter, also `none`, the kernel Euler step computes the mathematical MUSCL Euler step. -/
def LimiterEulerStepRefines : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dx dt : ℝ) (a : Array ℝ) (u : Fin n → ℝ),
    Represents a u → Represents (limiterEulerStepArray L dx dt a) (musclEulerStep (slopeOf L) dx dt u)

/-- E0c-S: the same for the SSPRK3 kernel step. -/
def LimiterSSPRK3StepRefines : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dx dt : ℝ) (a : Array ℝ) (u : Fin n → ℝ),
    Represents a u →
    Represents (limiterSsprk3StepArray L dx dt a) (ssprk3 (musclEulerStep (slopeOf L) dx dt) u)

/-- E0c-S: `k` kernel SSPRK3 steps compute `k` mathematical SSPRK3 steps. -/
def LimiterSSPRK3RunRefines : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dx dt : ℝ) (a : Array ℝ) (u : Fin n → ℝ) (k : ℕ),
    Represents a u →
    Represents (run (limiterSsprk3StepArray L dx dt) k a) ((ssprk3 (musclEulerStep (slopeOf L) dx dt))^[k] u)

/-- Every entry of the array is between `m` and `M`. -/
def EntriesBetween (m M : ℝ) (a : Array ℝ) : Prop :=
  ∀ (i : ℕ) (hi : i < a.size), m ≤ a[i] ∧ a[i] ≤ M

/-- E0c-T: for every limiter, also `none`, with `dx ≠ 0`, `k` kernel SSPRK3 steps keep the kernel sum diagnostic (the
sum of the entries, by the E0 statement `SumDiagnostic`). -/
def LimiterSSPRK3RunSum : Prop :=
  ∀ (L : Limiter) (dx dt : ℝ) (a : Array ℝ) (k : ℕ), dx ≠ 0 →
    sumArray (run (limiterSsprk3StepArray L dx dt) k a) = sumArray a

/-- E0c-T: for every limiter except `none`, with `dx > 0`, `dt ≥ 0`, entries between `m` and `M` and
`(4 + 2θ) · dt · max(|m|, |M|) ≤ dx`, every entry is between `m` and `M` after `k` kernel SSPRK3 steps. -/
def LimiterSSPRK3RunBounds : Prop :=
  ∀ (L : Limiter) (dx dt m M : ℝ) (a : Array ℝ) (k : ℕ),
    L ≠ Limiter.none → 0 < dx → 0 ≤ dt → (4 + 2 * thetaOf L) * (dt * max |m| |M|) ≤ dx → EntriesBetween m M a →
    EntriesBetween m M (run (limiterSsprk3StepArray L dx dt) k a)

/-- E0c-T: under the hypotheses of the bounds statement the kernel total-variation diagnostic (the periodic total
variation, by the E0 statement `TotalVariationDiagnostic`) does not increase. -/
def LimiterSSPRK3RunTotalVariation : Prop :=
  ∀ (L : Limiter) (dx dt m M : ℝ) (a : Array ℝ) (k : ℕ),
    L ≠ Limiter.none → 0 < dx → 0 ≤ dt → (4 + 2 * thetaOf L) * (dt * max |m| |M|) ≤ dx → EntriesBetween m M a →
    totalVariationArray (run (limiterSsprk3StepArray L dx dt) k a) ≤ totalVariationArray a

end CFDLean.Verification.BurgersE0cChallenge
