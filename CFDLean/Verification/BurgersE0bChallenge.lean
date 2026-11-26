import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Function.Iterate
import CFDLean.Exec.Kernel
import CFDLean.Exec.RealScalar
import CFDLean.Exec.MusclKernel

/-! Trusted Burgers E0b statements (`specifications/Burgers-E0b.md`). The statements are about the executable MUSCL
array kernel `CFDLean.Exec.MusclKernel`, which uses the E0 kernel `CFDLean.Exec.Kernel`, with the real-number
arithmetic of `CFDLean.Exec.RealScalar`; these three modules are the object under verification and are imported here.
Everything else comes from Mathlib and is restated in this file: the minmod limiter, the MUSCL scheme on `n` periodic
cells (`Fin n`, cyclic indices `i + 1` and `i - 1`), the SSPRK3 step, and the relation between an array and a cell
function. No mathematical implementation module is imported. -/
noncomputable section
namespace CFDLean.Verification.BurgersE0bChallenge

open scoped BigOperators
open CFDLean.Exec

/-- Burgers physical flux `f(u) = u² / 2`. -/
def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

/-- Rusanov wave speed `a(uL, uR) = max(|uL|, |uR|)`. -/
def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

/-- Rusanov (local Lax-Friedrichs) flux for Burgers. -/
def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

/-- The minmod limiter: the argument of smaller absolute value when both have the same strict sign, else zero. -/
def minmod (a b : ℝ) : ℝ :=
  if 0 < a ∧ 0 < b then min a b else if a < 0 ∧ b < 0 then max a b else 0

/-- E0b-L: with real arithmetic the comparison-free kernel limiter is the minmod limiter. -/
def KernelMinmodIsMinmod : Prop :=
  ∀ a b : ℝ, Scalar.minmod a b = minmod a b

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Three-stage SSP Runge-Kutta step over a one-step map `E`: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

end Generic

/-- Limited slope of cell `i`: `σ_i = minmod(u_i - u_{i-1}, u_{i+1} - u_i)`, indices modulo `n`. -/
def slope {n : ℕ} [NeZero n] (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  minmod (u i - u (i - 1)) (u (i + 1) - u i)

/-- Reconstructed state at the right face of cell `i`: `u_i + σ_i / 2`. -/
def facePlus {n : ℕ} [NeZero n] (u : Fin n → ℝ) (i : Fin n) : ℝ := u i + slope u i / 2

/-- Reconstructed state at the left face of cell `i`: `u_i - σ_i / 2`. -/
def faceMinus {n : ℕ} [NeZero n] (u : Fin n → ℝ) (i : Fin n) : ℝ := u i - slope u i / 2

/-- One Forward-Euler step of the MUSCL scheme with the minmod limiter and the Rusanov flux on `n` periodic cells:
`v_i = u_i - (dt/dx) (F(u_i⁺, u_{i+1}⁻) - F(u_{i-1}⁺, u_i⁻))`. -/
def musclEulerStep {n : ℕ} [NeZero n] (dx dt : ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => u i + dt *
    (-(rusanov (facePlus u i) (faceMinus u (i + 1)) - rusanov (facePlus u (i - 1)) (faceMinus u i)) / dx)

/-- The array `a` stores the cell values of `u`: it has `n` entries and entry `i` is `u i`. -/
def Represents {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) : Prop :=
  a.size = n ∧ ∀ (i : Fin n) (hi : i.val < a.size), a[i.val] = u i

/-- E0b-S: the kernel MUSCL Euler step computes the mathematical MUSCL Euler step. -/
def MusclEulerStepRefines : Prop :=
  ∀ (n : ℕ) [NeZero n] (dx dt : ℝ) (a : Array ℝ) (u : Fin n → ℝ),
    Represents a u → Represents (musclEulerStepArray dx dt a) (musclEulerStep dx dt u)

/-- E0b-S: the kernel MUSCL SSPRK3 step computes the mathematical MUSCL SSPRK3 step. -/
def MusclSSPRK3StepRefines : Prop :=
  ∀ (n : ℕ) [NeZero n] (dx dt : ℝ) (a : Array ℝ) (u : Fin n → ℝ),
    Represents a u → Represents (musclSsprk3StepArray dx dt a) (ssprk3 (musclEulerStep dx dt) u)

/-- E0b-S: `k` kernel MUSCL SSPRK3 steps compute `k` mathematical MUSCL SSPRK3 steps. -/
def MusclSSPRK3RunRefines : Prop :=
  ∀ (n : ℕ) [NeZero n] (dx dt : ℝ) (a : Array ℝ) (u : Fin n → ℝ) (k : ℕ),
    Represents a u →
    Represents (run (musclSsprk3StepArray dx dt) k a) ((ssprk3 (musclEulerStep dx dt))^[k] u)

/-- Every entry of the array is between `m` and `M`. -/
def EntriesBetween (m M : ℝ) (a : Array ℝ) : Prop :=
  ∀ (i : ℕ) (hi : i < a.size), m ≤ a[i] ∧ a[i] ≤ M

/-- E0b-T: with `dx > 0`, `dt ≥ 0`, entries between `m` and `M` and `6 · dt · max(|m|, |M|) ≤ dx`, every entry is
between `m` and `M` after `k` kernel MUSCL SSPRK3 steps. -/
def MusclSSPRK3RunBounds : Prop :=
  ∀ (dx dt m M : ℝ) (a : Array ℝ) (k : ℕ),
    0 < dx → 0 ≤ dt → 6 * (dt * max |m| |M|) ≤ dx → EntriesBetween m M a →
    EntriesBetween m M (run (musclSsprk3StepArray dx dt) k a)

/-- E0b-T: with `dx ≠ 0`, `k` kernel MUSCL SSPRK3 steps keep the kernel sum diagnostic (the sum of the entries, by the
E0 statement `SumDiagnostic`). -/
def MusclSSPRK3RunSum : Prop :=
  ∀ (dx dt : ℝ) (a : Array ℝ) (k : ℕ), dx ≠ 0 →
    sumArray (run (musclSsprk3StepArray dx dt) k a) = sumArray a

/-- E0b-T: under the hypotheses of the bounds statement, `k` kernel MUSCL SSPRK3 steps do not increase the kernel
total-variation diagnostic (the periodic total variation, by the E0 statement `TotalVariationDiagnostic`). -/
def MusclSSPRK3RunTotalVariation : Prop :=
  ∀ (dx dt m M : ℝ) (a : Array ℝ) (k : ℕ),
    0 < dx → 0 ≤ dt → 6 * (dt * max |m| |M|) ≤ dx → EntriesBetween m M a →
    totalVariationArray (run (musclSsprk3StepArray dx dt) k a) ≤ totalVariationArray a

end CFDLean.Verification.BurgersE0bChallenge
