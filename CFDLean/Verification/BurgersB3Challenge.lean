import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Function.Iterate

/-! Trusted Burgers B3 statements (`specifications/Burgers-B3.md`). This file imports only Mathlib and restates every
definition it uses. `next : I ≃ I` is the periodic successor of the cells; `next.symm` is the predecessor.
`T^[n]` is `n` applications of `T`. Sums and scalar multiples of cell functions are pointwise. -/
noncomputable section
namespace CFDLean.Verification.BurgersB3Challenge

open scoped BigOperators

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

/-- B3-L: the minmod slope has the sign of both arguments and is not larger than either. -/
def MinmodProperties : Prop :=
  ∀ a b : ℝ, 0 ≤ minmod a b * a ∧ 0 ≤ minmod a b * b ∧ |minmod a b| ≤ |a| ∧ |minmod a b| ≤ |b|

/-- B3-K: for states with absolute value at most `A` the Rusanov flux is Lipschitz with constant `2 A` in the left
state and in the right state. -/
def RusanovLipschitz : Prop :=
  ∀ A a a' b : ℝ, |a| ≤ A → |a'| ≤ A → |b| ≤ A →
    |rusanov a b - rusanov a' b| ≤ 2 * A * |a - a'| ∧
    |rusanov b a - rusanov b a'| ≤ 2 * A * |a - a'|

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Two-stage SSP Runge-Kutta step over a one-step map `E`: `½ u + ½ E(E u)`. -/
def ssprk2 (E : V → V) (u : V) : V := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • E (E u)

/-- Three-stage SSP Runge-Kutta step over a one-step map `E`: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

end Generic

variable {I : Type*}

/-- Total variation on the periodic grid: `Σ_i |u_{i+1} - u_i|`. -/
def totalVariation [Fintype I] (next : I ≃ I) (u : I → ℝ) : ℝ :=
  ∑ i, |u (next i) - u i|

/-- Limited slope of cell `i`: `σ_i = minmod(u_i - u_{i-1}, u_{i+1} - u_i)`. -/
def slope (next : I ≃ I) (u : I → ℝ) (i : I) : ℝ :=
  minmod (u i - u (next.symm i)) (u (next i) - u i)

/-- Reconstructed state at the right face of cell `i`: `u_i + σ_i / 2`. -/
def facePlus (next : I ≃ I) (u : I → ℝ) (i : I) : ℝ := u i + slope next u i / 2

/-- Reconstructed state at the left face of cell `i`: `u_i - σ_i / 2`. -/
def faceMinus (next : I ≃ I) (u : I → ℝ) (i : I) : ℝ := u i - slope next u i / 2

/-- One Forward-Euler step of the MUSCL scheme with the minmod limiter and the Rusanov flux:
`v_i = u_i - (dt/dx) (F(u_i⁺, u_{i+1}⁻) - F(u_{i-1}⁺, u_i⁻))`. -/
def musclEulerStep (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ) : I → ℝ :=
  fun i => u i + dt *
    (-(rusanov (facePlus next u i) (faceMinus next u (next i)) -
        rusanov (facePlus next u (next.symm i)) (faceMinus next u i)) / dx)

/-- A time-stepping map `T` (given the grid, `dx` and `dt`) is multi-step stable under CFL 1/6 when: for `dx > 0`,
`dt ≥ 0`, bounds `m ≤ u_j ≤ M` of the initial state and `6 · dt · max(|m|, |M|) ≤ dx`, the state after `n` steps has
the same bounds and no larger total variation, for every `n`. -/
def MultiStepStable (I : Type*) [Fintype I] (T : (I ≃ I) → ℝ → ℝ → (I → ℝ) → I → ℝ) : Prop :=
  ∀ (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ) (m M : ℝ) (n : ℕ),
    0 < dx → 0 ≤ dt → 6 * (dt * max |m| |M|) ≤ dx →
    (∀ j, m ≤ u j ∧ u j ≤ M) →
    (∀ j, m ≤ (T next dx dt)^[n] u j ∧ (T next dx dt)^[n] u j ≤ M) ∧
      totalVariation next ((T next dx dt)^[n] u) ≤ totalVariation next u

/-- B3-S: MUSCL-minmod-Rusanov with Forward Euler. -/
def MusclEulerMultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I musclEulerStep

/-- B3-S: MUSCL-minmod-Rusanov with SSPRK2. -/
def MusclSSPRK2MultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I (fun next dx dt => ssprk2 (musclEulerStep next dx dt))

/-- B3-S: MUSCL-minmod-Rusanov with SSPRK3. -/
def MusclSSPRK3MultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I (fun next dx dt => ssprk3 (musclEulerStep next dx dt))

/-- B3-S: one Forward-Euler MUSCL step keeps the total sum of the cell values when `dx ≠ 0`. -/
def MusclEulerConservation (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ), dx ≠ 0 →
    ∑ i, musclEulerStep next dx dt u i = ∑ i, u i

/-- B3-S: one SSPRK2 MUSCL step keeps the total sum of the cell values when `dx ≠ 0`. -/
def MusclSSPRK2Conservation (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ), dx ≠ 0 →
    ∑ i, ssprk2 (musclEulerStep next dx dt) u i = ∑ i, u i

/-- B3-S: one SSPRK3 MUSCL step keeps the total sum of the cell values when `dx ≠ 0`. -/
def MusclSSPRK3Conservation (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ), dx ≠ 0 →
    ∑ i, ssprk3 (musclEulerStep next dx dt) u i = ∑ i, u i

end CFDLean.Verification.BurgersB3Challenge
