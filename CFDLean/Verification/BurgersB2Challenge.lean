import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Function
import Mathlib.Logic.Function.Iterate

/-! Trusted Burgers B2 statements (`specifications/Burgers-B2.md`). This file imports only Mathlib and restates every
definition it uses. `next : I ≃ I` is the periodic successor of the cells; `next.symm` is the predecessor.
`T^[n]` is `n` applications of `T`. Sums and scalar multiples of cell functions are pointwise. -/
noncomputable section
namespace CFDLean.Verification.BurgersB2Challenge

open scoped BigOperators

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Two-stage SSP Runge-Kutta step over a one-step map `E`: `½ u + ½ E(E u)`. -/
def ssprk2 (E : V → V) (u : V) : V := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • E (E u)

/-- Three-stage SSP Runge-Kutta step over a one-step map `E`: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

/-- B2-C: if `E` keeps `S` and does not increase `Φ` on `S`, and `Φ` is convex on the convex set `S`, then one
SSPRK2 step keeps `S` and does not increase `Φ`. -/
def SSPRK2Convex (V : Type*) [AddCommGroup V] [Module ℝ V] : Prop :=
  ∀ (E : V → V) (S : Set V) (Φ : V → ℝ),
    ConvexOn ℝ S Φ → (∀ u ∈ S, E u ∈ S) → (∀ u ∈ S, Φ (E u) ≤ Φ u) →
    ∀ u ∈ S, ssprk2 E u ∈ S ∧ Φ (ssprk2 E u) ≤ Φ u

/-- B2-C: the same for one SSPRK3 step. -/
def SSPRK3Convex (V : Type*) [AddCommGroup V] [Module ℝ V] : Prop :=
  ∀ (E : V → V) (S : Set V) (Φ : V → ℝ),
    ConvexOn ℝ S Φ → (∀ u ∈ S, E u ∈ S) → (∀ u ∈ S, Φ (E u) ≤ Φ u) →
    ∀ u ∈ S, ssprk3 E u ∈ S ∧ Φ (ssprk3 E u) ≤ Φ u

end Generic

/-- Burgers physical flux `f(u) = u² / 2`. -/
def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

/-- Rusanov wave speed `a(uL, uR) = max(|uL|, |uR|)`. -/
def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

/-- Rusanov (local Lax-Friedrichs) flux for Burgers. -/
def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

variable {I : Type*}

/-- Total variation on the periodic grid: `Σ_i |u_{i+1} - u_i|`. -/
def totalVariation [Fintype I] (next : I ≃ I) (u : I → ℝ) : ℝ :=
  ∑ i, |u (next i) - u i|

/-- One Forward-Euler step of the periodic first-order finite-volume scheme with the Rusanov flux:
`v_i = u_i - (dt/dx) (F(u_i, u_{i+1}) - F(u_{i-1}, u_i))`. -/
def eulerStep (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ) : I → ℝ :=
  fun i => u i + dt * (-(rusanov (u i) (u (next i)) - rusanov (u (next.symm i)) (u i)) / dx)

/-- A time-stepping map `T` (given the grid, `dx` and `dt`) is multi-step stable when: for `dx > 0`, `dt ≥ 0`, bounds
`m ≤ u_j ≤ M` of the initial state and `2 · dt · max(|m|, |M|) ≤ dx`, the state after `n` steps has the same bounds
and no larger total variation, for every `n`. -/
def MultiStepStable (I : Type*) [Fintype I] (T : (I ≃ I) → ℝ → ℝ → (I → ℝ) → I → ℝ) : Prop :=
  ∀ (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ) (m M : ℝ) (n : ℕ),
    0 < dx → 0 ≤ dt → 2 * (dt * max |m| |M|) ≤ dx →
    (∀ j, m ≤ u j ∧ u j ≤ M) →
    (∀ j, m ≤ (T next dx dt)^[n] u j ∧ (T next dx dt)^[n] u j ≤ M) ∧
      totalVariation next ((T next dx dt)^[n] u) ≤ totalVariation next u

/-- B2-S: Forward Euler. -/
def EulerMultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I eulerStep

/-- B2-S: SSPRK2 over the Forward-Euler step. -/
def SSPRK2MultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I (fun next dx dt => ssprk2 (eulerStep next dx dt))

/-- B2-S: SSPRK3 over the Forward-Euler step. -/
def SSPRK3MultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I (fun next dx dt => ssprk3 (eulerStep next dx dt))

/-- B2-S: one SSPRK2 step keeps the total sum of the cell values when `dx ≠ 0`. -/
def SSPRK2Conservation (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ), dx ≠ 0 →
    ∑ i, ssprk2 (eulerStep next dx dt) u i = ∑ i, u i

/-- B2-S: one SSPRK3 step keeps the total sum of the cell values when `dx ≠ 0`. -/
def SSPRK3Conservation (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ), dx ≠ 0 →
    ∑ i, ssprk3 (eulerStep next dx dt) u i = ∑ i, u i

end CFDLean.Verification.BurgersB2Challenge
