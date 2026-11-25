import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field

/-! Trusted Burgers B1 statements (`specifications/Burgers-B1.md`). This file imports only Mathlib and restates every
definition it uses. `next : I ≃ I` is the periodic successor of the cells; `next.symm` is the predecessor. -/
noncomputable section
namespace CFDLean.Verification.BurgersB1Challenge

open scoped BigOperators

/-- Burgers physical flux `f(u) = u² / 2`. -/
def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

/-- Rusanov wave speed `a(uL, uR) = max(|uL|, |uR|)`. -/
def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

/-- Rusanov (local Lax-Friedrichs) flux for Burgers. -/
def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

/-- B1-M: the Rusanov flux is nondecreasing in the left state and nonincreasing in the right state. -/
def RusanovMonotone : Prop :=
  (∀ a a' b : ℝ, a ≤ a' → rusanov a b ≤ rusanov a' b) ∧
  (∀ a b b' : ℝ, b ≤ b' → rusanov a b' ≤ rusanov a b)

variable {I : Type*}

/-- Total variation on the periodic grid: `Σ_i |u_{i+1} - u_i|`. -/
def totalVariation [Fintype I] (next : I ≃ I) (u : I → ℝ) : ℝ :=
  ∑ i, |u (next i) - u i|

/-- Incremental form: `v_i = u_i + C_i (u_{i+1} - u_i) - D_{i-1} (u_i - u_{i-1})`. -/
def incrementalUpdate (next : I ≃ I) (C D : I → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  u i + C i * (u (next i) - u i) - D (next.symm i) * (u i - u (next.symm i))

/-- B1-H (Harten): `C_i ≥ 0`, `D_i ≥ 0`, `C_i + D_i ≤ 1` at every interface give `TV(v) ≤ TV(u)`. -/
def HartenTotalVariation (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (C D u : I → ℝ),
    (∀ i, 0 ≤ C i) → (∀ i, 0 ≤ D i) → (∀ i, C i + D i ≤ 1) →
    totalVariation next (incrementalUpdate next C D u) ≤ totalVariation next u

/-- B1-X: `C_i ≥ 0`, `D_{i-1} ≥ 0`, `C_i + D_{i-1} ≤ 1` give `m ≤ v_i ≤ M` when `m ≤ u ≤ M`. -/
def IncrementalBounds (I : Type*) : Prop :=
  ∀ (next : I ≃ I) (C D u : I → ℝ) (m M : ℝ) (i : I),
    0 ≤ C i → 0 ≤ D (next.symm i) → C i + D (next.symm i) ≤ 1 →
    (∀ j, m ≤ u j) → (∀ j, u j ≤ M) →
    m ≤ incrementalUpdate next C D u i ∧ incrementalUpdate next C D u i ≤ M

/-- One Forward-Euler step of the periodic first-order finite-volume scheme with the Rusanov flux:
`v_i = u_i - (dt/dx) (F(u_i, u_{i+1}) - F(u_{i-1}, u_i))`. -/
def rusanovStep (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ) (i : I) : ℝ :=
  u i + dt * (-(rusanov (u i) (u (next i)) - rusanov (u (next.symm i)) (u i)) / dx)

/-- B1-S: with `dx > 0`, `dt ≥ 0` and `dt · a_i ≤ dx` at every interface the step does not increase the total
variation. -/
def RusanovTotalVariation (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ),
    0 < dx → 0 ≤ dt →
    (∀ i, dt * rusanovWaveSpeed (u i) (u (next i)) ≤ dx) →
    totalVariation next (rusanovStep next dx dt u) ≤ totalVariation next u

/-- B1-S: with `dx > 0`, `dt ≥ 0` and `2 · dt · a_i ≤ dx` at every interface the step keeps every lower and upper
bound of the old state. -/
def RusanovBounds (I : Type*) : Prop :=
  ∀ (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ) (m M : ℝ),
    0 < dx → 0 ≤ dt →
    (∀ i, 2 * (dt * rusanovWaveSpeed (u i) (u (next i))) ≤ dx) →
    (∀ j, m ≤ u j) → (∀ j, u j ≤ M) →
    ∀ i, m ≤ rusanovStep next dx dt u i ∧ rusanovStep next dx dt u i ≤ M

end CFDLean.Verification.BurgersB1Challenge
