import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field

/-! Trusted Burgers B4 statements (`specifications/Burgers-B4.md`). This file imports only Mathlib and restates every
definition it uses. `next : I ≃ I` is the periodic successor of the cells; `next.symm` is the predecessor. A two-point
flux is a function `F : ℝ → ℝ → ℝ` with the left state first. -/
noncomputable section
namespace CFDLean.Verification.BurgersB4Challenge

open scoped BigOperators

/-- Burgers physical flux `f(u) = u² / 2`. -/
def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

/-- Rusanov wave speed `a(uL, uR) = max(|uL|, |uR|)`. -/
def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

/-- Rusanov (local Lax-Friedrichs) flux for Burgers. -/
def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

/-- Entropy-conservative flux of Burgers for the square entropy. -/
def entropyConservativeFlux (a b : ℝ) : ℝ := (a ^ 2 + a * b + b ^ 2) / 6

/-- B4-B: the entropy-conservative flux is consistent and satisfies `(b - a) F(a, b) = ψ(b) - ψ(a)` with the entropy
variable `v(u) = u` and the entropy potential `ψ(u) = u³/6` of the square entropy `η(u) = u²/2`. -/
def EntropyConservativeFluxProperties : Prop :=
  (∀ u : ℝ, entropyConservativeFlux u u = burgersFlux u) ∧
  (∀ a b : ℝ, (b - a) * entropyConservativeFlux a b = b ^ 3 / 6 - a ^ 3 / 6)

/-- B4-B: the Rusanov flux is entropy stable for the square entropy: `(b - a) F(a, b) ≤ ψ(b) - ψ(a)`. -/
def RusanovEntropyStable : Prop :=
  ∀ a b : ℝ, (b - a) * rusanov a b ≤ b ^ 3 / 6 - a ^ 3 / 6

variable {I : Type*}

/-- Right-hand side of the periodic first-order finite-volume scheme with the two-point flux `F`:
`L_i = -(F(u_i, u_{i+1}) - F(u_{i-1}, u_i)) / dx`. -/
def rhs (next : I ≃ I) (dx : ℝ) (F : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  -(F (u i) (u (next i)) - F (u (next.symm i)) (u i)) / dx

/-- Numerical entropy flux of the interface between cell `i` and cell `next i` for the entropy variable `v` and the
entropy potential `ψ`: `Q_i = (v_i + v_{i+1})/2 · F(u_i, u_{i+1}) - (ψ_i + ψ_{i+1})/2`. -/
def entropyFlux (next : I ≃ I) (v ψ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  (v (u i) + v (u (next i))) / 2 * F (u i) (u (next i)) - (ψ (u i) + ψ (u (next i))) / 2

/-- B4-I: for a flux with `(v(b) - v(a)) F(a, b) ≤ ψ(b) - ψ(a)` and `dx > 0`, every cell satisfies
`v_i L_i ≤ -(Q_i - Q_{i-1}) / dx`. `Q_{i-1}` is the numerical entropy flux of the interface of cell `next.symm i`. -/
def CellEntropyInequality (I : Type*) : Prop :=
  ∀ (next : I ≃ I) (dx : ℝ) (v ψ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I),
    0 < dx → (∀ a b, (v b - v a) * F a b ≤ ψ b - ψ a) →
    v (u i) * rhs next dx F u i ≤
      -(entropyFlux next v ψ F u i - entropyFlux next v ψ F u (next.symm i)) / dx

/-- B4-G: under the same hypotheses the total entropy production is nonpositive: `Σ_i v_i L_i ≤ 0`. -/
def EntropyProductionNonpos (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (dx : ℝ) (v ψ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (u : I → ℝ),
    0 < dx → (∀ a b, (v b - v a) * F a b ≤ ψ b - ψ a) →
    ∑ i, v (u i) * rhs next dx F u i ≤ 0

/-- B4-S: the Burgers Rusanov operator does not produce energy: `Σ_i u_i L_i(u) ≤ 0` for `dx > 0`. -/
def RusanovEnergyProduction (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (dx : ℝ) (u : I → ℝ), 0 < dx → ∑ i, u i * rhs next dx rusanov u i ≤ 0

end CFDLean.Verification.BurgersB4Challenge
