import CFDLean.Entropy.Scalar.Certificates
import CFDLean.Discrete.Periodic.FiniteVolume
import Mathlib.Tactic

/-! Burgers B4-Q, B4-I, B4-G: the numerical entropy flux of the periodic first-order finite-volume operator, the cell
entropy identity, and its consequences for a flux with an entropy certificate: a cell entropy inequality and a
nonpositive total entropy production. Algebraic statements; no time derivative appears. -/
noncomputable section
namespace CFDLean.Scalar.FiniteVolume

open Periodic
open scoped BigOperators

variable {I : Type*}

variable {I : Type*}

/-- B4-Q: numerical entropy flux of the interface between `i` and `g.next i` (Tadmor):
`Q = (v_i + v_{i+1})/2 · F - (ψ_i + ψ_{i+1})/2`. -/
def entropyFlux (g : Grid I) (v ψ : ℝ → ℝ) (nf : NumericalFlux) (u : I → ℝ) (i : I) : ℝ :=
  (v (u i) + v (u (g.next i))) / 2 * interfaceFlux g nf u i - (ψ (u i) + ψ (u (g.next i))) / 2

/-- B4-Q: consistency of the numerical entropy flux: on equal states it is `v f - ψ`. -/
theorem entropyFlux_constant (g : Grid I) (v ψ : ℝ → ℝ) (law : ConservationLaw) (nf : NumericalFlux)
    (hc : Consistent law nf) (c : ℝ) (i : I) :
    entropyFlux g v ψ nf (fun _ => c) i = v c * law.flux c - ψ c := by
  simp only [entropyFlux, interfaceFlux, hc c]
  ring

/-- B4-I: entropy production of a cell: `v_i L_i + (Q_i - Q_{i-1}) / dx` equals half the two interface defects over dx. -/
theorem cell_entropy_identity (g : Grid I) (dx : ℝ) (v ψ : ℝ → ℝ) (nf : NumericalFlux) (u : I → ℝ) (i : I) :
    v (u i) * rhs g dx nf u i + (entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx =
      (((v (u (g.next i)) - v (u i)) * nf.eval (u i) (u (g.next i)) - (ψ (u (g.next i)) - ψ (u i))) +
        ((v (u i) - v (u (g.prev i))) * nf.eval (u (g.prev i)) (u i) - (ψ (u i) - ψ (u (g.prev i))))) / (2 * dx) := by
  simp only [rhs, entropyFlux, interfaceFlux, g.next_prev]
  by_cases hdx : dx = 0
  · simp [hdx]
  · field_simp
    ring

/-- B4-I: cell entropy inequality (semidiscrete, algebraic form): `v_i L_i ≤ -(Q_i - Q_{i-1}) / dx`. -/
theorem cell_entropy_inequality (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (v ψ : ℝ → ℝ) (nf : NumericalFlux)
    (h : EntropyStable v ψ nf) (u : I → ℝ) (i : I) :
    v (u i) * rhs g dx nf u i ≤ -(entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx := by
  have e := cell_entropy_identity g dx v ψ nf u i
  have h1 := h (u i) (u (g.next i))
  have h2 := h (u (g.prev i)) (u i)
  have hneg : (((v (u (g.next i)) - v (u i)) * nf.eval (u i) (u (g.next i)) - (ψ (u (g.next i)) - ψ (u i))) +
      ((v (u i) - v (u (g.prev i))) * nf.eval (u (g.prev i)) (u i) - (ψ (u i) - ψ (u (g.prev i))))) / (2 * dx) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have e2 : -(entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx =
      -((entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx) := by ring
  rw [e2]
  linarith

/-- B4-I: cell entropy equality for an entropy-conservative flux. -/
theorem cell_entropy_equality (g : Grid I) (dx : ℝ) (v ψ : ℝ → ℝ) (nf : NumericalFlux)
    (h : EntropyConservative v ψ nf) (u : I → ℝ) (i : I) :
    v (u i) * rhs g dx nf u i = -(entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx := by
  have e := cell_entropy_identity g dx v ψ nf u i
  have h1 := h (u i) (u (g.next i))
  have h2 := h (u (g.prev i)) (u i)
  rw [h1, h2] at e
  have e2 : -(entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx =
      -((entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx) := by ring
  rw [e2]
  simp only [sub_self, add_zero, zero_div] at e
  linarith

/-- B4-G: the total entropy production on a periodic grid is nonpositive for an entropy-stable flux. -/
theorem entropy_production_nonpos [Fintype I] (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (v ψ : ℝ → ℝ)
    (nf : NumericalFlux) (h : EntropyStable v ψ nf) (u : I → ℝ) :
    ∑ i, v (u i) * rhs g dx nf u i ≤ 0 := by
  have hsum : ∑ i, -(entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx = 0 := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_sub_distrib, g.sum_prev]
    simp
  calc ∑ i, v (u i) * rhs g dx nf u i
      ≤ ∑ i, -(entropyFlux g v ψ nf u i - entropyFlux g v ψ nf u (g.prev i)) / dx :=
        Finset.sum_le_sum fun i _ => cell_entropy_inequality g dx hdx v ψ nf h u i
    _ = 0 := hsum

/-- B4-G: the total entropy production is zero for an entropy-conservative flux. -/
theorem entropy_production_zero [Fintype I] (g : Grid I) (dx : ℝ) (v ψ : ℝ → ℝ)
    (nf : NumericalFlux) (h : EntropyConservative v ψ nf) (u : I → ℝ) :
    ∑ i, v (u i) * rhs g dx nf u i = 0 := by
  simp only [cell_entropy_equality g dx v ψ nf h u]
  rw [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_sub_distrib, g.sum_prev]
  simp

end CFDLean.Scalar.FiniteVolume
