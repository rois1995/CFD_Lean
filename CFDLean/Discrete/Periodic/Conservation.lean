import CFDLean.Discrete.Periodic.FiniteVolume
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace CFDLean.Scalar.FiniteVolume

open Periodic
open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem fluxDifference_sum_zero (g : Grid I) (numFlux : NumericalFlux)
    (u : I → ℝ) :
    ∑ i, (interfaceFlux g numFlux u i - interfaceFlux g numFlux u (g.prev i)) = 0 := by
  rw [Finset.sum_sub_distrib, g.sum_prev]
  simp

theorem rhs_sum_zero (g : Grid I) (dx : ℝ) (_hdx : dx ≠ 0)
    (numFlux : NumericalFlux) (u : I → ℝ) :
    ∑ i, rhs g dx numFlux u i = 0 := by
  calc
    ∑ i, rhs g dx numFlux u i =
        -(∑ i, (interfaceFlux g numFlux u i -
          interfaceFlux g numFlux u (g.prev i))) / dx := by
      simp only [rhs, ← Finset.sum_div, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [fluxDifference_sum_zero]
      simp

end CFDLean.Scalar.FiniteVolume
