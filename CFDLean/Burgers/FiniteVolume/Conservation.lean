import CFDLean.Burgers.FiniteVolume.FirstOrder
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace CFDLean.Burgers.FiniteVolume

open Core
open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem fluxDifference_sum_zero (g : PeriodicGrid I) (numFlux : NumericalFlux)
    (u : I → ℝ) :
    ∑ i, (interfaceFlux g numFlux u i - interfaceFlux g numFlux u (g.prev i)) = 0 := by
  rw [Finset.sum_sub_distrib, g.sum_prev]
  simp

theorem rhs_sum_zero (g : PeriodicGrid I) (dx : ℝ) (hdx : dx ≠ 0)
    (numFlux : NumericalFlux) (u : I → ℝ) :
    ∑ i, rhs g dx numFlux u i = 0 := by
  simp only [rhs, Finset.sum_div, Finset.sum_neg_distrib]
  rw [fluxDifference_sum_zero]
  simp [hdx]

end CFDLean.Burgers.FiniteVolume
