import CFDLean.Papers.JST1.Spec.Item2
import CFDLean.Foundations.LogMean
import CFDLean.Entropy.PairFlux

noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

theorem pairF_neg_right {κ : Type} [Fintype κ] (x z : κ → ℝ) : pairF x (-z) = -pairF x z := by
  simp only [pairF, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem p1_2_1 : Spec.P1_2_1 := CFDLean.Num.antisymmetric_pairFlux

theorem p1_2_2 : Spec.P1_2_2 := CFDLean.Num.entropyConservative_production

theorem p1_2_6 : Spec.P1_2_6 := CFDLean.Num.dissipativePairFlux_conservation

theorem p1_2_7 : Spec.P1_2_7 := CFDLean.Num.dissipativePairFlux_freeStream

theorem p1_2_4 : Spec.P1_2_4 := CFDLean.Num.logMean_properties

end CFDLean.JST1.Proofs
