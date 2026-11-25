import CFDLean.Papers.JST1.Spec.Addendum2
import CFDLean.Papers.JST1.Proofs.Item10

/-! Proofs of the P2 addendum: P2-8.0b and P2-10.8c. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

theorem p2_8_0b : Spec.P2_8_0b := by
  intro ι _ d w φ hw hφ hs
  have h : (∑ k, φ k • w k) .energy = ∑ k, φ k * w k .energy := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  have hle : ∀ k ∈ (Finset.univ : Finset ι), φ k * w k .energy ≤ 0 :=
    fun k _ => mul_nonpos_of_nonneg_of_nonpos (hφ k) (hw k).le
  by_contra hc
  push Not at hc
  have h0 : ∑ k, φ k * w k .energy = 0 := le_antisymm (Finset.sum_nonpos hle) hc
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hle).1 h0
  have : ∀ k, φ k = 0 := fun k => by
    rcases mul_eq_zero.1 (hz k (Finset.mem_univ _)) with h1 | h1
    · exact h1
    · exact absurd h1 (hw k).ne
  simp [this] at hs

theorem p2_10_8c : Spec.P2_10_8c := by
  intro ι C _ _ d g Ut Vv R t Rhat X Ck Bk Dh Sk Rrho Pst inD kD Dgal Dt PiW Bhat Pi2 Pi4 hadm hV hU w β2 Rk hR
    hP hsch hX hS hD hDt hW
  have hpE : ∀ (w R : State d) (s : ℝ), pairF w (R + s • eE) = pairF w R + s * w .energy := by
    intro w R s
    rw [e1_pairF_channel, e1_pairF_channel]
    simp only [Pi.add_apply, Pi.smul_apply, eE, smul_eq_mul, mul_zero, add_zero, mul_one]
    ring
  have hβ : ∀ i, 0 ≤ β2 i := fun i => by
    have := p1_4_3b d g (hatState (Ut i t)) (hadm i)
    simp only [β2, w]; linarith
  have hrate := (p2_10_2 d g).2.2 ι Ut Vv R t hadm (fun i => (hV i).ne') hU
  refine ⟨_, hrate, ?_⟩
  simp only [hR, hpE]
  have hwE : ∀ i, entropyVars g (hatState (Ut i t)) .energy = -β2 i := fun i => by simp only [β2, w, neg_neg]
  simp only [hwE, Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib, w] at hsch
  have key : ∀ i, (X i - Rk i) * -β2 i ≥ (if inD i = true then 0 else β2 i * Vv i * (Pst i - Sk i)) +
      (if inD i = true then β2 i * Vv i * Pst i else 0) - β2 i * Vv i * Pst i := by
    intro i
    have hVi := (hV i).le
    simp only [Rk]
    cases h : inD i
    · simp only [ite_false, Bool.false_eq_true]
      rw [hX i h]
      nlinarith [hβ i]
    · simp only [ite_true]
      nlinarith [hD i h, hβ i]
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at this
  simp only [Finset.sum_sub_distrib]
  have hW' := Finset.sum_le_sum fun T (_ : T ∈ Finset.univ) => hW T
  simp only [Finset.sum_sub_distrib] at hW'
  have hm : ∀ i, (X i - Rk i) * -β2 i = -((X i - Rk i) * β2 i) := fun i => by ring
  simp only [hm, Finset.sum_neg_distrib] at this ⊢
  linarith

end CFDLean.JST1.Proofs
