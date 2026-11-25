import CFDLean.Papers.JST1.Proofs.GeomBase

noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

theorem dot_sub_left' {d : ℕ} (u v w : Vec d) : Num.dot (u - v) w = Num.dot u w - Num.dot v w := by
  simp only [Num.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dot_smul_l {d : ℕ} (c : ℝ) (u w : Vec d) : Num.dot (c • u) w = c * Num.dot u w := by
  simp only [Num.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_neg_l {d : ℕ} (u w : Vec d) : Num.dot (-u) w = -Num.dot u w := by
  simp only [Num.dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

set_option maxHeartbeats 2000000 in
/-- The 2D median-dual segment is a signed multiple of `g_k - g_i`. -/
theorem rot_eq (T : Simplex 2) (h : T.Nondeg) (i k : Fin 3) (hik : i ≠ k) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      rot90 (T.centroid - (1 / 2 : ℝ) • (T.x i + T.x k)) =
        (σ * (T.edgeMat.det / 6)) • (T.grad k - T.grad i) := by
  obtain ⟨-, hd, -, -, -⟩ := p1_5_1 2 T h
  have key : ∀ σ : ℝ, (∀ a, Num.dot (rot90 (T.centroid - (1 / 2 : ℝ) • (T.x i + T.x k))) (T.x a - T.x 0) =
      σ * (T.edgeMat.det / 6) * Num.dot (T.grad k - T.grad i) (T.x a - T.x 0)) →
      rot90 (T.centroid - (1 / 2 : ℝ) • (T.x i + T.x k)) =
        (σ * (T.edgeMat.det / 6)) • (T.grad k - T.grad i) := by
    intro σ hσ
    apply vec_eq_of_dots T h
    intro a
    rw [hσ, dot_smul_l]
  have hdk : ∀ a, Num.dot (T.grad k - T.grad i) (T.x a - T.x 0) =
      ((if k = a then 1 else 0) - (if k = 0 then 1 else 0)) -
        ((if i = a then 1 else 0) - (if i = 0 then 1 else 0)) := by
    intro a; rw [dot_sub_left', hd, hd]
  fin_cases i <;> fin_cases k <;> simp at hik
  · exact ⟨1, Or.inl rfl, key (1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, Num.dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨-1, Or.inr rfl, key (-1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, Num.dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨-1, Or.inr rfl, key (-1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, Num.dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨1, Or.inl rfl, key (1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, Num.dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨1, Or.inl rfl, key (1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, Num.dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨-1, Or.inr rfl, key (-1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, Num.dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩

theorem dualFacet2_eq (T : Simplex 2) (h : T.Nondeg) (i k : Fin 3) (hik : i ≠ k) :
    dualFacet2 T i k = (T.vol / 3) • (T.grad k - T.grad i) := by
  obtain ⟨-, hd, -, hvol, -⟩ := p1_5_1 2 T h
  obtain ⟨σ, hσ, hr⟩ := rot_eq T h i k hik
  have hvol' : T.vol = |T.edgeMat.det| / 2 := by simp [Simplex.vol]
  have hw : Num.dot (T.grad k - T.grad i) (T.x k - T.x i) = 2 := by
    rw [dot_sub_left', hd, hd]; simp [hik, Ne.symm hik]; norm_num
  -- `σ det/6 = ± vol/3`
  have hpm : σ * (T.edgeMat.det / 6) = T.vol / 3 ∨ σ * (T.edgeMat.det / 6) = -(T.vol / 3) := by
    rw [hvol']
    rcases hσ with rfl | rfl <;> rcases abs_choice T.edgeMat.det with hab | hab <;> rw [hab] <;>
      [left; right; right; left] <;> ring
  unfold dualFacet2
  simp only
  rw [hr]
  rcases hpm with hp | hp
  · rw [hp, ite_eq_left]
    rw [dot_smul_l, hw]; positivity
  · rw [hp, ite_eq_right, neg_smul, neg_neg]
    rw [dot_smul_l, hw]; push Not
    have : 0 < T.vol := hvol
    linarith

theorem p1_5_8 : Spec.P1_5_8 := by
  intro ι C κ _ _ _ _ M Fl i hM
  unfold WMesh.galerkinRes
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : M.vert T a = i
  · have hT := hM.2 T
    have hb : ∀ b, (if M.vert T a = i ∧ b ≠ a then
        M.ω T • (Fl T).mulVec (dualFacet2 (M.simplex T) a b) else 0) =
        M.ω T • (Fl T).mulVec ((M.vol T / 3) • (M.g T b - M.g T a)) := by
      intro b
      by_cases hba : b = a
      · subst hba; simp
      · rw [ite_eq_left ⟨ha, hba⟩, dualFacet2_eq _ hT a b (Ne.symm hba)]; rfl
    simp only [hb, ite_eq_left ha]
    rw [← Finset.smul_sum]
    have hlin : ∑ b, (Fl T).mulVec ((M.vol T / 3) • (M.g T b - M.g T a)) =
        (Fl T).mulVec (∑ b, (M.vol T / 3) • (M.g T b - M.g T a)) := by
      have := map_sum (Matrix.mulVecLin (Fl T)) (fun b => (M.vol T / 3) • (M.g T b - M.g T a)) Finset.univ
      simp only [Matrix.mulVecLin_apply] at this
      exact this.symm
    have hsum : ∑ b, (M.vol T / 3) • (M.g T b - M.g T a) = (-M.vol T) • M.g T a := by
      rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [WMesh.g]
      rw [grad_sum, zero_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_neg, smul_smul, ← neg_smul]
      congr 1
      push_cast
      ring
    rw [hlin, hsum, Matrix.mulVec_smul, smul_smul, ← neg_smul]
    congr 1
    ring
  · simp [ha]

end CFDLean.JST1.Proofs
