import CFDLean.Num.Mesh

/-! Galerkin identity (P1-4.1), finite-volume residual = Galerkin residual (P1-5.5), and the mean flux at a closed
vertex as the Galerkin form (P2-6.7, `prop:consistency`(b)).

MC-N: proofs moved from JST_Paper_Lean `Paper1/Proofs/{MeshAlgebra,Item6}.lean`. -/
noncomputable section
open scoped BigOperators
namespace CFDLean.Num.Internal

/-- MC-N.P1-4.1 (JST `Paper1.Spec.P1_4_1`, proof `Paper1.Proofs.p1_4_1`). P1-4.1: Galerkin identity `Σ_i w_i·R_i = -Σ_T ω_T |T| G_T : F_T`, for any element fluxes. -/
theorem _root_.CFDLean.Num.WMesh.galerkin_identity :
    ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
      (w : ι → κ → ℝ) (Fl : C → Matrix κ (Fin d) ℝ),
      ∑ i, pairF (w i) (M.galerkinRes Fl i) = -∑ T, M.ω T * M.vol T * frob (M.gradW w T) (Fl T) := by
  intro ι C κ _ _ _ _ d M w Fl
  unfold WMesh.galerkinRes
  have h1 : ∀ i, pairF (w i) (-∑ T, ∑ a, if M.vert T a = i then
      (M.ω T * M.vol T) • (Fl T).mulVec (M.g T a) else 0) =
      -∑ T, ∑ a, if M.vert T a = i then
      (M.ω T * M.vol T) * pairF (w (M.vert T a)) ((Fl T).mulVec (M.g T a)) else 0 := by
    intro i
    rw [pairF_neg']
    congr 1
    rw [pairF_sum']
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [pairF_sum']
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · subst h
      rw [pairF_smul']
    · simp [pairF]
  simp only [h1, Finset.sum_neg_distrib, neg_inj]
  rw [sum_single (X := ℝ) M (fun T a => (M.ω T * M.vol T) * pairF (w (M.vert T a)) ((Fl T).mulVec (M.g T a)))]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [← Finset.mul_sum, mul_assoc]
  congr 1
  simp only [pairF_mulVec, frob, WMesh.gradW]
  refine congrArg (M.vol T * ·) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  erw [Finset.sum_apply, Finset.sum_apply]

/-- MC-N.P1-5.5 (JST `Paper1.Spec.P1_5_5`, proof `Paper1.Proofs.p1_5_5`). P1-5.5 (`prop:fv`, algebraic core): dual facet vectors `m_T (g_k - g_i)` turn the finite-volume residual of constant element fluxes into the Galerkin residual. -/
theorem _root_.CFDLean.Num.WMesh.fvRes_eq_galerkinRes :
    ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
      (S : C → ι → ι → Vec d) (Fl : C → Matrix κ (Fin d) ℝ),
      (∀ T a b, S T (M.vert T a) (M.vert T b) = M.m T • (M.g T b - M.g T a)) →
      ∀ i, M.fvRes Fl S i = M.galerkinRes Fl i := by
  intro ι C κ _ _ _ _ d M S Fl hS i
  unfold WMesh.fvRes WMesh.galerkinRes
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : M.vert T a = i
  · subst ha
    simp only [ite_true, hS]
    have hsum : ∑ b, M.m T • (M.g T b - M.g T a) = (-M.vol T) • M.g T a := by
      rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [WMesh.g]
      rw [grad_sum, zero_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_neg, smul_smul, ← neg_smul]
      congr 1
      have hd : ((d : ℝ) + 1) ≠ 0 := by positivity
      simp only [WMesh.m, WMesh.vol]
      push_cast
      field_simp
    rw [← Finset.smul_sum]
    have hlin : ∑ b, (Fl T).mulVec (M.m T • (M.g T b - M.g T a)) =
        (Fl T).mulVec (∑ b, M.m T • (M.g T b - M.g T a)) := by
      have := map_sum (Matrix.mulVecLin (Fl T)) (fun b => M.m T • (M.g T b - M.g T a)) Finset.univ
      simp only [Matrix.mulVecLin_apply] at this
      exact this.symm
    rw [hlin, hsum, Matrix.mulVec_smul, smul_smul, ← neg_smul]
    congr 1
    ring
  · simp [ha]

section
open Sbp6

/-- MC-N.P2-6.7 (JST `Paper1.Spec.P2_6_7`, proof `Paper1.Proofs.p2_6_7`). P2-6.7 (`prop:consistency`(b)): at a closed vertex the mean flux on `n_ik` is the Galerkin form `Σ_{T∋i} m_T Σ_k g_k^T · F_k = Σ_k c_ik · F_k`. -/
theorem _root_.CFDLean.Num.WMesh.closed_mean_galerkin :
    ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
      (F : ι → Matrix κ (Fin d) ℝ) (i : ι), M.Valid → M.Closed i →
      (∑ k, ((1 / 2 : ℝ) • (F i + F k)).mulVec (M.n i k)) = ∑ k, (F k).mulVec (M.c i k) ∧
      (∑ k, (F k).mulVec (M.c i k)) = ∑ T, ∑ a, if M.vert T a = i then
        (M.ω T * M.m T) • ∑ b, (F (M.vert T b)).mulVec (M.g T b) else 0 := by
  intro ι C κ _ _ _ _ d M F i _hM hi
  have hn : ∀ k, M.n i k = (2 : ℝ) • M.c i k := by
    intro k
    have hB : M.c i k + M.c k i = 0 := hi k
    unfold WMesh.n
    rw [eq_neg_of_add_eq_zero_right hB, two_smul, sub_neg_eq_add]
  refine ⟨?_, ?_⟩
  · simp only [hn, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.mulVec_smul, smul_smul]
    norm_num
    rw [Finset.sum_add_distrib, mulVec_fsum, c_row, Matrix.mulVec_zero, zero_add]
  · have step : ∀ k, (F k).mulVec (M.c i k) = ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then
        (M.ω T * M.m T) • (F (M.vert T b)).mulVec (M.g T b) else 0 := by
      intro k
      unfold WMesh.c WMesh.cW
      rw [← mulVec_fsum]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [← mulVec_fsum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← mulVec_fsum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rw [h.2, Matrix.mulVec_smul]
      · simp
    simp only [step]
    rw [sum_second M i (fun T a b => (M.ω T * M.m T) • (F (M.vert T b)).mulVec (M.g T b))]
    refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · rw [Finset.smul_sum]
    · simp

end

end CFDLean.Num.Internal
