import CFDLean.Papers.JST1.Proofs.Simplex
import CFDLean.Discrete.Mesh

/-! Proofs of `lem:dissgeom`(a)-(c): P1-5.2, P1-5.3, P1-5.4 and the Cartesian model P1-5.4b. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs

namespace DissGeom

section Vec
variable {d : ℕ}

theorem dot_sum_left {β : Type} (s : Finset β) (f : β → Vec d) (v : Vec d) :
    Num.dot (∑ j ∈ s, f j) v = ∑ j ∈ s, Num.dot (f j) v := by
  simp only [Num.dot, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem dot_ite_left (p : Prop) [Decidable p] (u v : Vec d) :
    Num.dot (if p then u else 0) v = if p then Num.dot u v else 0 := by
  split_ifs <;> simp [Num.dot]

theorem dot_smul_l (c : ℝ) (u v : Vec d) : Num.dot (c • u) v = c * Num.dot u v := by
  simp only [Num.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_smul_r (c : ℝ) (u v : Vec d) : Num.dot u (c • v) = c * Num.dot u v := by
  simp only [Num.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_sub_l (u v w : Vec d) : Num.dot (u - v) w = Num.dot u w - Num.dot v w := by
  simp only [Num.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dot_zero_r (u : Vec d) : Num.dot u 0 = 0 := by simp [Num.dot]

theorem dot_self_nonneg (u : Vec d) : 0 ≤ Num.dot u u :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem eq_zero_of_dot_self (u : Vec d) (h : Num.dot u u = 0) : u = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => mul_self_nonneg (u α))).1 h
  funext α
  exact mul_self_eq_zero.1 (this α (Finset.mem_univ _))

theorem len_nonneg (u : Vec d) : 0 ≤ len u := Real.sqrt_nonneg _

theorem len_zero : len (0 : Vec d) = 0 := by simp [len, Num.dot]

theorem len_smul' (c : ℝ) (u : Vec d) : len (c • u) = |c| * len u := by
  unfold len
  rw [dot_smul_l, dot_smul_r, ← mul_assoc, Real.sqrt_mul' _ (dot_self_nonneg u),
    Real.sqrt_mul_self_eq_abs]

theorem outer_smul_left (c : ℝ) (u v : Vec d) : outer (c • u) v = c • outer u v := by
  ext α γ; simp [outer, mul_assoc]

theorem outer_smul_right (c : ℝ) (u v : Vec d) : outer u (c • v) = c • outer u v := by
  ext α γ
  simp only [outer, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

end Vec

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

theorem gdot (hM : M.Valid) (T : C) (a b c : Fin (d + 1)) :
    Num.dot (M.g T a) (M.pos (M.vert T b) - M.pos (M.vert T c)) =
      (if a = b then 1 else 0) - (if a = c then 1 else 0) :=
  (p1_5_1 d (M.simplex T) (hM.2 T)).2.1 a b c

theorem m_pos (hM : M.Valid) (T : C) : 0 < M.m T :=
  div_pos (p1_5_1 d (M.simplex T) (hM.2 T)).2.2.2.1 (by positivity)

theorem wm_nonneg (hM : M.Valid) (T : C) : 0 ≤ M.ω T * M.m T :=
  mul_nonneg (hM.1 T) (m_pos M hM T).le

theorem e_self (i : ι) : M.e i i = 0 := sub_self _

theorem mu_nonneg (hM : M.Valid) (i k : ι) : 0 ≤ M.mu i k :=
  Finset.sum_nonneg fun T _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact wm_nonneg M hM T
    · exact le_rfl

theorem mu_symm (i k : ι) : M.mu k i = M.mu i k := by
  unfold WMesh.mu
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [and_comm]

theorem dot_c (i k : ι) (v : Vec d) :
    Num.dot (M.c i k) v = ∑ T, ∑ a, ∑ b, if M.vert T a = i ∧ M.vert T b = k then
      M.ω T * M.m T * Num.dot (M.g T b) v else 0 := by
  unfold WMesh.c WMesh.cW
  simp only [dot_sum_left, dot_ite_left, dot_smul_l]

theorem dot_c_e (hM : M.Valid) (i k : ι) (hik : i ≠ k) : Num.dot (M.c i k) (M.e i k) = M.mu i k := by
  rw [dot_c]
  unfold WMesh.mu
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · obtain ⟨ha, hb⟩ := h
    have hab : b ≠ a := fun hba => hik (by subst hba; exact ha.symm.trans hb)
    unfold WMesh.e
    rw [← ha, ← hb, gdot M hM, ite_eq_left rfl, ite_eq_right hab]
    ring
  · rfl

theorem dot_c_e' (hM : M.Valid) (i k : ι) (hik : i ≠ k) :
    Num.dot (M.c k i) (M.e i k) = -M.mu i k := by
  rw [dot_c, ← mu_symm M i k]
  unfold WMesh.mu
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · obtain ⟨ha, hb⟩ := h
    have hab : b ≠ a := fun hba => hik (by subst hba; exact hb.symm.trans ha)
    unfold WMesh.e
    rw [← ha, ← hb, gdot M hM, ite_eq_right hab, ite_eq_left rfl]
    ring
  · simp

theorem n_dot_e (hM : M.Valid) (i k : ι) (hik : i ≠ k) :
    Num.dot (M.n i k) (M.e i k) = 2 * M.mu i k := by
  unfold WMesh.n
  rw [dot_sub_l, dot_c_e M hM i k hik, dot_c_e' M hM i k hik]
  ring

end Mesh
end DissGeom

open DissGeom

theorem p1_5_2 : Spec.P1_5_2 := CFDLean.Num.WMesh.dissGeom_edge

theorem p1_5_3 : Spec.P1_5_3 := CFDLean.Num.WMesh.dissGeom_outer

theorem p1_5_4 : Spec.P1_5_4 := CFDLean.Num.WMesh.dissGeom_calibration

theorem p1_5_4b : Spec.P1_5_4b := by
  intro d V h hV hh
  dsimp only
  have dsingle : ∀ α : Fin d, Num.dot (Pi.single α (1 : ℝ) : Vec d) (Pi.single α 1) = 1 := by
    intro α; simp [Num.dot, Pi.single_apply]
  have lsingle : ∀ (α : Fin d) (c : ℝ), len (c • (Pi.single α (1 : ℝ) : Vec d)) = |c| := by
    intro α c
    rw [len_smul', len, dsingle, Real.sqrt_one, mul_one]
  refine ⟨?_, ?_⟩
  · rintro ⟨α, s⟩
    have := (hh α).ne'
    unfold WMesh.nuOf
    rw [dot_smul_l, dot_smul_r, dot_smul_l, dot_smul_r, dsingle, smul_smul]
    congr 1
    cases s <;> simp <;> field_simp
  · have hterm : ∀ (α : Fin d) (s : Bool),
        (len (((if s then (1:ℝ) else -1) * (V / h α)) • (Pi.single α (1:ℝ) : Vec d)) *
          len (((if s then (1:ℝ) else -1) * h α) • (Pi.single α (1:ℝ) : Vec d))) •
        outer (WMesh.unit (((if s then (1:ℝ) else -1) * h α) • (Pi.single α (1:ℝ) : Vec d)))
          (WMesh.unit (((if s then (1:ℝ) else -1) * h α) • (Pi.single α (1:ℝ) : Vec d))) =
        V • outer (Pi.single α (1:ℝ) : Vec d) (Pi.single α 1) := by
      intro α s
      have hα := hh α
      unfold WMesh.unit
      simp only [lsingle, smul_smul, outer_smul_left, outer_smul_right]
      congr 1
      cases s <;> simp [abs_of_pos hα, abs_of_pos (div_pos hV hα)] <;> field_simp
    rw [Fintype.sum_prod_type]
    dsimp only
    simp only [hterm, Fintype.sum_bool]
    ext β γ
    simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, outer, smul_eq_mul,
      Matrix.one_apply]
    rw [Finset.sum_eq_single β]
    · by_cases hβγ : β = γ
      · subst hβγ; simp; ring
      · simp [hβγ, Ne.symm hβγ]
    · intro x _ hx
      simp [Pi.single_apply, Ne.symm hx]
    · simp

end CFDLean.JST1.Proofs
