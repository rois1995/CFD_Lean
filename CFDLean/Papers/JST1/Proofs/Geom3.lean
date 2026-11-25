import CFDLean.Papers.JST1.Spec.Item12
import CFDLean.Papers.JST1.Proofs.GeomBase
import CFDLean.Geometry.Simplex

/-! P3-11.2 (facet vectors of a tetrahedron as cross products), P3-12.2 (flat dihedral angles of the brick
sliver) and P3-12.5 (non-obtuse Kuhn tetrahedra). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology
namespace CFDLean.JST1.Proofs

namespace Geo3

open CFDLean.JST1.Spec

theorem dot_comm' {d : ℕ} (u v : Vec d) : Num.dot u v = Num.dot v u := by
  simp only [Num.dot, mul_comm]

/-- A family with the barycentric dot table is the gradient family, and the simplex is nondegenerate. -/
theorem grads_of_dual {d : ℕ} (T : Simplex d) (G : Fin (d + 1) → Vec d)
    (hG : ∀ a j, Num.dot (G a) (T.x j - T.x 0) = (if a = j then 1 else 0) - (if a = 0 then 1 else 0)) :
    T.Nondeg ∧ ∀ a, T.grad a = G a := by
  have hN : T.Nondeg := by
    let M : Matrix (Fin d) (Fin d) ℝ := fun β α => G β.succ α
    have hM : M * T.edgeMat = 1 := by
      ext β γ
      have := hG β.succ γ.succ
      simp only [Fin.succ_inj, Fin.succ_ne_zero, ite_false, sub_zero] at this
      rw [Matrix.mul_apply, Matrix.one_apply, ← this]
      simp only [M, Num.dot, Simplex.edgeMat, Pi.sub_apply]
    have := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  refine ⟨hN, fun a => ?_⟩
  apply vec_eq_of_dots T hN
  intro j
  rw [hG a j, (p1_5_1 d T hN).2.1 a j 0]


/-! ### P3-12.5: Kuhn tetrahedra -/


/-! ### P3-11.2: facet vectors as cross products -/

theorem cross_dot_left (u v : Vec 3) : Num.dot (cross3 u v) u = 0 := by
  simp only [cross3, Num.dot, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem cross_dot_right (u v : Vec 3) : Num.dot (cross3 u v) v = 0 := by
  simp only [cross3, Num.dot, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- Expansion of a vector in the dual basis of `u, v, w` (polynomial form). -/
theorem lagrange (u v w g : Vec 3) :
    Num.dot g w • cross3 u v + Num.dot g u • cross3 v w + Num.dot g v • cross3 w u = Num.dot (cross3 u v) w • g := by
  funext i
  fin_cases i <;>
  simp only [cross3, Num.dot, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> ring

theorem det_edge3 (T : Simplex 3) :
    T.edgeMat.det = Num.dot (cross3 (T.x 1 - T.x 0) (T.x 2 - T.x 0)) (T.x 3 - T.x 0) := by
  rw [Matrix.det_fin_three]
  simp only [Simplex.edgeMat, cross3, Num.dot, Fin.sum_univ_three, Pi.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  simp
  ring

theorem triple_perm (p : Fin 4 → Vec 3) (o a b c : Fin 4) (hnd : [o, a, b, c].Nodup) :
    Num.dot (cross3 (p b - p a) (p c - p a)) (p o - p a) = Num.dot (cross3 (p 1 - p 0) (p 2 - p 0)) (p 3 - p 0) ∨
    Num.dot (cross3 (p b - p a) (p c - p a)) (p o - p a) = -Num.dot (cross3 (p 1 - p 0) (p 2 - p 0)) (p 3 - p 0) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hoa, hob, hoc⟩, ⟨hab, hac⟩, hbc⟩ := hnd
  fin_cases o <;> fin_cases a <;> (simp at hoa) <;> fin_cases b <;> (simp at hob hab) <;>
    fin_cases c <;> (simp at hoc hac hbc) <;>
  (simp only [cross3, Num.dot, Fin.sum_univ_three, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
   first | exact Or.inl trivial | (left; ring1) | (right; ring1))

theorem facet_cross (T : Simplex 3) (o a b c : Fin 4) (hT : T.Nondeg) (hnd : [o, a, b, c].Nodup) :
    T.facet o = (if 0 < Num.dot (cross3 (T.x b - T.x a) (T.x c - T.x a)) (T.x o - T.x a) then -(1 / 2 : ℝ)
      else 1 / 2) • cross3 (T.x b - T.x a) (T.x c - T.x a) := by
  have habs : |Num.dot (cross3 (T.x b - T.x a) (T.x c - T.x a)) (T.x o - T.x a)| = |T.edgeMat.det| := by
    rw [det_edge3]
    rcases triple_perm T.x o a b c hnd with h | h <;> rw [h]
    rw [abs_neg]
  have hne := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hne
  obtain ⟨⟨hoa, hob, hoc⟩, -, -⟩ := hne
  set u := T.x b - T.x a
  set v := T.x c - T.x a
  set w := T.x o - T.x a
  set D := Num.dot (cross3 u v) w with hD
  have hgrad := (p1_5_1 3 T hT).2.1
  have hu : Num.dot (T.grad o) u = 0 := by rw [hgrad]; simp [hob, hoa]
  have hv : Num.dot (T.grad o) v = 0 := by rw [hgrad]; simp [hoc, hoa]
  have hw : Num.dot (T.grad o) w = 1 := by rw [hgrad]; simp [hoa]
  have hL := lagrange u v w (T.grad o)
  rw [hw, hu, hv, zero_smul, zero_smul, add_zero, add_zero, one_smul] at hL
  have hD0 : D ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    exact hT (abs_eq_zero.mp habs.symm)
  have hg : T.grad o = D⁻¹ • cross3 u v := by rw [hL, smul_smul, inv_mul_cancel₀ hD0, one_smul]
  rw [Simplex.facet, Simplex.vol, ← habs, hg, smul_smul]
  congr 1
  norm_num [Nat.factorial]
  split_ifs with hpos
  · rw [abs_of_pos hpos]; field_simp; ring
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp hpos) hD0)]; field_simp; ring

/-! ### P3-12.2: the brick sliver -/

/-- Gradients of the sliver `sliverBrick a b h`. -/
def sliverG (a b h : ℝ) : Fin 4 → Vec 3 :=
  ![![0, 0, -1 / h], ![0, -1 / b, 1 / h], ![1 / a, 1 / b, -1 / h], ![-1 / a, 0, 1 / h]]

theorem sliver_grads (a b h : ℝ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    (sliverBrick a b h).Nondeg ∧ ∀ i, (sliverBrick a b h).grad i = sliverG a b h i := by
  apply grads_of_dual
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sliverG, sliverBrick, Num.dot, Fin.sum_univ_three] <;> field_simp <;> norm_num

theorem dot_self_nonneg {d : ℕ} (u : Vec d) : 0 ≤ Num.dot u u := Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem sqrt_prod (h : ℝ) (hh : 0 < h) (A B P : ℝ) (hA : 0 ≤ A)
    (hAB : A * B = (1 / h ^ 2) ^ 2 * P) :
    Real.sqrt A * Real.sqrt B = (1 / h ^ 2) * Real.sqrt P := by
  rw [← Real.sqrt_mul hA, hAB, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

theorem cos_form (h : ℝ) (hh : 0 < h) (D A B P : ℝ) (hA : 0 ≤ A) (hP : 0 < P) (hD : D = 1 / h ^ 2)
    (hAB : A * B = (1 / h ^ 2) ^ 2 * P) :
    -D / (Real.sqrt A * Real.sqrt B) = -1 / Real.sqrt P := by
  rw [sqrt_prod h hh A B P hA hAB, hD]
  have hs := Real.sqrt_pos.mpr hP
  generalize Real.sqrt P = s at hs ⊢
  field_simp

theorem cos13 (a b h : ℝ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    cosDih (sliverBrick a b h) 1 3 = -1 / Real.sqrt ((1 + h ^ 2 / b ^ 2) * (1 + h ^ 2 / a ^ 2)) := by
  obtain ⟨-, hg⟩ := sliver_grads a b h ha hb hh
  unfold cosDih len
  rw [hg, hg]
  have d13 : Num.dot (sliverG a b h 1) (sliverG a b h 3) = 1 / h ^ 2 := by
    simp [sliverG, Num.dot, Fin.sum_univ_three]; field_simp
  have d11 : Num.dot (sliverG a b h 1) (sliverG a b h 1) = 1 / b ^ 2 + 1 / h ^ 2 := by
    simp [sliverG, Num.dot, Fin.sum_univ_three]; field_simp
  have d33 : Num.dot (sliverG a b h 3) (sliverG a b h 3) = 1 / a ^ 2 + 1 / h ^ 2 := by
    simp [sliverG, Num.dot, Fin.sum_univ_three]; field_simp
  refine cos_form h hh _ _ _ _ (dot_self_nonneg _) (by positivity) d13 ?_
  rw [d11, d33]
  field_simp
  ring

theorem cos02 (a b h : ℝ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    cosDih (sliverBrick a b h) 0 2 = -1 / Real.sqrt (1 + h ^ 2 / a ^ 2 + h ^ 2 / b ^ 2) := by
  obtain ⟨-, hg⟩ := sliver_grads a b h ha hb hh
  unfold cosDih len
  rw [hg, hg]
  have d02 : Num.dot (sliverG a b h 0) (sliverG a b h 2) = 1 / h ^ 2 := by
    simp [sliverG, Num.dot, Fin.sum_univ_three]; field_simp
  have d00 : Num.dot (sliverG a b h 0) (sliverG a b h 0) = 1 / h ^ 2 := by
    simp [sliverG, Num.dot, Fin.sum_univ_three]; field_simp
  have d22 : Num.dot (sliverG a b h 2) (sliverG a b h 2) = 1 / a ^ 2 + 1 / b ^ 2 + 1 / h ^ 2 := by
    simp [sliverG, Num.dot, Fin.sum_univ_three]; field_simp
  refine cos_form h hh _ _ _ _ (dot_self_nonneg _) (by positivity) d02 ?_
  rw [d00, d22]
  field_simp
  ring

end Geo3

theorem p3_12_5 : Spec.P3_12_5 := CFDLean.Num.pathSimplex_nonobtuse

theorem p3_11_2 : Spec.P3_11_2 := CFDLean.Num.Simplex.facet_cross3

open Geo3 in
theorem p3_12_2 : Spec.P3_12_2 := by
  intro a b ha hb
  constructor
  · have hc : Continuous fun h : ℝ => -1 / Real.sqrt ((1 + h ^ 2 / b ^ 2) * (1 + h ^ 2 / a ^ 2)) := by
      refine Continuous.div continuous_const (by fun_prop) fun h => ?_
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
    have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, mul_one,
      Real.sqrt_one, div_one] at ht
    refine ht.congr' (eventually_nhdsWithin_of_forall fun h hh => (cos13 a b h ha hb hh).symm)
  · have hc : Continuous fun h : ℝ => -1 / Real.sqrt (1 + h ^ 2 / a ^ 2 + h ^ 2 / b ^ 2) := by
      refine Continuous.div continuous_const (by fun_prop) fun h => ?_
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
    have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, 
      Real.sqrt_one, div_one] at ht
    refine ht.congr' (eventually_nhdsWithin_of_forall fun h hh => (cos02 a b h ha hb hh).symm)

end CFDLean.JST1.Proofs
