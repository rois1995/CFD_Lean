import CFDLean.Papers.JST1.Proofs.Item11cBase

/-! Proofs of item 11, stage 3 (P3): the sides of the sub-tetrahedra of the pulling splits of affine cells
(P3-11.7) and the facet balance of the assembled weighted tetrahedral mesh (P3-11.8). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs

namespace Asm11

open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec

/-! ### P3-11.7 -/

theorem sideF_aff (k : Kind) (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3) (f : List (Fin k.n)) (v : Fin k.n) :
    sideF (affX k A b) f (kz k) (affX k A b v) = A.det * (sF k f v : ℝ) := side_aff k A b _ _ _ v

theorem sideF_cen (k : Kind) (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3) (f : List (Fin k.n)) :
    sideF (affX k A b) f (kz k) ((1 / (k.n : ℝ)) • ∑ a, affX k A b a) =
      A.det * ((1 / (k.n : ℝ)) * (cF k f : ℝ)) := side_cen k A b _ _ _

theorem sq_mul_neg (d x y : ℝ) (hd : d ≠ 0) (h : x * y < 0) : d * x * (d * y) < 0 := by
  rw [show d * x * (d * y) = (d * d) * (x * y) by ring]
  exact mul_neg_of_pos_of_neg (mul_self_pos.mpr hd) h

theorem sq_mul_pos (d x y m : ℝ) (hd : d ≠ 0) (hm : 0 < m) (h : 0 < x * y) : 0 < d * x * (d * (m * y)) := by
  rw [show d * x * (d * (m * y)) = (d * d) * m * (x * y) by ring]
  exact mul_pos (mul_pos (mul_self_pos.mpr hd) hm) h

end Asm11

open Asm11 CFDLean.JST1.Mixed CFDLean.JST1.Spec in
theorem p3_11_7 : Spec.P3_11_7 := by
  intro k A b hA X cen s hs
  have hc := checkK_all k
  simp only [checkK, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, Bool.not_eq_true'] at hc
  have h := hc s hs
  have hX : X = affX k A b := rfl
  have hcen : cen = (1 / (k.n : ℝ)) • ∑ a, affX k A b a := rfl
  refine ⟨fun t ht => ?_, fun t ht t' ht' f hf h1 h2 h3 => ?_, fun t ht f hf h1 => ?_⟩
  · have h0 := (h t ht).1
    rw [Simplex.Nondeg, Geo3.det_edge3]
    show sideOf (affX k A b (t.getD 0 (kz k))) (affX k A b (t.getD 1 (kz k))) (affX k A b (t.getD 2 (kz k)))
      (affX k A b (t.getD 3 (kz k))) ≠ 0
    rw [side_aff]
    refine mul_ne_zero hA (Int.cast_ne_zero.mpr ?_)
    simpa [sF] using h0
  · have h0 := ((h t ht).2 f hf).1 t' ht'
    simp only [h1, h2, h3, Bool.false_eq_true, false_or, or_false] at h0
    replace h0 := h0.resolve_left (by simp)
    rw [hX, sideF_aff, sideF_aff]
    exact sq_mul_neg _ _ _ hA (by exact_mod_cast h0)
  · have h0 := ((h t ht).2 f hf).2
    simp only [h1] at h0
    replace h0 := h0.resolve_left (by simp)
    rw [hcen, hX, sideF_aff, sideF_cen]
    exact sq_mul_pos _ _ _ _ hA (by have := n_ne_zero k; positivity) (by exact_mod_cast h0)

namespace Asm11

open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec

/-! ### P3-11.8: signs, shapes, faces -/

/-- Sign as a real number. -/
abbrev sg (x : ℝ) : ℝ := (SignType.sign x : ℝ)

theorem sg_mul (x y : ℝ) : sg (x * y) = sg x * sg y := by simp [sg, sign_mul]

theorem sg_int (z : ℤ) : sg (z : ℝ) = (Int.sign z : ℝ) := by
  rcases lt_trichotomy z 0 with h | rfl | h
  · have h' : (z : ℝ) < 0 := by exact_mod_cast h
    simp [sg, sign_neg h', Int.sign_eq_neg_one_of_neg h]
  · simp [sg]
  · have h' : (0 : ℝ) < z := by exact_mod_cast h
    simp [sg, sign_pos h', Int.sign_eq_one_of_pos h]

theorem sg_opp (x y : ℝ) (h : x * y < 0) : sg x + sg y = 0 := by
  rcases mul_neg_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · simp [sg, sign_pos hx, sign_neg hy]
  · simp [sg, sign_neg hx, sign_pos hy]

/-- Shapes of the reference data: sub-tetrahedra are four distinct vertices, face triangles three, and there are
splits. -/
def shape2 (k : Kind) : Bool :=
  (k.tets.all fun t => t.length == 4 && decide t.Nodup) &&
    ((quadTris k.cell).all fun f => f.length == 3 && decide f.Nodup) &&
    (k.cell.tris.all fun f => f.length == 3 && decide f.Nodup) && (k.cell.splits.length != 0)

theorem shape2_all (k : Kind) : shape2 k = true := by
  cases k <;> decide +kernel

theorem shape (k : Kind) : (∀ t ∈ k.tets, t.length = 4 ∧ t.Nodup) ∧
    (∀ f ∈ quadTris k.cell, f.length = 3 ∧ f.Nodup) ∧ (∀ f ∈ k.cell.tris, f.length = 3 ∧ f.Nodup) ∧
    k.cell.splits.length ≠ 0 := by
  have h := shape2_all k
  simp only [shape2, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem local_ok (k : Kind) (a0 a1 a2 : Fin k.n) (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h12 : a1 ≠ a2) :
    ¬(quadAny k a0 a1 a2 = true ∧ triAny k a0 a1 a2 = true) ∧
      2 * (k.tets.map (termZ k a0 a1 a2)).sum = shareZ k a0 a1 a2 * Int.sign (cenZ k a0 a1 a2) := by
  have h := localOK_all k
  simp only [localOK, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp] at h
  have h' := h a0 a1 a2
  simp only [h01, h02, h12, false_or] at h'
  refine ⟨fun ⟨hq, ht⟩ => ?_, h'.2⟩
  have := h'.1 hq
  rw [ht] at this
  exact Bool.false_ne_true this.symm

/-- A list of three local vertices containing three distinct vertices spans them as a global set. -/
theorem toFinset_eq {n : ℕ} {ι : Type} [DecidableEq ι] (g : Fin n ↪ ι) (f : List (Fin n)) (hf : f.length = 3)
    (a0 a1 a2 : Fin n) (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h12 : a1 ≠ a2) :
    (f.map g).toFinset = {g a0, g a1, g a2} ↔ (f.contains a0 && f.contains a1 && f.contains a2) = true := by
  simp only [Bool.and_eq_true, List.contains_iff_mem]
  constructor
  · intro h
    have hm : ∀ a, g a ∈ (f.map g).toFinset → a ∈ f := by
      intro a ha
      simpa using ha
    refine ⟨⟨hm _ (by rw [h]; simp), hm _ (by rw [h]; simp)⟩, hm _ (by rw [h]; simp)⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩
    have hsub : ({g a0, g a1, g a2} : Finset ι) ⊆ (f.map g).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp [h0, h1, h2]
    have hc3 : ({g a0, g a1, g a2} : Finset ι).card = 3 :=
      Finset.card_eq_three.mpr ⟨_, _, _, fun h => h01 (g.injective h), fun h => h02 (g.injective h),
        fun h => h12 (g.injective h), rfl⟩
    have hle : (f.map g).toFinset.card ≤ 3 := by
      have := List.toFinset_card_le (f.map g)
      simpa [hf] using this
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-! ### P3-11.8: the assembled mesh -/

section Mesh
variable {ι Cl : Type} [Fintype ι] [DecidableEq ι] [Fintype Cl] [DecidableEq Cl] (M : Mesh ι Cl)

theorem tet_ok (x : Σ c : Cl, Fin (M.cell c).kind.tets.length) :
    ((M.cell x.1).kind.tets.get x.2).length = 4 ∧ ((M.cell x.1).kind.tets.get x.2).Nodup :=
  (shape _).1 _ (List.get_mem _ _)

theorem vert_eq (x : Σ c : Cl, Fin (M.cell c).kind.tets.length) (a : Fin 4) :
    M.toW.vert x a = (M.cell x.1).glob (((M.cell x.1).kind.tets.get x.2).getD a (kz _)) := by
  have h := tet_ok M x
  simp only [Mesh.toW, tetEmb, dite_eq_left h]
  show (M.cell x.1).glob _ = (M.cell x.1).glob _
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [h.1]; exact a.isLt)]
  rfl

theorem valid (hA : M.Affine) : M.toW.Valid := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show 0 ≤ (M.cell x.1).kind.w
    unfold Kind.w
    positivity
  · have ht : (M.cell x.1).kind.tets.get x.2 ∈ (M.cell x.1).kind.tets := List.get_mem _ _
    obtain ⟨s, hs, hts⟩ := List.mem_flatMap.mp ht
    have hN := (p3_11_7 (M.cell x.1).kind (M.cell x.1).A (M.cell x.1).b (hA x.1).1 s hs).1 _ hts
    have e : M.toW.simplex x = realize (fun a => (M.cell x.1).A.mulVec ((M.cell x.1).kind.ref a) + (M.cell x.1).b)
        ((M.cell x.1).kind.tets.get x.2) (kz _) := by
      unfold WMesh.simplex realize
      congr 1
      funext a
      rw [vert_eq]
      exact (hA x.1).2 _
    rw [e]
    exact hN

theorem card_fn (p : (Σ c : Cl, Fin (M.cell c).kind.tets.length) × Fin 4) : (M.toW.facetNodes p).card = 3 := by
  simp [WMesh.facetNodes, Finset.card_erase_of_mem]

end Mesh

/-- 3D facet vector against any ordering of the facet's vertices. -/
theorem facetVec_any {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] (W : WMesh ι C 3) (p : C × Fin 4)
    (hT : (W.simplex p.1).Nondeg) (i0 i1 i2 : ι) (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2)
    (hS : W.facetNodes p = {i0, i1, i2}) :
    W.facetVec p = (-(1 / 2) * sg (sideOf (W.pos i0) (W.pos i1) (W.pos i2) (W.pos (W.vert p.1 p.2)))) •
      cross3 (W.pos i1 - W.pos i0) (W.pos i2 - W.pos i0) := by
  have hm : ∀ i ∈ ({i0, i1, i2} : Finset ι), ∃ a, a ≠ p.2 ∧ W.vert p.1 a = i := by
    intro i hi
    rw [← hS] at hi
    simp only [WMesh.facetNodes, Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    exact ⟨a, ha, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hm i0 (by simp)
  obtain ⟨b, hb, rfl⟩ := hm i1 (by simp)
  obtain ⟨c, hc, rfl⟩ := hm i2 (by simp)
  have hnd : [p.2, a, b, c].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true]
    refine ⟨⟨Ne.symm ha, Ne.symm hb, Ne.symm hc⟩, ⟨fun h => h01 (by rw [h]), fun h => h02 (by rw [h])⟩,
      fun h => h12 (by rw [h])⟩
  have hf := Geo3.facet_cross (W.simplex p.1) p.2 a b c hT hnd
  have htp := Geo3.triple_perm (W.simplex p.1).x p.2 a b c hnd
  have hdet := Geo3.det_edge3 (W.simplex p.1)
  have hx : ∀ e, (W.simplex p.1).x e = W.pos (W.vert p.1 e) := fun _ => rfl
  simp only [hx] at hf htp hdet
  set D := Num.dot (cross3 (W.pos (W.vert p.1 b) - W.pos (W.vert p.1 a)) (W.pos (W.vert p.1 c) - W.pos (W.vert p.1 a)))
    (W.pos (W.vert p.1 p.2) - W.pos (W.vert p.1 a)) with hD
  have hD0 : D ≠ 0 := by
    intro h0
    apply hT
    rw [hdet]
    rcases htp with h | h
    · rw [← h, h0]
    · rw [h0] at h
      linarith
  have hside : sideOf (W.pos (W.vert p.1 a)) (W.pos (W.vert p.1 b)) (W.pos (W.vert p.1 c))
      (W.pos (W.vert p.1 p.2)) = D := rfl
  rw [WMesh.facetVec, hf, hside]
  congr 1
  rcases lt_or_gt_of_ne hD0 with h | h
  · rw [ite_eq_right (not_lt.mpr h.le)]
    simp [sg, sign_neg h]
  · rw [ite_eq_left h]
    simp [sg, sign_pos h]

/-! ### One sub-tetrahedron -/

theorem match_iff {n : ℕ} {ι : Type} [DecidableEq ι] (g : Fin n ↪ ι) (t : List (Fin n)) (z : Fin n)
    (ht : t.length = 4) (hnd : t.Nodup) (e : Fin 4 ↪ ι) (he : ∀ a : Fin 4, e a = g (t.getD a z))
    (a0 a1 a2 : Fin n) (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h12 : a1 ≠ a2) (o : Fin 4) :
    (Finset.univ.erase o).map e = {g a0, g a1, g a2} ↔
      ((t.contains a0 && t.contains a1 && t.contains a2) = true ∧ inF a0 a1 a2 (t.getD o z) = false) := by
  have hget : ∀ a : Fin 4, t.getD a z = t[a.val]'(by rw [ht]; exact a.isLt) := fun a => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    rfl
  have hinj : ∀ a b : Fin 4, t.getD a z = t.getD b z → a = b := by
    intro a b h
    rw [hget, hget] at h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h)
  have hmem : ∀ v, v ∈ t ↔ ∃ a : Fin 4, t.getD a z = v := by
    intro v
    rw [List.mem_iff_getElem]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by omega⟩, by rw [hget]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, by omega, (hget a).symm⟩
  have hmap : ∀ v, g v ∈ (Finset.univ.erase o).map e ↔ ∃ a, a ≠ o ∧ t.getD a z = v := by
    intro v
    simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true, he]
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, ha, g.injective h⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  simp only [Bool.and_eq_true, List.contains_iff_mem, inF, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  constructor
  · intro h
    have hin : ∀ v, g v ∈ ({g a0, g a1, g a2} : Finset ι) → v ∈ t ∧ ¬t.getD o z = v := by
      intro v hv
      rw [← h] at hv
      obtain ⟨a, ha, rfl⟩ := (hmap v).mp hv
      exact ⟨(hmem _).mpr ⟨a, rfl⟩, fun h' => ha (hinj _ _ h').symm⟩
    have h0 := hin a0 (by simp)
    have h1 := hin a1 (by simp)
    have h2 := hin a2 (by simp)
    exact ⟨⟨⟨h0.1, h1.1⟩, h2.1⟩, ⟨h0.2, h1.2⟩, h2.2⟩
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, ⟨n0, n1⟩, n2⟩
    have key : ∀ v, v ∈ t → ¬t.getD o z = v → g v ∈ (Finset.univ.erase o).map e := by
      intro v hv hne
      obtain ⟨a, rfl⟩ := (hmem v).mp hv
      exact (hmap _).mpr ⟨a, fun h => hne (by rw [h]), rfl⟩
    have hsub : ({g a0, g a1, g a2} : Finset ι) ⊆ (Finset.univ.erase o).map e := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact key _ h0 n0
      · exact key _ h1 n1
      · exact key _ h2 n2
    have hc3 : ({g a0, g a1, g a2} : Finset ι).card = 3 :=
      Finset.card_eq_three.mpr ⟨_, _, _, fun h => h01 (g.injective h), fun h => h02 (g.injective h),
        fun h => h12 (g.injective h), rfl⟩
    have hcm : ((Finset.univ.erase o).map e).card = 3 := by simp [Finset.card_erase_of_mem]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem sum_four {n : ℕ} (t : List (Fin n)) (z : Fin n) (ht : t.length = 4) (G : Fin n → ℝ) :
    ∑ o : Fin 4, G (t.getD o z) = (t.map G).sum := by
  rcases t with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, t⟩⟩⟩⟩⟩ <;> simp at ht
  simp [Fin.sum_univ_four, add_assoc]

theorem tet_sum {n : ℕ} {ι : Type} [DecidableEq ι] (g : Fin n ↪ ι) (t : List (Fin n)) (z : Fin n)
    (ht : t.length = 4) (hnd : t.Nodup) (e : Fin 4 ↪ ι) (he : ∀ a : Fin 4, e a = g (t.getD a z))
    (a0 a1 a2 : Fin n) (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h12 : a1 ≠ a2) (F : Fin n → ℝ) :
    ∑ o : Fin 4, (if (Finset.univ.erase o).map e = {g a0, g a1, g a2} then F (t.getD o z) else 0) =
      if (t.contains a0 && t.contains a1 && t.contains a2) = true then
        (t.map fun v => if inF a0 a1 a2 v = true then 0 else F v).sum else 0 := by
  have hterm : ∀ o : Fin 4, (if (Finset.univ.erase o).map e = {g a0, g a1, g a2} then F (t.getD o z) else 0) =
      if (t.contains a0 && t.contains a1 && t.contains a2) = true then
        (fun v => if inF a0 a1 a2 v = true then 0 else F v) (t.getD o z) else 0 := by
    intro o
    dsimp only
    have hm := match_iff g t z ht hnd e he a0 a1 a2 h01 h02 h12 o
    by_cases h1 : (Finset.univ.erase o).map e = {g a0, g a1, g a2}
    · obtain ⟨hc, hi⟩ := hm.mp h1
      rw [ite_eq_left h1, ite_eq_left hc, ite_eq_right (by rw [hi]; exact Bool.false_ne_true)]
    · rw [ite_eq_right h1]
      by_cases hc : (t.contains a0 && t.contains a1 && t.contains a2) = true
      · have hi : inF a0 a1 a2 (t.getD o z) = true := by
          by_contra hi
          exact h1 (hm.mpr ⟨hc, by simpa using hi⟩)
        rw [ite_eq_left hc, ite_eq_left hi]
      · rw [ite_eq_right hc]
  rw [Finset.sum_congr rfl fun o _ => hterm o]
  split_ifs
  · exact sum_four t z ht (fun v => if inF a0 a1 a2 v = true then 0 else F v)
  · simp

theorem termZ_real (k : Kind) (a0 a1 a2 : Fin k.n) (t : List (Fin k.n)) (C : ℝ) :
    (if (t.contains a0 && t.contains a1 && t.contains a2) = true then
        (t.map fun v => if inF a0 a1 a2 v = true then 0 else
          C * (Int.sign (sideZ (refZ k a0) (refZ k a1) (refZ k a2) (refZ k v)) : ℝ)).sum else 0) =
      C * (termZ k a0 a1 a2 t : ℝ) := by
  unfold termZ
  split_ifs
  · have L : ∀ l : List (Fin k.n), (l.map fun v => if inF a0 a1 a2 v = true then 0 else
          C * (Int.sign (sideZ (refZ k a0) (refZ k a1) (refZ k a2) (refZ k v)) : ℝ)).sum =
        C * (((l.map fun v => if inF a0 a1 a2 v = true then 0 else
          Int.sign (sideZ (refZ k a0) (refZ k a1) (refZ k a2) (refZ k v))).sum : ℤ) : ℝ) := by
      intro l
      induction l with
      | nil => simp
      | cons x l ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        push_cast
        split_ifs <;> ring
    exact L t
  · simp

/-! ### Face triangles of a cell -/

section Faces
variable {ι : Type} [DecidableEq ι]

/-- Weight share of a cell at a global triangle: 1/2 on a quadrilateral face, 1 on a triangular face. -/
def share (c : Cell ι) (S : Finset ι) : ℝ :=
  if (S, true) ∈ c.faceTris then 1 / 2 else if (S, false) ∈ c.faceTris then 1 else 0

theorem mem_faceTris_true (c : Cell ι) (S : Finset ι) :
    (S, true) ∈ c.faceTris ↔ ∃ f ∈ quadTris c.kind.cell, (f.map c.glob).toFinset = S := by
  simp [Cell.faceTris, quadTris, List.mem_flatMap]
  constructor
  · rintro ⟨q, hq, ⟨f, hf, h⟩ | ⟨f, hf, h⟩⟩
    · exact ⟨f, ⟨q, hq, Or.inl hf⟩, h⟩
    · exact ⟨f, ⟨q, hq, Or.inr hf⟩, h⟩
  · rintro ⟨f, ⟨q, hq, hf | hf⟩, h⟩
    · exact ⟨q, hq, Or.inl ⟨f, hf, h⟩⟩
    · exact ⟨q, hq, Or.inr ⟨f, hf, h⟩⟩

theorem mem_faceTris_false (c : Cell ι) (S : Finset ι) :
    (S, false) ∈ c.faceTris ↔ ∃ f ∈ c.kind.cell.tris, (f.map c.glob).toFinset = S := by
  simp [Cell.faceTris, List.mem_flatMap]

theorem faceTris_range (c : Cell ι) (S : Finset ι) (fl : Bool) (h : (S, fl) ∈ c.faceTris) :
    ∀ i ∈ S, ∃ a, c.glob a = i := by
  have h' : ∃ f : List (Fin c.kind.n), (f.map c.glob).toFinset = S := by
    cases fl
    · obtain ⟨f, -, hf⟩ := (mem_faceTris_false c S).mp h
      exact ⟨f, hf⟩
    · obtain ⟨f, -, hf⟩ := (mem_faceTris_true c S).mp h
      exact ⟨f, hf⟩
  obtain ⟨f, rfl⟩ := h'
  intro i hi
  simp only [List.mem_toFinset, List.mem_map] at hi
  obtain ⟨a, -, rfl⟩ := hi
  exact ⟨a, rfl⟩

theorem faceTris_quad (c : Cell ι) (a0 a1 a2 : Fin c.kind.n) (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h12 : a1 ≠ a2) :
    (({c.glob a0, c.glob a1, c.glob a2} : Finset ι), true) ∈ c.faceTris ↔ quadAny c.kind a0 a1 a2 = true := by
  rw [mem_faceTris_true, quadAny, List.any_eq_true]
  exact exists_congr fun f => and_congr_right fun hf =>
    toFinset_eq c.glob f ((shape _).2.1 f hf).1 a0 a1 a2 h01 h02 h12

theorem faceTris_tri (c : Cell ι) (a0 a1 a2 : Fin c.kind.n) (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h12 : a1 ≠ a2) :
    (({c.glob a0, c.glob a1, c.glob a2} : Finset ι), false) ∈ c.faceTris ↔ triAny c.kind a0 a1 a2 = true := by
  rw [mem_faceTris_false, triAny, List.any_eq_true]
  exact exists_congr fun f => and_congr_right fun hf =>
    toFinset_eq c.glob f ((shape _).2.2.1 f hf).1 a0 a1 a2 h01 h02 h12

theorem share_eq (c : Cell ι) (a0 a1 a2 : Fin c.kind.n) (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h12 : a1 ≠ a2) :
    share c {c.glob a0, c.glob a1, c.glob a2} =
      (shareZ c.kind a0 a1 a2 : ℝ) / (2 * (c.kind.cell.splits.length : ℝ)) := by
  have hN : (c.kind.cell.splits.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (shape _).2.2.2
  unfold share shareZ
  simp only [faceTris_quad c a0 a1 a2 h01 h02 h12, faceTris_tri c a0 a1 a2 h01 h02 h12]
  split_ifs <;> push_cast <;> field_simp
  simp

/-- No triangle is both on a quadrilateral and on a triangular face of the same cell. -/
theorem not_both (c : Cell ι) (S : Finset ι) (ht : (S, true) ∈ c.faceTris) (hf : (S, false) ∈ c.faceTris) :
    False := by
  obtain ⟨f, hfm, rfl⟩ := (mem_faceTris_false c _).mp hf
  obtain ⟨hl, hnd⟩ := (shape _).2.2.1 f hfm
  rcases f with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, f⟩⟩⟩⟩ <;> simp at hl
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨d01, d02⟩, d12⟩ := hnd
  have e : (([f0, f1, f2].map c.glob).toFinset) = {c.glob f0, c.glob f1, c.glob f2} := by simp
  rw [e] at ht
  have hq := (faceTris_quad c f0 f1 f2 d01 d02 d12).mp ht
  have htr : triAny c.kind f0 f1 f2 = true := by
    rw [triAny, List.any_eq_true]
    exact ⟨[f0, f1, f2], hfm, by simp⟩
  exact (local_ok _ f0 f1 f2 d01 d02 d12).1 ⟨hq, htr⟩

theorem share_of_mem (c : Cell ι) (S : Finset ι) (fl : Bool) (h : (S, fl) ∈ c.faceTris) :
    share c S = if fl then 1 / 2 else 1 := by
  cases fl
  · rw [share, ite_eq_right (fun h' => not_both c S h' h), ite_eq_left h]
    rfl
  · rw [share, ite_eq_left h]
    rfl

end Faces

/-! ### Sum over the sub-tetrahedra of one cell, and over the cells -/

section Cells
variable {ι Cl : Type} [Fintype ι] [DecidableEq ι] [Fintype Cl] [DecidableEq Cl] (M : Mesh ι Cl)

theorem cell_sum (hA : M.Affine) (cl : Cl) (i0 i1 i2 : ι) (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2) :
    ∑ j : Fin (M.cell cl).kind.tets.length, ∑ o : Fin 4,
      (if M.toW.facetNodes (⟨cl, j⟩, o) = {i0, i1, i2} then
        M.toW.ω ⟨cl, j⟩ * sg (sideOf (M.pos i0) (M.pos i1) (M.pos i2) (M.pos (M.toW.vert ⟨cl, j⟩ o))) else 0) =
      share (M.cell cl) {i0, i1, i2} * sg (sideOf (M.pos i0) (M.pos i1) (M.pos i2) (M.cell cl).centroid) := by
  by_cases hr : ∃ a0 a1 a2, (M.cell cl).glob a0 = i0 ∧ (M.cell cl).glob a1 = i1 ∧ (M.cell cl).glob a2 = i2
  · obtain ⟨a0, a1, a2, rfl, rfl, rfl⟩ := hr
    have d01 : a0 ≠ a1 := fun h => h01 (by rw [h])
    have d02 : a0 ≠ a2 := fun h => h02 (by rw [h])
    have d12 : a1 ≠ a2 := fun h => h12 (by rw [h])
    have hP : ∀ a, M.pos ((M.cell cl).glob a) = affX (M.cell cl).kind (M.cell cl).A (M.cell cl).b a :=
      (hA cl).2
    have hsd : ∀ v, sg (sideOf (M.pos ((M.cell cl).glob a0)) (M.pos ((M.cell cl).glob a1))
        (M.pos ((M.cell cl).glob a2)) (M.pos ((M.cell cl).glob v))) =
        sg (M.cell cl).A.det * (Int.sign (sideZ (refZ (M.cell cl).kind a0) (refZ (M.cell cl).kind a1)
          (refZ (M.cell cl).kind a2) (refZ (M.cell cl).kind v)) : ℝ) := by
      intro v
      rw [hP, hP, hP, hP, side_aff, sg_mul, sg_int]
    have hj : ∀ j : Fin (M.cell cl).kind.tets.length, ∑ o : Fin 4,
        (if M.toW.facetNodes (⟨cl, j⟩, o) = {(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} then
          M.toW.ω ⟨cl, j⟩ * sg (sideOf (M.pos ((M.cell cl).glob a0)) (M.pos ((M.cell cl).glob a1))
            (M.pos ((M.cell cl).glob a2)) (M.pos (M.toW.vert ⟨cl, j⟩ o))) else 0) =
        ((M.cell cl).kind.w * sg (M.cell cl).A.det) *
          (termZ (M.cell cl).kind a0 a1 a2 ((M.cell cl).kind.tets.get j) : ℝ) := by
      intro j
      have hv : ∀ o, M.toW.vert ⟨cl, j⟩ o =
          (M.cell cl).glob (((M.cell cl).kind.tets.get j).getD o (kz _)) := fun o => vert_eq M ⟨cl, j⟩ o
      simp only [hv, hsd, WMesh.facetNodes]
      have hw : M.toW.ω ⟨cl, j⟩ = (M.cell cl).kind.w := rfl
      rw [hw, ← termZ_real]
      have ht := tet_ok M ⟨cl, j⟩
      rw [← tet_sum (M.cell cl).glob ((M.cell cl).kind.tets.get j) (kz _) ht.1 ht.2 (M.toW.vert ⟨cl, j⟩)
        hv a0 a1 a2 d01 d02 d12]
      refine Finset.sum_congr rfl fun o _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]
    have hsum : ∑ j : Fin (M.cell cl).kind.tets.length,
        (termZ (M.cell cl).kind a0 a1 a2 ((M.cell cl).kind.tets.get j) : ℝ) =
        (((M.cell cl).kind.tets.map (termZ (M.cell cl).kind a0 a1 a2)).sum : ℤ) := by
      simp only [List.get_eq_getElem]
      rw [Fin.sum_univ_fun_getElem (M.cell cl).kind.tets (fun t => (termZ (M.cell cl).kind a0 a1 a2 t : ℝ))]
      push_cast [Int.cast_list_sum, List.map_map]
      rfl
    have hloc := (local_ok (M.cell cl).kind a0 a1 a2 d01 d02 d12).2
    have hloc' : (2 : ℝ) * (((M.cell cl).kind.tets.map (termZ (M.cell cl).kind a0 a1 a2)).sum : ℤ) =
        (shareZ (M.cell cl).kind a0 a1 a2 : ℝ) * (Int.sign (cenZ (M.cell cl).kind a0 a1 a2) : ℝ) := by
      exact_mod_cast hloc
    have hcen : sg (sideOf (M.pos ((M.cell cl).glob a0)) (M.pos ((M.cell cl).glob a1))
        (M.pos ((M.cell cl).glob a2)) (M.cell cl).centroid) =
        sg (M.cell cl).A.det * (Int.sign (cenZ (M.cell cl).kind a0 a1 a2) : ℝ) := by
      rw [hP, hP, hP]
      have hn : (0 : ℝ) < 1 / ((M.cell cl).kind.n : ℝ) := by
        have := n_ne_zero (M.cell cl).kind
        positivity
      rw [show (M.cell cl).centroid = (1 / ((M.cell cl).kind.n : ℝ)) •
          ∑ a, affX (M.cell cl).kind (M.cell cl).A (M.cell cl).b a from rfl, side_cen, sg_mul, sg_mul,
        sg_int, show sg (1 / ((M.cell cl).kind.n : ℝ)) = 1 by simp only [sg, sign_pos hn, SignType.coe_one], one_mul]
    have hN : ((M.cell cl).kind.cell.splits.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (shape _).2.2.2
    have hT : ((((M.cell cl).kind.tets.map (termZ (M.cell cl).kind a0 a1 a2)).sum : ℤ) : ℝ) =
        (shareZ (M.cell cl).kind a0 a1 a2 : ℝ) * (Int.sign (cenZ (M.cell cl).kind a0 a1 a2) : ℝ) / 2 := by
      linarith
    rw [hsum, hcen, share_eq _ a0 a1 a2 d01 d02 d12, Kind.w, hT]
    field_simp
  · have hfn : ∀ j o, M.toW.facetNodes (⟨cl, j⟩, o) ≠ {i0, i1, i2} := by
      intro j o h
      have hin : ∀ i ∈ ({i0, i1, i2} : Finset ι), ∃ a, (M.cell cl).glob a = i := by
        intro i hi
        rw [← h] at hi
        simp only [WMesh.facetNodes, Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true] at hi
        obtain ⟨b, -, rfl⟩ := hi
        exact ⟨_, (vert_eq M ⟨cl, j⟩ b).symm⟩
      obtain ⟨a0, h0⟩ := hin i0 (by simp)
      obtain ⟨a1, h1⟩ := hin i1 (by simp)
      obtain ⟨a2, h2⟩ := hin i2 (by simp)
      exact hr ⟨a0, a1, a2, h0, h1, h2⟩
    have hno : ∀ fl, (({i0, i1, i2} : Finset ι), fl) ∉ (M.cell cl).faceTris := by
      intro fl h
      have hin := faceTris_range _ _ fl h
      obtain ⟨a0, h0⟩ := hin i0 (by simp)
      obtain ⟨a1, h1⟩ := hin i1 (by simp)
      obtain ⟨a2, h2⟩ := hin i2 (by simp)
      exact hr ⟨a0, a1, a2, h0, h1, h2⟩
    rw [share, ite_eq_right (hno true), ite_eq_right (hno false), zero_mul]
    exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun o _ => ite_eq_right (hfn j o)

theorem conform_sum (bdTris : Finset (Finset ι)) (hC : M.Conform bdTris) (i0 i1 i2 : ι)
    (hS : ({i0, i1, i2} : Finset ι) ∉ bdTris) :
    ∑ cl, share (M.cell cl) {i0, i1, i2} * sg (sideOf (M.pos i0) (M.pos i1) (M.pos i2) (M.cell cl).centroid) =
      0 := by
  by_cases h : ∃ cl fl, (({i0, i1, i2} : Finset ι), fl) ∈ (M.cell cl).faceTris
  · obtain ⟨cl, fl, hm⟩ := h
    rcases hC cl _ fl hm with ⟨hb, -⟩ | ⟨-, cl', hne, hm', huniq, hside⟩
    · exact absurd hb hS
    · rw [Fintype.sum_eq_add cl cl' hne.symm ?_]
      · rw [share_of_mem _ _ fl hm, share_of_mem _ _ fl hm', ← mul_add, sg_opp _ _ (hside i0 i1 i2 rfl),
          mul_zero]
      · rintro x ⟨hx1, hx2⟩
        have hno : ∀ fl'', (({i0, i1, i2} : Finset ι), fl'') ∉ (M.cell x).faceTris :=
          fun fl'' h'' => hx2 (huniq x hx1 fl'' h'')
        rw [share, ite_eq_right (hno true), ite_eq_right (hno false), zero_mul]
  · push Not at h
    refine Finset.sum_eq_zero fun cl _ => ?_
    rw [share, ite_eq_right (h cl true), ite_eq_right (h cl false), zero_mul]

end Cells

end Asm11

open Asm11 CFDLean.JST1.Mixed CFDLean.JST1.Spec in
theorem p3_11_8 : Spec.P3_11_8 := by
  intro ι Cl _ _ _ _ M bdTris hA hC
  refine ⟨valid M hA, fun S => ?_⟩
  by_cases hS : S ∈ bdTris
  · refine Finset.sum_eq_zero fun p _ => ite_eq_right ?_
    rintro ⟨h1, h2⟩
    simp [h2, hS] at h1
  · have e1 : ∀ p, (if decide (M.toW.facetNodes p ∈ bdTris) = false ∧ M.toW.facetNodes p = S then
        M.toW.areaVec p else 0) = if M.toW.facetNodes p = S then M.toW.areaVec p else 0 := by
      intro p
      by_cases h : M.toW.facetNodes p = S
      · rw [ite_eq_left h, ite_eq_left ⟨by simp [h, hS], h⟩]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.2)]
    rw [Finset.sum_congr rfl fun p _ => e1 p]
    by_cases h3 : S.card = 3
    · obtain ⟨i0, i1, i2, h01, h02, h12, rfl⟩ := Finset.card_eq_three.mp h3
      have e2 : ∀ p : (Σ c : Cl, Fin (M.cell c).kind.tets.length) × Fin 4,
          (if M.toW.facetNodes p = {i0, i1, i2} then M.toW.areaVec p else 0) =
          (-(1 / 2) * (if M.toW.facetNodes p = {i0, i1, i2} then M.toW.ω p.1 *
            sg (sideOf (M.pos i0) (M.pos i1) (M.pos i2) (M.pos (M.toW.vert p.1 p.2))) else 0)) •
            cross3 (M.pos i1 - M.pos i0) (M.pos i2 - M.pos i0) := by
        intro p
        split_ifs with h
        · rw [WMesh.areaVec, facetVec_any M.toW p ((valid M hA).2 p.1) i0 i1 i2 h01 h02 h12 h, smul_smul]
          congr 1
          rw [show M.toW.pos = M.pos from rfl]
          ring
        · simp
      rw [Finset.sum_congr rfl fun p _ => e2 p, ← Finset.sum_smul, ← Finset.mul_sum]
      have hz : ∑ p : (Σ c : Cl, Fin (M.cell c).kind.tets.length) × Fin 4,
          (if M.toW.facetNodes p = {i0, i1, i2} then M.toW.ω p.1 *
            sg (sideOf (M.pos i0) (M.pos i1) (M.pos i2) (M.pos (M.toW.vert p.1 p.2))) else 0) = 0 := by
        rw [Fintype.sum_prod_type, Fintype.sum_sigma]
        refine (Finset.sum_congr rfl fun cl _ => ?_).trans (conform_sum M bdTris hC i0 i1 i2 hS)
        exact cell_sum M hA cl i0 i1 i2 h01 h02 h12
      rw [hz, mul_zero, zero_smul]
    · refine Finset.sum_eq_zero fun p _ => ite_eq_right fun h => h3 ?_
      rw [← h]
      exact card_fn M p

end CFDLean.JST1.Proofs
