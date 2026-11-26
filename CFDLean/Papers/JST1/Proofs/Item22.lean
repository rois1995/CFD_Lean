import CFDLean.Papers.JST1.Spec.Item22
import CFDLean.Papers.JST1.Proofs.Item11c

/-! Proofs of item 22 (P7): `lem:avg` for cells with free vertex positions, and the twisted-cube counterexample (G8).
The side of a vertex against a face of a sub-tetrahedron is its determinant up to a sign that depends only on the
vertex order (`perm_sign`); so `σ · det_X · det_ref > 0` carries every reference side sign to the cell
(`side_transfer`), and the closed reference computations of P3-11.7/11.8 apply. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Gen22

open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec Asm11

/-- The 4-point determinant `(p₁ - p₀) × (p₂ - p₀) · (p₃ - p₀)`. -/
def D4 (p : Fin 4 → Vec 3) : ℝ := sideOf (p 0) (p 1) (p 2) (p 3)

set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
theorem perm_sign (a b c o : Fin 4) (hnd : [a, b, c, o].Nodup) :
    (∀ p : Fin 4 → Vec 3, sideOf (p a) (p b) (p c) (p o) = D4 p) ∨
      (∀ p : Fin 4 → Vec 3, sideOf (p a) (p b) (p c) (p o) = -D4 p) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hab, hac, hao⟩, ⟨hbc, hbo⟩, hco⟩ := hnd
  fin_cases a <;> fin_cases b <;> (simp at hab) <;> fin_cases c <;> (simp at hac hbc) <;>
    fin_cases o <;> (simp at hao hbo hco) <;>
  first
    | (left; intro p; simp only [D4, sideOf, cross, Num.dot, Fin.sum_univ_three, Pi.sub_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring1)
    | (right; intro p; simp only [D4, sideOf, cross, Num.dot, Fin.sum_univ_three, Pi.sub_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring1)

theorem tetDet_D4 {n : ℕ} (X : Fin n → Vec 3) (t : List (Fin n)) (z : Fin n) :
    tetDet X t z = D4 (fun i => X (t.getD i.val z)) := by
  rw [tetDet, Geo3.det_edge3]
  rfl

theorem mem_idx {n : ℕ} (t : List (Fin n)) (z : Fin n) (ht : t.length = 4) {a : Fin n} (ha : a ∈ t) :
    ∃ i : Fin 4, t.getD i.val z = a := by
  obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.mp ha
  refine ⟨⟨i, by omega⟩, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact h

/-- Transfer of sides between two position families: the product of the sides of `v` against `a0 a1 a2` is the
product of the determinants of the sub-tetrahedron with these four vertices. -/
theorem side_transfer {n : ℕ} (X Y : Fin n → Vec 3) (t : List (Fin n)) (z : Fin n) (ht : t.length = 4)
    (a0 a1 a2 v : Fin n) (hnd : [a0, a1, a2, v].Nodup) (h0 : a0 ∈ t) (h1 : a1 ∈ t) (h2 : a2 ∈ t) (hv : v ∈ t) :
    sideOf (X a0) (X a1) (X a2) (X v) * sideOf (Y a0) (Y a1) (Y a2) (Y v) = tetDet X t z * tetDet Y t z := by
  obtain ⟨i0, e0⟩ := mem_idx t z ht h0
  obtain ⟨i1, e1⟩ := mem_idx t z ht h1
  obtain ⟨i2, e2⟩ := mem_idx t z ht h2
  obtain ⟨iv, ev⟩ := mem_idx t z ht hv
  have hnd' : [i0, i1, i2, iv].Nodup := by
    have hm : [i0, i1, i2, iv].map (fun i : Fin 4 => t.getD i.val z) = [a0, a1, a2, v] := by
      simp only [List.map_cons, List.map_nil, e0, e1, e2, ev]
    exact List.Nodup.of_map (fun i : Fin 4 => t.getD i.val z) (hm ▸ hnd)
  rw [tetDet_D4, tetDet_D4, ← e0, ← e1, ← e2, ← ev]
  rcases perm_sign i0 i1 i2 iv hnd' with h | h
  · rw [h (fun i => X (t.getD i.val z)), h (fun i => Y (t.getD i.val z))]
  · rw [h (fun i => X (t.getD i.val z)), h (fun i => Y (t.getD i.val z))]; ring

theorem sideOf_ref (k : Kind) (a0 a1 a2 v : Fin k.n) :
    sideOf (k.ref a0) (k.ref a1) (k.ref a2) (k.ref v) =
      (sideZ (refZ k a0) (refZ k a1) (refZ k a2) (refZ k v) : ℝ) := by
  rw [ref_eq, ref_eq, ref_eq, ref_eq, sideOf_cast]

/-- From `σ x a > 0`, `σ y b > 0` with `σ² = 1`: the sign of `x y` is the sign of `a b`. -/
theorem sign_pair {σ x y a b : ℝ} (hσ : σ = 1 ∨ σ = -1) (hx : 0 < σ * x * a) (hy : 0 < σ * y * b) :
    (a * b < 0 → x * y < 0) ∧ (0 < a * b → 0 < x * y) := by
  have hp : 0 < (x * y) * (a * b) := by
    have := mul_pos hx hy
    rcases hσ with rfl | rfl <;> nlinarith
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hc; push Not at hc; nlinarith
  · by_contra hc; push Not at hc; nlinarith

/-! ### Closed checks on the reference cells -/

section Check
variable (k : Kind)

/-- Faces of the distinct sub-tetrahedra: three distinct vertices plus the opposite one, all in the tetrahedron;
the same for every other sub-tetrahedron with that face; cell-face triangles are face triangles of the cell. -/
def chkF : Bool :=
  k.tets.dedup.all fun t => (tetFaces t).all fun f =>
    let q := [f.getD 0 (kz k), f.getD 1 (kz k), f.getD 2 (kz k)]
    (decide (q ++ [oppV t f (kz k)]).Nodup && (q ++ [oppV t f (kz k)]).all t.contains) &&
    (!onCellFace k.cell f || quadAny k (q.getD 0 (kz k)) (q.getD 1 (kz k)) (q.getD 2 (kz k)) ||
      triAny k (q.getD 0 (kz k)) (q.getD 1 (kz k)) (q.getD 2 (kz k))) &&
    (k.tets.dedup.all fun t' => !((tetFaces t').any (sameSimplex f)) ||
      (decide (q ++ [oppV t' f (kz k)]).Nodup && (q ++ [oppV t' f (kz k)]).all t'.contains))

/-- At a face triangle of the cell, the fourth vertex of every sub-tetrahedron containing it is on the side of the
reference centroid (which is off the triangle's plane). -/
def chkR : Bool :=
  (List.finRange k.n).all fun a0 => (List.finRange k.n).all fun a1 => (List.finRange k.n).all fun a2 =>
    a0 == a1 || a0 == a2 || a1 == a2 || !(quadAny k a0 a1 a2 || triAny k a0 a1 a2) ||
      (cenZ k a0 a1 a2 != 0 &&
        k.tets.dedup.all fun t => !(t.contains a0 && t.contains a1 && t.contains a2) ||
          t.all fun v => inF a0 a1 a2 v ||
            Int.sign (sideZ (refZ k a0) (refZ k a1) (refZ k a2) (refZ k v)) == Int.sign (cenZ k a0 a1 a2))

end Check

/-! The same checks with the cell data as plain arguments (`docs/LEAN_PERFORMANCE.md`, rule 2). -/

section Generic
variable {n : ℕ} (C : Cell3 n) (R : Fin n → Z3) (S : Z3) (z : Fin n)

def chkFg : Bool :=
  (tetsOf C).dedup.all fun t => (tetFaces t).all fun f =>
    let q := [f.getD 0 z, f.getD 1 z, f.getD 2 z]
    (decide (q ++ [oppV t f z]).Nodup && (q ++ [oppV t f z]).all t.contains) &&
    (!onCellFace C f || quadAnyg C (q.getD 0 z) (q.getD 1 z) (q.getD 2 z) ||
      triAnyg C (q.getD 0 z) (q.getD 1 z) (q.getD 2 z)) &&
    ((tetsOf C).dedup.all fun t' => !((tetFaces t').any (sameSimplex f)) ||
      (decide (q ++ [oppV t' f z]).Nodup && (q ++ [oppV t' f z]).all t'.contains))

def chkRg : Bool :=
  (List.finRange n).all fun a0 => (List.finRange n).all fun a1 => (List.finRange n).all fun a2 =>
    a0 == a1 || a0 == a2 || a1 == a2 || !(quadAnyg C a0 a1 a2 || triAnyg C a0 a1 a2) ||
      (cenZg R S a0 a1 a2 != 0 &&
        (tetsOf C).dedup.all fun t => !(t.contains a0 && t.contains a1 && t.contains a2) ||
          t.all fun v => inF a0 a1 a2 v ||
            Int.sign (sideZ (R a0) (R a1) (R a2) (R v)) == Int.sign (cenZg R S a0 a1 a2))

end Generic

set_option maxHeartbeats 4000000 in
theorem chkF_all (k : Kind) : chkF k = true := by
  cases k
  · rw [show chkF .hex = chkFg RefCell.hex 0 from rfl]; decide +kernel
  · rw [show chkF .prism = chkFg RefCell.prism 0 from rfl]; decide +kernel
  · rw [show chkF .pyr = chkFg RefCell.pyramid 0 from rfl]; decide +kernel
set_option maxHeartbeats 4000000 in
theorem chkR_all (k : Kind) : chkR k = true := by
  cases k
  · rw [show chkR .hex = chkRg RefCell.hex hexR (4, 4, 4) from rfl]; decide +kernel
  · rw [show chkR .prism = chkRg RefCell.prism prismR (2, 2, 3) from rfl]; decide +kernel
  · rw [show chkR .pyr = chkRg RefCell.pyramid pyrR (5, 5, 2) from rfl]; decide +kernel

theorem face_facts (k : Kind) {t : List (Fin k.n)} (ht : t ∈ k.tets) {f : List (Fin k.n)} (hf : f ∈ tetFaces t) :
    ([f.getD 0 (kz k), f.getD 1 (kz k), f.getD 2 (kz k), oppV t f (kz k)].Nodup ∧
      f.getD 0 (kz k) ∈ t ∧ f.getD 1 (kz k) ∈ t ∧ f.getD 2 (kz k) ∈ t ∧ oppV t f (kz k) ∈ t) ∧
    (onCellFace k.cell f = true →
      (quadAny k (f.getD 0 (kz k)) (f.getD 1 (kz k)) (f.getD 2 (kz k)) ||
        triAny k (f.getD 0 (kz k)) (f.getD 1 (kz k)) (f.getD 2 (kz k))) = true) ∧
    ∀ t' ∈ k.tets, (tetFaces t').any (sameSimplex f) = true →
      [f.getD 0 (kz k), f.getD 1 (kz k), f.getD 2 (kz k), oppV t' f (kz k)].Nodup ∧
      f.getD 0 (kz k) ∈ t' ∧ f.getD 1 (kz k) ∈ t' ∧ f.getD 2 (kz k) ∈ t' ∧ oppV t' f (kz k) ∈ t' := by
  have h := chkF_all k
  simp only [chkF, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.mem_dedup, List.getD_cons_zero, List.getD_cons_succ, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨hn, hm⟩, hc⟩, ht'⟩ := h t ht f hf
  refine ⟨⟨hn, hm⟩, fun hcf => ?_, fun t' h1 h2 => ?_⟩
  · rcases hc with (hc | hc) | hc
    · rw [hcf] at hc; exact absurd hc (by simp)
    · rw [Bool.or_eq_true]; exact Or.inl hc
    · rw [Bool.or_eq_true]; exact Or.inr hc
  · rcases ht' t' h1 with h3 | h3
    · rw [h2] at h3; exact absurd h3 (by simp)
    · exact h3

/-- The sign transfer at a face of a sub-tetrahedron of a split-oriented cell. -/
theorem side_pos (k : Kind) (X : Fin k.n → Vec 3) {σ : ℝ}
    (hO : ∀ t ∈ k.tets, 0 < σ * tetDet X t (kz k) * tetDet k.ref t (kz k))
    {t : List (Fin k.n)} (ht : t ∈ k.tets) (a0 a1 a2 v : Fin k.n) (hnd : [a0, a1, a2, v].Nodup)
    (h0 : a0 ∈ t) (h1 : a1 ∈ t) (h2 : a2 ∈ t) (hv : v ∈ t) :
    0 < σ * sideOf (X a0) (X a1) (X a2) (X v) *
      (sideZ (refZ k a0) (refZ k a1) (refZ k a2) (refZ k v) : ℝ) := by
  have e := side_transfer X k.ref t (kz k) ((shape k).1 t ht).1 a0 a1 a2 v hnd h0 h1 h2 hv
  rw [sideOf_ref] at e
  rw [mul_assoc, e, ← mul_assoc]
  exact hO t ht

theorem ref_side (k : Kind) (a0 a1 a2 : Fin k.n) (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h12 : a1 ≠ a2)
    (hq : (quadAny k a0 a1 a2 || triAny k a0 a1 a2) = true) :
    cenZ k a0 a1 a2 ≠ 0 ∧ ∀ t ∈ k.tets, a0 ∈ t → a1 ∈ t → a2 ∈ t → ∀ v ∈ t, v ≠ a0 → v ≠ a1 → v ≠ a2 →
      Int.sign (sideZ (refZ k a0) (refZ k a1) (refZ k a2) (refZ k v)) = Int.sign (cenZ k a0 a1 a2) := by
  have h := chkR_all k
  simp only [chkR, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.mem_dedup] at h
  have h' := h a0 a1 a2
  simp only [h01, h02, h12, false_or] at h'
  rcases h' with h' | ⟨hc, h'⟩
  · rw [hq] at h'; exact absurd h' (by simp)
  refine ⟨hc, fun t ht m0 m1 m2 v hv n0 n1 n2 => ?_⟩
  rcases h' t ht with h'' | h''
  · simp [m0, m1, m2] at h''
  · rcases h'' v hv with h3 | h3
    · simp [inF, n0, n1, n2] at h3
    · exact h3

theorem sg_of_pos {σ x : ℝ} {z : ℤ} (hσ : σ = 1 ∨ σ = -1) (h : 0 < σ * x * (z : ℝ)) :
    sg x = σ * (Int.sign z : ℝ) := by
  rw [← sg_int]
  rcases hσ with rfl | rfl
  · rw [one_mul] at h ⊢
    rcases mul_pos_iff.mp h with ⟨hx, hz⟩ | ⟨hx, hz⟩
    · simp [sg, sign_pos hx, sign_pos hz]
    · simp [sg, sign_neg hx, sign_neg hz]
  · have h' : 0 < x * (-(z : ℝ)) := by linarith
    rcases mul_pos_iff.mp h' with ⟨hx, hz⟩ | ⟨hx, hz⟩
    · have : (z : ℝ) < 0 := by linarith
      simp [sg, sign_pos hx, sign_neg this]
    · have : 0 < (z : ℝ) := by linarith
      simp [sg, sign_neg hx, sign_pos this]

section MeshG
variable {ι Cl : Type} [Fintype ι] [DecidableEq ι] [Fintype Cl] [DecidableEq Cl] (M : Mesh ι Cl)

theorem simplex_eq (x : Σ c : Cl, Fin (M.cell c).kind.tets.length) :
    M.toW.simplex x = realize (cellPos M x.1) ((M.cell x.1).kind.tets.get x.2) (kz _) := by
  unfold WMesh.simplex realize
  congr 1
  funext a
  rw [vert_eq]
  rfl

theorem valid' (hS : MeshSplitOriented M) : M.toW.Valid := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show 0 ≤ (M.cell x.1).kind.w
    unfold Kind.w
    positivity
  · obtain ⟨σ, -, hO⟩ := hS x.1
    have := hO _ (List.get_mem _ x.2)
    rw [simplex_eq]
    intro h0
    rw [show tetDet (cellPos M x.1) ((M.cell x.1).kind.tets.get x.2) (kz _) =
      (realize (cellPos M x.1) ((M.cell x.1).kind.tets.get x.2) (kz _)).edgeMat.det from rfl, h0] at this
    simp at this

theorem cell_sum' (cl : Cl) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hO : ∀ t ∈ (M.cell cl).kind.tets,
      0 < σ * tetDet (cellPos M cl) t (kz _) * tetDet (M.cell cl).kind.ref t (kz _))
    (a0 a1 a2 : Fin (M.cell cl).kind.n) (d01 : a0 ≠ a1) (d02 : a0 ≠ a2) (d12 : a1 ≠ a2) :
    ∑ j : Fin (M.cell cl).kind.tets.length, ∑ o : Fin 4,
      (if M.toW.facetNodes (⟨cl, j⟩, o) = {(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} then
        M.toW.ω ⟨cl, j⟩ * sg (sideOf (M.pos ((M.cell cl).glob a0)) (M.pos ((M.cell cl).glob a1))
          (M.pos ((M.cell cl).glob a2)) (M.pos (M.toW.vert ⟨cl, j⟩ o))) else 0) =
      share (M.cell cl) {(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} *
        (σ * (Int.sign (cenZ (M.cell cl).kind a0 a1 a2) : ℝ)) := by
  have hj : ∀ j : Fin (M.cell cl).kind.tets.length, ∑ o : Fin 4,
      (if M.toW.facetNodes (⟨cl, j⟩, o) = {(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} then
        M.toW.ω ⟨cl, j⟩ * sg (sideOf (M.pos ((M.cell cl).glob a0)) (M.pos ((M.cell cl).glob a1))
          (M.pos ((M.cell cl).glob a2)) (M.pos (M.toW.vert ⟨cl, j⟩ o))) else 0) =
      ((M.cell cl).kind.w * σ) * (termZ (M.cell cl).kind a0 a1 a2 ((M.cell cl).kind.tets.get j) : ℝ) := by
    intro j
    have hv : ∀ o, M.toW.vert ⟨cl, j⟩ o =
        (M.cell cl).glob (((M.cell cl).kind.tets.get j).getD o (kz _)) := fun o => vert_eq M ⟨cl, j⟩ o
    simp only [hv, WMesh.facetNodes]
    have hw : M.toW.ω ⟨cl, j⟩ = (M.cell cl).kind.w := rfl
    rw [hw]
    have ht := tet_ok M ⟨cl, j⟩
    have e := tet_sum (M.cell cl).glob ((M.cell cl).kind.tets.get j) (kz _) ht.1 ht.2 (M.toW.vert ⟨cl, j⟩)
      hv a0 a1 a2 d01 d02 d12 (fun v => (M.cell cl).kind.w * sg (sideOf (M.pos ((M.cell cl).glob a0))
        (M.pos ((M.cell cl).glob a1)) (M.pos ((M.cell cl).glob a2)) (M.pos ((M.cell cl).glob v))))
    rw [e, ← termZ_real]
    split_ifs with hc
    · congr 1
      refine List.map_congr_left fun v hvt => ?_
      split_ifs with hi
      · rfl
      · simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
        obtain ⟨⟨m0, m1⟩, m2⟩ := hc
        simp only [inF, Bool.or_eq_true, beq_iff_eq, not_or] at hi
        obtain ⟨⟨n0, n1⟩, n2⟩ := hi
        have hnd : [a0, a1, a2, v].Nodup := by
          simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
            List.nodup_nil, and_true]
          exact ⟨⟨d01, d02, fun e => n0 e.symm⟩, ⟨d12, fun e => n1 e.symm⟩, fun e => n2 e.symm⟩
        have hp := side_pos (M.cell cl).kind (cellPos M cl) hO (List.get_mem _ _) a0 a1 a2 v hnd m0 m1 m2 hvt
        rw [show M.pos ((M.cell cl).glob a0) = cellPos M cl a0 from rfl,
          show M.pos ((M.cell cl).glob a1) = cellPos M cl a1 from rfl,
          show M.pos ((M.cell cl).glob a2) = cellPos M cl a2 from rfl,
          show M.pos ((M.cell cl).glob v) = cellPos M cl v from rfl, sg_of_pos hσ hp]
        ring
    · rfl
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
  have hN : ((M.cell cl).kind.cell.splits.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (shape _).2.2.2
  have hT : ((((M.cell cl).kind.tets.map (termZ (M.cell cl).kind a0 a1 a2)).sum : ℤ) : ℝ) =
      (shareZ (M.cell cl).kind a0 a1 a2 : ℝ) * (Int.sign (cenZ (M.cell cl).kind a0 a1 a2) : ℝ) / 2 := by
    linarith
  rw [hsum, share_eq _ a0 a1 a2 d01 d02 d12, Kind.w, hT]
  field_simp

/-- The weighted side sum of one cell at a global triangle `{i0, i1, i2}`. -/
def cellV (cl : Cl) (i0 i1 i2 : ι) : ℝ :=
  ∑ j : Fin (M.cell cl).kind.tets.length, ∑ o : Fin 4,
    (if M.toW.facetNodes (⟨cl, j⟩, o) = {i0, i1, i2} then
      M.toW.ω ⟨cl, j⟩ * sg (sideOf (M.pos i0) (M.pos i1) (M.pos i2) (M.pos (M.toW.vert ⟨cl, j⟩ o))) else 0)

/-- The cell sum is the share of the cell at the triangle times a cell constant. -/
theorem cellV_share (hS : MeshSplitOriented M) (cl : Cl) (i0 i1 i2 : ι) (h01 : i0 ≠ i1) (h02 : i0 ≠ i2)
    (h12 : i1 ≠ i2) : ∃ κ : ℝ, cellV M cl i0 i1 i2 = share (M.cell cl) {i0, i1, i2} * κ := by
  by_cases hr : ∃ a0 a1 a2, (M.cell cl).glob a0 = i0 ∧ (M.cell cl).glob a1 = i1 ∧ (M.cell cl).glob a2 = i2
  · obtain ⟨a0, a1, a2, rfl, rfl, rfl⟩ := hr
    obtain ⟨σ, hσ, hO⟩ := hS cl
    exact ⟨_, cell_sum' M cl hσ hO a0 a1 a2 (fun h => h01 (by rw [h])) (fun h => h02 (by rw [h]))
      (fun h => h12 (by rw [h]))⟩
  · refine ⟨0, ?_⟩
    rw [mul_zero]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun o _ => ite_eq_right fun h => hr ?_
    have hin : ∀ i ∈ ({i0, i1, i2} : Finset ι), ∃ a, (M.cell cl).glob a = i := by
      intro i hi
      rw [← h] at hi
      simp only [WMesh.facetNodes, Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true] at hi
      obtain ⟨b, -, rfl⟩ := hi
      exact ⟨_, (vert_eq M ⟨cl, j⟩ b).symm⟩
    obtain ⟨a0, h0⟩ := hin i0 (by simp)
    obtain ⟨a1, h1⟩ := hin i1 (by simp)
    obtain ⟨a2, h2⟩ := hin i2 (by simp)
    exact ⟨a0, a1, a2, h0, h1, h2⟩

/-- At a face triangle of a split-oriented cell: some sub-tetrahedron has it as a face, and the cell sum is the
share times the side sign of the fourth vertex of any such sub-tetrahedron. -/
theorem cellV_face (hS : MeshSplitOriented M) (cl : Cl) (a0 a1 a2 : Fin (M.cell cl).kind.n) (d01 : a0 ≠ a1)
    (d02 : a0 ≠ a2) (d12 : a1 ≠ a2) (fl : Bool)
    (hf : (({(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} : Finset ι), fl) ∈
      (M.cell cl).faceTris) :
    (∃ t ∈ (M.cell cl).kind.tets, ∃ v ∈ t,
      ({(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} : Finset ι) ⊆
        (t.map (M.cell cl).glob).toFinset ∧
      (M.cell cl).glob v ∉ ({(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} : Finset ι)) ∧
    ∀ t ∈ (M.cell cl).kind.tets, ∀ v ∈ t,
      ({(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} : Finset ι) ⊆
        (t.map (M.cell cl).glob).toFinset →
      (M.cell cl).glob v ∉ ({(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} : Finset ι) →
      cellV M cl ((M.cell cl).glob a0) ((M.cell cl).glob a1) ((M.cell cl).glob a2) =
        share (M.cell cl) {(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} *
          sg (sideOf (cellPos M cl a0) (cellPos M cl a1) (cellPos M cl a2) (cellPos M cl v)) := by
  have hq : (quadAny (M.cell cl).kind a0 a1 a2 || triAny (M.cell cl).kind a0 a1 a2) = true := by
    rw [Bool.or_eq_true]
    cases fl
    · exact Or.inr ((faceTris_tri _ a0 a1 a2 d01 d02 d12).mp hf)
    · exact Or.inl ((faceTris_quad _ a0 a1 a2 d01 d02 d12).mp hf)
  obtain ⟨hc0, hR⟩ := ref_side (M.cell cl).kind a0 a1 a2 d01 d02 d12 hq
  have memOf : ∀ t : List (Fin (M.cell cl).kind.n), ({(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} : Finset ι) ⊆ (t.map (M.cell cl).glob).toFinset →
      a0 ∈ t ∧ a1 ∈ t ∧ a2 ∈ t := by
    intro t h
    have m : ∀ a, (M.cell cl).glob a ∈ (t.map (M.cell cl).glob).toFinset → a ∈ t := by
      intro a ha
      simp only [List.mem_toFinset, List.mem_map] at ha
      obtain ⟨b, hb, e⟩ := ha
      rwa [← (M.cell cl).glob.injective e]
    exact ⟨m _ (h (by simp)), m _ (h (by simp)), m _ (h (by simp))⟩
  have neOf : ∀ v, (M.cell cl).glob v ∉ ({(M.cell cl).glob a0, (M.cell cl).glob a1, (M.cell cl).glob a2} : Finset ι) → v ≠ a0 ∧ v ≠ a1 ∧ v ≠ a2 := by
    intro v hv
    refine ⟨fun e => hv (by simp [e]), fun e => hv (by simp [e]), fun e => hv (by simp [e])⟩
  refine ⟨?_, fun t ht v hvt hsub hvS => ?_⟩
  · -- a sub-tetrahedron with this face: the reference sum of the face is not zero
    have hloc := (local_ok (M.cell cl).kind a0 a1 a2 d01 d02 d12).2
    have hsh : shareZ (M.cell cl).kind a0 a1 a2 ≠ 0 := by
      have hN := (shape (M.cell cl).kind).2.2.2
      unfold shareZ
      rw [Bool.or_eq_true] at hq
      split_ifs with h1 h2
      · exact_mod_cast hN
      · positivity
      · rcases hq with h | h
        · exact absurd h h1
        · exact absurd h h2
    have hne : ((M.cell cl).kind.tets.map (termZ (M.cell cl).kind a0 a1 a2)).sum ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hloc
      exact mul_ne_zero hsh (fun h => hc0 (Int.sign_eq_zero_iff_zero.mp h)) hloc.symm
    obtain ⟨z, hz, hz0⟩ := List.exists_mem_ne_zero_of_sum_ne_zero hne
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    have hct : (t.contains a0 && t.contains a1 && t.contains a2) = true := by
      by_contra h
      apply hz0
      unfold termZ
      split_ifs
      rfl
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hct
    obtain ⟨⟨m0, m1⟩, m2⟩ := hct
    obtain ⟨h4, hnd⟩ := (shape (M.cell cl).kind).1 t ht
    have hv : ∃ v ∈ t, v ≠ a0 ∧ v ≠ a1 ∧ v ≠ a2 := by
      by_contra hno
      push Not at hno
      have hsub : t.toFinset ⊆ {a0, a1, a2} := by
        intro v hv
        rw [List.mem_toFinset] at hv
        by_cases e0 : v = a0
        · simp [e0]
        by_cases e1 : v = a1
        · simp [e1]
        simp [hno v hv e0 e1]
      have := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hnd, h4] at this
      have h3 := Finset.card_le_three (a := a0) (b := a1) (c := a2)
      omega
    obtain ⟨v, hvt, n0, n1, n2⟩ := hv
    refine ⟨t, ht, v, hvt, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [List.mem_toFinset, List.mem_map]
      rcases hi with rfl | rfl | rfl
      · exact ⟨a0, m0, rfl⟩
      · exact ⟨a1, m1, rfl⟩
      · exact ⟨a2, m2, rfl⟩
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with e | e | e
      · exact n0 ((M.cell cl).glob.injective e)
      · exact n1 ((M.cell cl).glob.injective e)
      · exact n2 ((M.cell cl).glob.injective e)
  · obtain ⟨σ, hσ, hO⟩ := hS cl
    obtain ⟨m0, m1, m2⟩ := memOf t hsub
    obtain ⟨n0, n1, n2⟩ := neOf v hvS
    have hnd : [a0, a1, a2, v].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true]
      exact ⟨⟨d01, d02, fun e => n0 e.symm⟩, ⟨d12, fun e => n1 e.symm⟩, fun e => n2 e.symm⟩
    have hp := side_pos (M.cell cl).kind (cellPos M cl) hO ht a0 a1 a2 v hnd m0 m1 m2 hvt
    rw [cellV, cell_sum' M cl hσ hO a0 a1 a2 d01 d02 d12, sg_of_pos hσ hp, hR t ht m0 m1 m2 v hvt n0 n1 n2]

theorem conform_sum' (hS : MeshSplitOriented M) (bdTris : Finset (Finset ι)) (hC : ConformT M bdTris)
    (i0 i1 i2 : ι) (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2) (hSb : ({i0, i1, i2} : Finset ι) ∉ bdTris) :
    ∑ cl, cellV M cl i0 i1 i2 = 0 := by
  have hzero : ∀ cl, (∀ fl, (({i0, i1, i2} : Finset ι), fl) ∉ (M.cell cl).faceTris) → cellV M cl i0 i1 i2 = 0 := by
    intro cl hno
    obtain ⟨κ, hκ⟩ := cellV_share M hS cl i0 i1 i2 h01 h02 h12
    rw [hκ, share, ite_eq_right (hno true), ite_eq_right (hno false), zero_mul]
  by_cases h : ∃ cl fl, (({i0, i1, i2} : Finset ι), fl) ∈ (M.cell cl).faceTris
  · obtain ⟨cl, fl, hm⟩ := h
    rcases hC cl _ fl hm with ⟨hb, -⟩ | ⟨-, cl', hne, hm', huniq, hside⟩
    · exact absurd hb hSb
    rw [Fintype.sum_eq_add cl cl' hne.symm fun x hx => hzero x fun fl'' h'' => hx.2 (huniq x hx.1 fl'' h'')]
    -- local indices of the triangle in both cells
    have loc : ∀ c fl, (({i0, i1, i2} : Finset ι), fl) ∈ (M.cell c).faceTris →
        ∃ a0 a1 a2, (M.cell c).glob a0 = i0 ∧ (M.cell c).glob a1 = i1 ∧ (M.cell c).glob a2 = i2 := by
      intro c fl h
      have hin := faceTris_range _ _ fl h
      obtain ⟨a0, e0⟩ := hin i0 (by simp)
      obtain ⟨a1, e1⟩ := hin i1 (by simp)
      obtain ⟨a2, e2⟩ := hin i2 (by simp)
      exact ⟨a0, a1, a2, e0, e1, e2⟩
    obtain ⟨a0, a1, a2, e0, e1, e2⟩ := loc cl fl hm
    obtain ⟨b0, b1, b2, f0, f1, f2⟩ := loc cl' fl hm'
    subst e0 e1 e2
    have hm2 : (({(M.cell cl').glob b0, (M.cell cl').glob b1, (M.cell cl').glob b2} : Finset ι), fl) ∈
        (M.cell cl').faceTris := by rw [f0, f1, f2]; exact hm'
    have d : ∀ {c : Cl} {x y : Fin (M.cell c).kind.n}, (M.cell c).glob x ≠ (M.cell c).glob y → x ≠ y :=
      fun hxy e => hxy (by rw [e])
    obtain ⟨⟨t, ht, v, hvt, hsub, hvS⟩, hval⟩ := cellV_face M hS cl a0 a1 a2 (d h01) (d h02) (d h12) fl hm
    obtain ⟨⟨t', ht', v', hvt', hsub', hvS'⟩, hval'⟩ := cellV_face M hS cl' b0 b1 b2
      (d (by rw [f0, f1]; exact h01)) (d (by rw [f0, f2]; exact h02)) (d (by rw [f1, f2]; exact h12)) fl hm2
    have V1 := hval t ht v hvt hsub hvS
    have V2 := hval' t' ht' v' hvt' hsub' hvS'
    rw [f0, f1, f2] at V2 hsub' hvS'
    have hsd := (hside _ _ _ rfl) t ht v hvt hsub hvS t' ht' v' hvt' hsub' hvS'
    rw [V1, V2, share_of_mem _ _ fl hm, share_of_mem _ _ fl hm', ← mul_add]
    have e0 : cellPos M cl' b0 = M.pos ((M.cell cl).glob a0) := by rw [cellPos, f0]
    have e1 : cellPos M cl' b1 = M.pos ((M.cell cl).glob a1) := by rw [cellPos, f1]
    have e2 : cellPos M cl' b2 = M.pos ((M.cell cl).glob a2) := by rw [cellPos, f2]
    rw [e0, e1, e2, show cellPos M cl a0 = M.pos ((M.cell cl).glob a0) from rfl,
      show cellPos M cl a1 = M.pos ((M.cell cl).glob a1) from rfl,
      show cellPos M cl a2 = M.pos ((M.cell cl).glob a2) from rfl, sg_opp _ _ hsd, mul_zero]
  · push Not at h
    exact Finset.sum_eq_zero fun cl _ => hzero cl (h cl)

end MeshG

end Gen22

open Gen22 Asm11 CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec in
theorem p7_22_1 : Spec.P7_22_1 := by
  intro k X ⟨σ, hσ, hO⟩ s hs
  have hT : ∀ t ∈ k.cell.pull s.1 s.2, t ∈ k.tets := fun t ht => List.mem_flatMap.mpr ⟨s, hs, ht⟩
  have hc := checkK_all k
  simp only [checkK, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, Bool.not_eq_true'] at hc
  refine ⟨fun t ht => ?_, fun t ht t' ht' f hf h1 h2 h3 => ?_, fun t ht t' ht' f hf h1 h2 => ?_⟩
  · intro h0
    have := hO t (hT t ht)
    rw [show tetDet X t (kz k) = (realize X t (kz k)).edgeMat.det from rfl, h0] at this
    simp at this
  · have h0 := ((hc s hs t ht).2 f hf).1 t' ht'
    simp only [h1, h2, h3, Bool.false_eq_true, false_or, or_false] at h0
    replace h0 := h0.resolve_left (by simp)
    obtain ⟨⟨hn, hm0, hm1, hm2, hmo⟩, -, hT'⟩ := face_facts k (hT t ht) hf
    obtain ⟨hn', hm0', hm1', hm2', hmo'⟩ := hT' t' (hT t' ht') h2
    have p1 := side_pos k X hO (hT t ht) _ _ _ _ hn hm0 hm1 hm2 hmo
    have p2 := side_pos k X hO (hT t' ht') _ _ _ _ hn' hm0' hm1' hm2' hmo'
    exact (sign_pair hσ p1 p2).1 (by exact_mod_cast h0)
  · obtain ⟨⟨hn, hm0, hm1, hm2, hmo⟩, hcf, hT'⟩ := face_facts k ht hf
    obtain ⟨hn', hm0', hm1', hm2', hmo'⟩ := hT' t' ht' h2
    have p1 := side_pos k X hO ht _ _ _ _ hn hm0 hm1 hm2 hmo
    have p2 := side_pos k X hO ht' _ _ _ _ hn' hm0' hm1' hm2' hmo'
    refine (sign_pair hσ p1 p2).2 ?_
    have hnd3 : f.getD 0 (kz k) ≠ f.getD 1 (kz k) ∧ f.getD 0 (kz k) ≠ f.getD 2 (kz k) ∧
        f.getD 1 (kz k) ≠ f.getD 2 (kz k) := by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true] at hn
      exact ⟨hn.1.1, hn.1.2.1, hn.2.1.1⟩
    have hop : ∀ (o : Fin k.n), [f.getD 0 (kz k), f.getD 1 (kz k), f.getD 2 (kz k), o].Nodup →
        o ≠ f.getD 0 (kz k) ∧ o ≠ f.getD 1 (kz k) ∧ o ≠ f.getD 2 (kz k) := by
      intro o ho
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true] at ho
      exact ⟨fun e => ho.1.2.2 e.symm, fun e => ho.2.1.2 e.symm, fun e => ho.2.2 e.symm⟩
    obtain ⟨hc0, hR⟩ := ref_side k _ _ _ hnd3.1 hnd3.2.1 hnd3.2.2 (hcf h1)
    obtain ⟨o1, o2, o3⟩ := hop _ hn
    obtain ⟨o1', o2', o3'⟩ := hop _ hn'
    have s1 := hR t ht hm0 hm1 hm2 _ hmo o1 o2 o3
    have s2 := hR t' ht' hm0' hm1' hm2' _ hmo' o1' o2' o3'
    have key : ∀ x y c : ℤ, c ≠ 0 → x.sign = c.sign → y.sign = c.sign → 0 < x * y := by
      intro x y c hc hx hy
      rcases lt_trichotomy c 0 with h | h | h
      · rw [Int.sign_eq_neg_one_of_neg h, Int.sign_eq_neg_one_iff_neg] at hx hy; nlinarith
      · exact absurd h hc
      · rw [Int.sign_eq_one_of_pos h, Int.sign_eq_one_iff_pos] at hx hy; nlinarith
    exact_mod_cast key _ _ _ hc0 s1 s2

open Gen22 Asm11 CFDLean.JST1.Mixed CFDLean.JST1.Spec in
theorem p7_22_2 : Spec.P7_22_2 := by
  intro ι Cl _ _ _ _ M bdTris hS hC
  refine ⟨valid' M hS, fun S => ?_⟩
  by_cases hSb : S ∈ bdTris
  · refine Finset.sum_eq_zero fun p _ => ite_eq_right ?_
    rintro ⟨h1, h2⟩
    simp [h2, hSb] at h1
  · have e1 : ∀ p, (if decide (M.toW.facetNodes p ∈ bdTris) = false ∧ M.toW.facetNodes p = S then
        M.toW.areaVec p else 0) = if M.toW.facetNodes p = S then M.toW.areaVec p else 0 := by
      intro p
      by_cases h : M.toW.facetNodes p = S
      · rw [ite_eq_left h, ite_eq_left ⟨by simp [h, hSb], h⟩]
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
        · rw [WMesh.areaVec, facetVec_any M.toW p ((valid' M hS).2 p.1) i0 i1 i2 h01 h02 h12 h, smul_smul]
          congr 1
          rw [show M.toW.pos = M.pos from rfl]
          ring
        · simp
      rw [Finset.sum_congr rfl fun p _ => e2 p, ← Finset.sum_smul, ← Finset.mul_sum]
      have hz : ∑ p : (Σ c : Cl, Fin (M.cell c).kind.tets.length) × Fin 4,
          (if M.toW.facetNodes p = {i0, i1, i2} then M.toW.ω p.1 *
            sg (sideOf (M.pos i0) (M.pos i1) (M.pos i2) (M.pos (M.toW.vert p.1 p.2))) else 0) = 0 := by
        rw [Fintype.sum_prod_type, Fintype.sum_sigma]
        exact conform_sum' M hS bdTris hC i0 i1 i2 h01 h02 h12 hSb
      rw [hz, mul_zero, zero_smul]
    · refine Finset.sum_eq_zero fun p _ => ite_eq_right fun h => h3 ?_
      rw [← h]
      exact card_fn M p

namespace Gen22
open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec Asm11

section Aff
variable {ι Cl : Type} [Fintype ι] [DecidableEq ι] [Fintype Cl] [DecidableEq Cl] (M : Mesh ι Cl)

theorem tetDet_aff (k : Kind) (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3) (t : List (Fin k.n)) :
    tetDet (affX k A b) t (kz k) = A.det * tetDet k.ref t (kz k) := by
  rw [tetDet_D4, tetDet_D4]
  show sideOf _ _ _ _ = A.det * sideOf _ _ _ _
  rw [side_aff, sideOf_ref]

theorem ref_det_ne (k : Kind) (t : List (Fin k.n)) (ht : t ∈ k.tets) : tetDet k.ref t (kz k) ≠ 0 := by
  obtain ⟨s, hs, hts⟩ := List.mem_flatMap.mp ht
  have hc := checkK_all k
  simp only [checkK, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, Bool.not_eq_true'] at hc
  have h0 := (hc s hs t hts).1
  rw [tetDet_D4]
  show sideOf _ _ _ _ ≠ 0
  rw [sideOf_ref]
  have h4 := ((shape k).1 t ht).1
  rcases t with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, t⟩⟩⟩⟩⟩ <;> simp at h4
  simpa [sF] using h0

theorem split_oriented_aff (hA : M.Affine) : MeshSplitOriented M := by
  intro c
  have hP : cellPos M c = affX (M.cell c).kind (M.cell c).A (M.cell c).b := funext fun a => (hA c).2 a
  have hd := (hA c).1
  refine ⟨if 0 < (M.cell c).A.det then 1 else -1, by split_ifs <;> simp, fun t ht => ?_⟩
  rw [hP, tetDet_aff, ← mul_assoc, mul_assoc _ _ (tetDet _ t _)]
  have hr := ref_det_ne _ t ht
  have hsq : 0 < tetDet (M.cell c).kind.ref t (kz _) * tetDet (M.cell c).kind.ref t (kz _) :=
    mul_self_pos.mpr hr
  split_ifs with h
  · nlinarith
  · have : (M.cell c).A.det < 0 := lt_of_le_of_ne (not_lt.mp h) hd
    nlinarith

theorem faceTris_card (c : Cell ι) (S : Finset ι) (fl : Bool) (h : (S, fl) ∈ c.faceTris) : S.card = 3 := by
  have h' : ∃ f : List (Fin c.kind.n), f.length = 3 ∧ f.Nodup ∧ (f.map c.glob).toFinset = S := by
    cases fl
    · obtain ⟨f, hf, e⟩ := (mem_faceTris_false c S).mp h
      exact ⟨f, ((shape _).2.2.1 f hf).1, ((shape _).2.2.1 f hf).2, e⟩
    · obtain ⟨f, hf, e⟩ := (mem_faceTris_true c S).mp h
      exact ⟨f, ((shape _).2.1 f hf).1, ((shape _).2.1 f hf).2, e⟩
  obtain ⟨f, h3, hnd, rfl⟩ := h'
  rw [List.toFinset_card_of_nodup (hnd.map c.glob.injective), List.length_map, h3]

/-- In an affine cell, the fourth vertex of a sub-tetrahedron at a face triangle is on the centroid side. -/
theorem aff_face (hA : M.Affine) (c : Cl) (S : Finset ι) (fl : Bool) (hS : (S, fl) ∈ (M.cell c).faceTris)
    (xa xb xc : ι) (hx : S = {xa, xb, xc}) (t : List (Fin (M.cell c).kind.n)) (ht : t ∈ (M.cell c).kind.tets)
    (v : Fin (M.cell c).kind.n) (hvt : v ∈ t) (hsub : S ⊆ (t.map (M.cell c).glob).toFinset)
    (hvS : (M.cell c).glob v ∉ S) :
    0 < sideOf (M.pos xa) (M.pos xb) (M.pos xc) (cellPos M c v) *
      sideOf (M.pos xa) (M.pos xb) (M.pos xc) (M.cell c).centroid := by
  have hrange := faceTris_range _ _ fl hS
  obtain ⟨a0, e0⟩ := hrange xa (by rw [hx]; simp)
  obtain ⟨a1, e1⟩ := hrange xb (by rw [hx]; simp)
  obtain ⟨a2, e2⟩ := hrange xc (by rw [hx]; simp)
  subst e0 e1 e2
  have hcard := faceTris_card _ _ fl hS
  rw [hx] at hcard hS hsub hvS
  have d01 : a0 ≠ a1 := by
    rintro rfl; have := Finset.card_le_two (a := (M.cell c).glob a0) (b := (M.cell c).glob a2)
    simp at hcard; omega
  have d02 : a0 ≠ a2 := by
    rintro rfl; have := Finset.card_le_two (a := (M.cell c).glob a0) (b := (M.cell c).glob a1)
    rw [show ({(M.cell c).glob a0, (M.cell c).glob a1, (M.cell c).glob a0} : Finset ι) =
      {(M.cell c).glob a0, (M.cell c).glob a1} by ext; simp; tauto] at hcard; omega
  have d12 : a1 ≠ a2 := by
    rintro rfl; have := Finset.card_le_two (a := (M.cell c).glob a0) (b := (M.cell c).glob a1)
    simp at hcard; omega
  have hq : (quadAny (M.cell c).kind a0 a1 a2 || triAny (M.cell c).kind a0 a1 a2) = true := by
    rw [Bool.or_eq_true]
    cases fl
    · exact Or.inr ((faceTris_tri _ a0 a1 a2 d01 d02 d12).mp hS)
    · exact Or.inl ((faceTris_quad _ a0 a1 a2 d01 d02 d12).mp hS)
  obtain ⟨hc0, hR⟩ := ref_side _ a0 a1 a2 d01 d02 d12 hq
  have m : ∀ a, (M.cell c).glob a ∈ (t.map (M.cell c).glob).toFinset → a ∈ t := by
    intro a ha
    simp only [List.mem_toFinset, List.mem_map] at ha
    obtain ⟨b', hb, e⟩ := ha
    rwa [← (M.cell c).glob.injective e]
  have n : ∀ a, (M.cell c).glob v ≠ (M.cell c).glob a → v ≠ a := fun a h e => h (by rw [e])
  have hsg := hR t ht (m _ (hsub (by simp))) (m _ (hsub (by simp))) (m _ (hsub (by simp))) v hvt
    (n _ (fun e => hvS (by simp [e]))) (n _ (fun e => hvS (by simp [e]))) (n _ (fun e => hvS (by simp [e])))
  have hP : ∀ a, M.pos ((M.cell c).glob a) = affX (M.cell c).kind (M.cell c).A (M.cell c).b a := (hA c).2
  rw [show cellPos M c v = M.pos ((M.cell c).glob v) from rfl, hP, hP, hP, hP,
    show (M.cell c).centroid = (1 / ((M.cell c).kind.n : ℝ)) •
      ∑ a, affX (M.cell c).kind (M.cell c).A (M.cell c).b a from rfl, side_aff, side_cen]
  have hn : (0 : ℝ) < 1 / ((M.cell c).kind.n : ℝ) := by
    have := n_ne_zero (M.cell c).kind
    positivity
  have hd := (hA c).1
  have hzz : 0 < (sideZ (refZ (M.cell c).kind a0) (refZ (M.cell c).kind a1) (refZ (M.cell c).kind a2)
      (refZ (M.cell c).kind v) : ℝ) * (cenZ (M.cell c).kind a0 a1 a2 : ℝ) := by
    have : 0 < sideZ (refZ (M.cell c).kind a0) (refZ (M.cell c).kind a1) (refZ (M.cell c).kind a2)
        (refZ (M.cell c).kind v) * cenZ (M.cell c).kind a0 a1 a2 := by
      rcases lt_trichotomy (cenZ (M.cell c).kind a0 a1 a2) 0 with h | h | h
      · rw [Int.sign_eq_neg_one_of_neg h, Int.sign_eq_neg_one_iff_neg] at hsg; nlinarith
      · exact absurd h hc0
      · rw [Int.sign_eq_one_of_pos h, Int.sign_eq_one_iff_pos] at hsg; nlinarith
    exact_mod_cast this
  have : (M.cell c).A.det * (sideZ (refZ (M.cell c).kind a0) (refZ (M.cell c).kind a1) (refZ (M.cell c).kind a2)
      (refZ (M.cell c).kind v) : ℝ) * ((M.cell c).A.det * ((1 / ((M.cell c).kind.n : ℝ)) *
        (cenZ (M.cell c).kind a0 a1 a2 : ℝ))) =
      ((M.cell c).A.det * (M.cell c).A.det) * (1 / ((M.cell c).kind.n : ℝ)) *
        ((sideZ (refZ (M.cell c).kind a0) (refZ (M.cell c).kind a1) (refZ (M.cell c).kind a2)
          (refZ (M.cell c).kind v) : ℝ) * (cenZ (M.cell c).kind a0 a1 a2 : ℝ)) := by ring
  rw [this]
  exact mul_pos (mul_pos (mul_self_pos.mpr hd) hn) hzz

end Aff
end Gen22

open Gen22 Asm11 CFDLean.JST1.Mixed CFDLean.JST1.Spec in
theorem p7_22_3 : Spec.P7_22_3 := by
  intro ι Cl _ _ _ _ M bdTris hA
  refine ⟨split_oriented_aff M hA, fun hC c S fl hS => ?_⟩
  rcases hC c S fl hS with h | ⟨hb, c', hne, hS', huniq, hside⟩
  · exact Or.inl h
  refine Or.inr ⟨hb, c', hne, hS', huniq, fun xa xb xc hx t ht v hvt hsub hvS t' ht' v' hvt' hsub' hvS' => ?_⟩
  have p1 := aff_face M hA c S fl hS xa xb xc hx t ht v hvt hsub hvS
  have p2 := aff_face M hA c' S fl hS' xa xb xc hx t' ht' v' hvt' hsub' hvS'
  have hc := hside xa xb xc hx
  set x := sideOf (M.pos xa) (M.pos xb) (M.pos xc) (cellPos M c v)
  set y := sideOf (M.pos xa) (M.pos xb) (M.pos xc) (cellPos M c' v')
  set m := sideOf (M.pos xa) (M.pos xb) (M.pos xc) (M.cell c).centroid
  set m' := sideOf (M.pos xa) (M.pos xb) (M.pos xc) (M.cell c').centroid
  have : 0 < (x * m) * (y * m') := mul_pos p1 p2
  have e : (x * m) * (y * m') = (x * y) * (m * m') := by ring
  rw [e] at this
  by_contra hxy
  push Not at hxy
  nlinarith

namespace Twist22
open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec Asm11

/-- Integer coordinates of the twisted cube: `5 · twistX`. -/
def twZ : Fin 8 → Z3 := ![(0, 0, 0), (5, 0, 0), (5, 5, 0), (0, 5, 0), (3, -1, 5), (6, 3, 5), (2, 6, 5), (-1, 2, 5)]

def smulZ (c : ℤ) (u : Z3) : Z3 := (c * u.1, c * u.2.1, c * u.2.2)

/-- `-3200` times the area vector of the facet opposite local vertex `o` of the sub-tetrahedron `t` (one cell,
weight `1/64`), in the coordinates `twZ`. -/
def AZ (t : List (Fin 8)) (o : Fin 4) : Z3 :=
  smulZ (Int.sign (sideZ (twZ (t.getD (o.succAbove 0) 0)) (twZ (t.getD (o.succAbove 1) 0))
      (twZ (t.getD (o.succAbove 2) 0)) (twZ (t.getD o 0))))
    (crsZ (subZ (twZ (t.getD (o.succAbove 1) 0)) (twZ (t.getD (o.succAbove 0) 0)))
      (subZ (twZ (t.getD (o.succAbove 2) 0)) (twZ (t.getD (o.succAbove 0) 0))))

/-- The vertex set of that facet. -/
def nodesL (t : List (Fin 8)) (o : Fin 4) : Finset (Fin 8) :=
  {t.getD (o.succAbove 0) 0, t.getD (o.succAbove 1) 0, t.getD (o.succAbove 2) 0}

/-- Integer sum of the facet vectors selected by `Q`, over all sub-tetrahedra of all pulling splits. -/
def intS (Q : List (Fin 8) → Fin 4 → Bool) : Z3 :=
  (Kind.hex.tets.map fun t => ((List.finRange 4).map fun o => if Q t o then AZ t o else 0).sum).sum

def S0 : Finset (Fin 8) := {0, 1, 7}

/-- Fast forms for the kernel checks (`docs/LEAN_PERFORMANCE.md`, rule 2), tied to the originals by `rfl`. -/
def intSF (Q : List (Fin 8) → Fin 4 → Bool) : Z3 :=
  ((tetsOf RefCell.hex).map fun t => ((List.finRange 4).map fun o => if Q t o then AZ t o else 0).sum).sum

theorem intS_eq : intS = intSF := rfl

def twistBdF : Finset (Finset (Fin 8)) :=
  (((RefCell.hex.quads.flatMap fun q => (q.tris false ++ q.tris true).map fun f =>
      ((f.map (Function.Embedding.refl (Fin 8))).toFinset, true)) ++
    RefCell.hex.tris.map fun f => ((f.map (Function.Embedding.refl (Fin 8))).toFinset, false)).map Prod.fst).toFinset

theorem twistBd_eq : twistBd = twistBdF := rfl

theorem chk_nondeg : Kind.hex.tets.all (fun (t : List (Fin 8)) =>
    sideZ (twZ (t.getD 0 0)) (twZ (t.getD 1 0)) (twZ (t.getD 2 0)) (twZ (t.getD 3 0)) != 0) = true := by
  rw [hexTets_eq]
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem chk_S0 : intS (fun t o => decide (nodesL t o ∉ twistBd) && decide (nodesL t o = S0)) = (0, 200, -80) := by
  rw [intS_eq, twistBd_eq]
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem chk_v0 : intS (fun t o => decide (nodesL t o ∉ twistBd) && decide ((0 : Fin 8) ∈ nodesL t o)) =
    (680, -160, -40) := by
  rw [intS_eq, twistBd_eq]
  decide +kernel

theorem chk_dist : Kind.hex.tets.all (fun (t : List (Fin 8)) => (List.finRange 4).all fun o =>
    t.getD (o.succAbove 0) 0 != t.getD (o.succAbove 1) 0 && t.getD (o.succAbove 0) 0 != t.getD (o.succAbove 2) 0 &&
      t.getD (o.succAbove 1) 0 != t.getD (o.succAbove 2) 0) = true := by
  rw [hexTets_eq]
  decide +kernel

theorem splits_len : (Kind.hex.cell.splits.length : ℝ) = 64 := by
  have : Kind.hex.cell.splits.length = 64 := by decide +kernel
  rw [this]; norm_num

theorem twistX_eq (a : Fin 8) : twistX a = (1 / 5 : ℝ) • castZ3 (twZ a) := by
  ext α
  fin_cases a <;> fin_cases α <;> simp [twistX, castZ3, twZ] <;> norm_num

theorem sideOf_smul (c : ℝ) (a b d x : Vec 3) :
    sideOf (c • a) (c • b) (c • d) (c • x) = c ^ 3 * sideOf a b d x := by
  simp only [sideOf, cross, Num.dot, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem erase_eq : ∀ o : Fin 4, (Finset.univ.erase o) = {o.succAbove 0, o.succAbove 1, o.succAbove 2} := by
  decide

theorem cell_tw (c : Unit) : twistMesh.cell c = ⟨.hex, Function.Embedding.refl _, 1, 0⟩ := rfl

/-- A sub-tetrahedron of the twisted mesh as a list of vertices of `Fin 8`. -/
def twT (x : Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) : List (Fin 8) :=
  (twistMesh.cell x.1).kind.tets.get x.2

theorem tet_mem (x : Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) :
    twT x ∈ (Kind.hex.tets : List (List (Fin 8))) := List.get_mem _ x.2

theorem vert_tw (x : Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) (a : Fin 4) :
    twistMesh.toW.vert x a = (twT x).getD a 0 := by
  rw [vert_eq]
  dsimp only [twistMesh, twT]
  rfl

theorem nodes_tw (p : (Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) × Fin 4) :
    twistMesh.toW.facetNodes p = nodesL (twT p.1) p.2 := by
  rw [WMesh.facetNodes, erase_eq, Finset.map_insert, Finset.map_insert, Finset.map_singleton, vert_tw, vert_tw,
    vert_tw]
  rfl

theorem side_tw (a b d x : Fin 8) :
    sideOf (twistX a) (twistX b) (twistX d) (twistX x) =
      (1 / 5 : ℝ) ^ 3 * (sideZ (twZ a) (twZ b) (twZ d) (twZ x) : ℝ) := by
  rw [twistX_eq, twistX_eq, twistX_eq, twistX_eq, sideOf_smul, sideOf_cast]

theorem nondeg_tw (x : Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) : (twistMesh.toW.simplex x).Nondeg := by
  have h1 := List.all_eq_true.mp chk_nondeg (twT x) (tet_mem x)
  simp only [bne_iff_ne, ne_eq] at h1
  have hs : twistMesh.toW.simplex x = ⟨fun a => twistX ((twT x).getD a 0)⟩ := by
    unfold WMesh.simplex
    rw [show twistMesh.toW.pos = twistX from rfl]
    simp only [vert_tw]
  rw [hs, Simplex.Nondeg, Geo3.det_edge3]
  show sideOf _ _ _ _ ≠ 0
  simp only [side_tw, Fin.coe_ofNat_eq_mod]
  exact mul_ne_zero (by norm_num) (by exact_mod_cast h1)

theorem area_tw (p : (Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) × Fin 4) :
    twistMesh.toW.areaVec p = (-(1 / 3200) : ℝ) • castZ3 (AZ (twT p.1) p.2) := by
  have hd1 := List.all_eq_true.mp chk_dist (twT p.1) (tet_mem p.1)
  have hd2 := List.all_eq_true.mp hd1 p.2 (List.mem_finRange _)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hd2
  obtain ⟨⟨h01, h02⟩, h12⟩ := hd2
  have hS := nodes_tw p
  rw [WMesh.areaVec, facetVec_any twistMesh.toW p (nondeg_tw p.1) _ _ _ h01 h02 h12 hS]
  rw [show twistMesh.toW.pos = twistX from rfl, vert_tw, side_tw, sg_mul,
    show sg ((1 / 5 : ℝ) ^ 3) = 1 by simp [sg], one_mul, sg_int,
    show twistMesh.toW.ω p.1 = 1 / 64 by
      show (twistMesh.cell p.1.1).kind.w = 1 / 64
      rw [cell_tw, Kind.w, splits_len]]
  rw [twistX_eq, twistX_eq, twistX_eq]
  ext α
  fin_cases α <;>
    simp [AZ, cross3, castZ3, crsZ, subZ, smulZ] <;> ring

/-- `castZ3` as an additive map. -/
def castHom : Z3 →+ Vec 3 where
  toFun := castZ3
  map_zero' := by ext i; fin_cases i <;> simp [castZ3]
  map_add' := by intro a b; ext i; fin_cases i <;> simp [castZ3]

theorem sum_list {α β : Type} [AddCommMonoid β] (L : List α) (f : α → β) :
    ∑ j : Fin L.length, f (L.get j) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get <;> simp

set_option maxRecDepth 10000 in
theorem sum_tw (Q : List (Fin 8) → Fin 4 → Bool) :
    (∑ p : (Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) × Fin 4,
      if Q (twT p.1) p.2 = true then twistMesh.toW.areaVec p else 0) =
      (-(1 / 3200) : ℝ) • castZ3 (intS Q) := by
  have e : ∀ p : (Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) × Fin 4,
      (if Q (twT p.1) p.2 = true then twistMesh.toW.areaVec p else 0) =
      (-(1 / 3200) : ℝ) • castHom (if Q (twT p.1) p.2 = true then AZ (twT p.1) p.2 else 0) := by
    intro p
    split_ifs
    · rw [area_tw]; rfl
    · simp
  rw [Finset.sum_congr rfl fun p _ => e p, ← Finset.smul_sum, ← map_sum,
    show (⇑castHom : Z3 → Vec 3) = castZ3 from rfl]
  congr 2
  rw [Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_unique]
  have hO : ∀ t : List (Fin 8), ∑ o : Fin 4, (if Q t o = true then AZ t o else 0) =
      ((List.finRange 4).map fun o => if Q t o = true then AZ t o else 0).sum := by
    intro t
    rw [List.finRange, List.map_ofFn, List.sum_ofFn]
    rfl
  simp only [hO]
  unfold intS
  exact sum_list (α := List (Fin 8)) (β := Z3) (Kind.hex.tets : List (List (Fin 8)))
    (fun t => ((List.finRange 4).map fun o => if Q t o = true then AZ t o else 0).sum)

/-! ### `β` from all facets (any mesh), split into boundary and interior facets -/

section Beta
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)

theorem B_all (hd : 1 ≤ d) (i k : ι) :
    M.B i k = ∑ p, if i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
        ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0 := by
  have h := CFDLean.Num.Internal.Sbp6.B_facets M i k
  have hne : ((d : ℝ) * ((d : ℝ) + 1)) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hB : M.B i k = (((d : ℝ) * ((d : ℝ) + 1))⁻¹ * (if i = k then (2 : ℝ) else 1)) •
      ∑ p, (if i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then M.areaVec p else 0) := by
    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hB, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_ite, smul_zero]
  congr 1
  congr 1
  split_ifs <;> ring

theorem beta_all (hd : 1 ≤ d) (i : ι) :
    M.beta i = ∑ p, if i ∈ M.facetNodes p then (1 / (d : ℝ)) • M.areaVec p else 0 := by
  rw [← CFDLean.Num.Internal.Sbp6.B_row, Finset.sum_congr rfl fun k _ => B_all M hd i k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : i ∈ M.facetNodes p
  · rw [ite_eq_left hp]
    have e : ∀ k, (if i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
        ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0) =
        (if k ∈ M.facetNodes p then (1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1)) else 0) •
          M.areaVec p := by
      intro k
      by_cases hk : k ∈ M.facetNodes p
      · simp [hp, hk]
      · simp [hk]
    rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.sum_smul, ← Finset.sum_filter]
    congr 1
    have hfil : Finset.univ.filter (fun k => k ∈ M.facetNodes p) = M.facetNodes p := by
      ext k; simp
    rw [hfil, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hp]
    simp only [Finset.sum_const, CFDLean.Num.Internal.Sbp6.card_facetNodes, nsmul_eq_mul, mul_one]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    field_simp
  · rw [ite_eq_right hp]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [ite_eq_right]
    exact fun h => hp h.1

theorem beta_gap (hd : 1 ≤ d) (bd : C × Fin (d + 1) → Bool) (i : ι) :
    M.beta i - (∑ p, if bd p = true ∧ i ∈ M.facetNodes p then (1 / (d : ℝ)) • M.areaVec p else 0) =
      (1 / (d : ℝ)) • ∑ p, if bd p = false ∧ i ∈ M.facetNodes p then M.areaVec p else 0 := by
  rw [beta_all M hd, CFDLean.Num.Internal.Sbp6.split_bd bd (fun p => i ∈ M.facetNodes p)
    (fun p => (1 / (d : ℝ)) • M.areaVec p), add_sub_cancel_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

end Beta

theorem tetDet_tw (t : List (Fin 8)) :
    @tetDet 8 twistX t 0 = (1 / 5) ^ 3 * (sideZ (twZ (t.getD 0 0)) (twZ (t.getD 1 0))
      (twZ (t.getD 2 0)) (twZ (t.getD 3 0)) : ℝ) := by
  rw [Gen22.tetDet_D4]
  exact side_tw _ _ _ _

theorem tetDet_refh (t : List (Fin 8)) :
    @tetDet 8 Kind.hex.ref t 0 = (sideZ (refZ .hex (t.getD 0 0)) (refZ .hex (t.getD 1 0))
      (refZ .hex (t.getD 2 0)) (refZ .hex (t.getD 3 0)) : ℝ) :=
  (Gen22.tetDet_D4 _ _ _).trans (Gen22.sideOf_ref Kind.hex _ _ _ _)

theorem len5 : 5 < Kind.hex.tets.length := by decide +kernel
theorem len0 : 0 < Kind.hex.tets.length := by decide +kernel
theorem z1 : sideZ (twZ (@List.getD (Fin 8) (Kind.hex.tets.get ⟨5, len5⟩) 0 0)) (twZ (@List.getD (Fin 8) (Kind.hex.tets.get ⟨5, len5⟩) 1 0)) (twZ (@List.getD (Fin 8) (Kind.hex.tets.get ⟨5, len5⟩) 2 0)) (twZ (@List.getD (Fin 8) (Kind.hex.tets.get ⟨5, len5⟩) 3 0)) = -25 := by decide +kernel
theorem y1 : sideZ (refZ .hex (@List.getD (Fin 8) (Kind.hex.tets.get ⟨5, len5⟩) 0 0)) (refZ .hex (@List.getD (Fin 8) (Kind.hex.tets.get ⟨5, len5⟩) 1 0)) (refZ .hex (@List.getD (Fin 8) (Kind.hex.tets.get ⟨5, len5⟩) 2 0)) (refZ .hex (@List.getD (Fin 8) (Kind.hex.tets.get ⟨5, len5⟩) 3 0)) = 1 := by decide +kernel
theorem z2 : sideZ (twZ (@List.getD (Fin 8) (Kind.hex.tets.get ⟨0, len0⟩) 0 0)) (twZ (@List.getD (Fin 8) (Kind.hex.tets.get ⟨0, len0⟩) 1 0)) (twZ (@List.getD (Fin 8) (Kind.hex.tets.get ⟨0, len0⟩) 2 0)) (twZ (@List.getD (Fin 8) (Kind.hex.tets.get ⟨0, len0⟩) 3 0)) = 125 := by decide +kernel
theorem y2 : sideZ (refZ .hex (@List.getD (Fin 8) (Kind.hex.tets.get ⟨0, len0⟩) 0 0)) (refZ .hex (@List.getD (Fin 8) (Kind.hex.tets.get ⟨0, len0⟩) 1 0)) (refZ .hex (@List.getD (Fin 8) (Kind.hex.tets.get ⟨0, len0⟩) 2 0)) (refZ .hex (@List.getD (Fin 8) (Kind.hex.tets.get ⟨0, len0⟩) 3 0)) = 1 := by decide +kernel

/-! ### The trilinear map of the twisted cube -/

/-- The trilinear map of the twisted cube in closed form. -/
def Gtw (ξ : Vec 3) : Vec 3 :=
  ![(1 - ξ 2) * ξ 0 + ξ 2 * (3 / 5 * ξ 0 - 4 / 5 * ξ 1 + 3 / 5),
    (1 - ξ 2) * ξ 1 + ξ 2 * (4 / 5 * ξ 0 + 3 / 5 * ξ 1 - 1 / 5), ξ 2]

theorem trilin_def (X : Fin 8 → Vec 3) (ξ : Vec 3) : trilin X ξ =
    ∑ a : Fin 8, (∏ α : Fin 3, (Kind.hex.ref a α * ξ α + (1 - Kind.hex.ref a α) * (1 - ξ α))) • X a := rfl

theorem trilin_eq : trilin twistX = Gtw := by
  funext ξ
  ext α
  rw [trilin_def]
  fin_cases α <;>
    simp [Gtw, Fin.sum_univ_eight, Fin.prod_univ_three, Kind.ref, twistX] <;> ring

/-- Its Jacobian matrix. -/
def Jtw (ξ : Vec 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - 2 / 5 * ξ 2, -(4 / 5) * ξ 2, -(2 / 5) * ξ 0 - 4 / 5 * ξ 1 + 3 / 5;
     4 / 5 * ξ 2, 1 - 2 / 5 * ξ 2, 4 / 5 * ξ 0 - 2 / 5 * ξ 1 - 1 / 5;
     0, 0, 1]

theorem hasFDerivAt_Gtw (ξ : Vec 3) :
    HasFDerivAt Gtw (LinearMap.toContinuousLinearMap (Matrix.toLin' (Jtw ξ))) ξ := by
  rw [hasFDerivAt_pi']
  intro i
  have p0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) ξ
  have p1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) ξ
  have p2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) ξ
  fin_cases i
  · have h := ((hasFDerivAt_const 1 ξ).sub p2).mul p0 |>.add
      (p2.mul (((p0.const_mul (3 / 5)).sub (p1.const_mul (4 / 5))).add (hasFDerivAt_const (3 / 5) ξ)))
    refine h.congr_fderiv ?_
    ext v
    simp [Jtw, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    ring
  · have h := ((hasFDerivAt_const 1 ξ).sub p2).mul p1 |>.add
      (p2.mul (((p0.const_mul (4 / 5)).add (p1.const_mul (3 / 5))).sub (hasFDerivAt_const (1 / 5) ξ)))
    refine h.congr_fderiv ?_
    ext v
    simp [Jtw, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    ring
  · refine p2.congr_fderiv ?_
    ext v
    simp [Jtw, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]

theorem det_Jtw (ξ : Vec 3) : (Jtw ξ).det = 1 - 4 / 5 * ξ 2 * (1 - ξ 2) := by
  rw [Matrix.det_fin_three]
  simp [Jtw]
  ring

end Twist22

open Gen22 Twist22 Asm11 CFDLean.JST1.Mixed CFDLean.JST1.Spec in
theorem p7_22_4 : Spec.P7_22_4 := by
  refine ⟨?_, fun ξ hξ => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ∀ a : Fin 8, trilin twistX (Kind.hex.ref a) = twistX a
    intro a
    ext α
    rw [trilin_def]
    fin_cases a <;> fin_cases α <;>
      simp [Fin.sum_univ_eight, Fin.prod_univ_three, Kind.ref, twistX]
  · rw [trilin_eq, (hasFDerivAt_Gtw ξ).fderiv, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
      det_Jtw]
    have h0 := (hξ 2).1
    have h1 := (hξ 2).2
    nlinarith
  · rintro ⟨σ, hσ, hO⟩
    have q1 : 0 < σ * @tetDet 8 twistX (Kind.hex.tets.get ⟨5, len5⟩) 0 *
        @tetDet 8 Kind.hex.ref (Kind.hex.tets.get ⟨5, len5⟩) 0 := hO _ (List.get_mem _ _)
    have q2 : 0 < σ * @tetDet 8 twistX (Kind.hex.tets.get ⟨0, len0⟩) 0 *
        @tetDet 8 Kind.hex.ref (Kind.hex.tets.get ⟨0, len0⟩) 0 := hO _ (List.get_mem _ _)
    have k1 := lt_of_lt_of_eq q1 (congrArg₂ (fun a b => σ * a * b)
      ((tetDet_tw (Kind.hex.tets.get ⟨5, len5⟩)).trans (by rw [z1])) ((tetDet_refh (Kind.hex.tets.get ⟨5, len5⟩)).trans
        (by rw [y1])))
    have k2 := lt_of_lt_of_eq q2 (congrArg₂ (fun a b => σ * a * b)
      ((tetDet_tw (Kind.hex.tets.get ⟨0, len0⟩)).trans (by rw [z2])) ((tetDet_refh (Kind.hex.tets.get ⟨0, len0⟩)).trans
        (by rw [y2])))
    beta_reduce at k1 k2
    rcases hσ with rfl | rfl
    · norm_num at k1
    · norm_num at k2
  · intro c S fl h
    cases c
    left
    refine ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨(S, fl), h, rfl⟩), fun c' hc' => absurd (Subsingleton.elim _ _) hc'⟩
  · intro c S fl h
    cases c
    left
    refine ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨(S, fl), h, rfl⟩), fun c' hc' => absurd (Subsingleton.elim _ _) hc'⟩
  · intro hFB
    have h := hFB S0
    have e : ∀ p : (Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) × Fin 4,
        (if decide (twistMesh.toW.facetNodes p ∈ twistBd) = false ∧ twistMesh.toW.facetNodes p = S0 then
          twistMesh.toW.areaVec p else 0) =
        if (decide (nodesL (twT p.1) p.2 ∉ twistBd) && decide (nodesL (twT p.1) p.2 = S0)) = true then
          twistMesh.toW.areaVec p else 0 := by
      intro p
      rw [nodes_tw]
      refine if_congr ?_ rfl rfl
      rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_false_iff_not]
    rw [Finset.sum_congr rfl fun p _ => e p,
      sum_tw (fun t o => decide (nodesL t o ∉ twistBd) && decide (nodesL t o = S0)), chk_S0] at h
    have := congrFun h 1
    simp [castZ3] at this
  · refine ⟨0, fun hb => ?_⟩
    have hg := beta_gap twistMesh.toW (by norm_num) (fun p => decide (twistMesh.toW.facetNodes p ∈ twistBd)) 0
    simp only [Nat.cast_ofNat] at hg
    rw [hb, sub_self] at hg
    have e : ∀ p : (Σ c : Unit, Fin (twistMesh.cell c).kind.tets.length) × Fin 4,
        (if decide (twistMesh.toW.facetNodes p ∈ twistBd) = false ∧ (0 : Fin 8) ∈ twistMesh.toW.facetNodes p then
          twistMesh.toW.areaVec p else 0) =
        if (decide (nodesL (twT p.1) p.2 ∉ twistBd) && decide ((0 : Fin 8) ∈ nodesL (twT p.1) p.2)) = true
          then twistMesh.toW.areaVec p else 0 := by
      intro p
      rw [nodes_tw]
      refine if_congr ?_ rfl rfl
      rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_false_iff_not]
    rw [Finset.sum_congr rfl fun p _ => e p,
      sum_tw (fun t o => decide (nodesL t o ∉ twistBd) && decide ((0 : Fin 8) ∈ nodesL t o)), chk_v0] at hg
    have := congrFun hg 0
    norm_num [castZ3] at this

end CFDLean.JST1.Proofs

