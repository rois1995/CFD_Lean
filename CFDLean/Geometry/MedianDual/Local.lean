import CFDLean.Discrete.Assembly

noncomputable section
namespace CFDLean.MedianDual
open Coordinates
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

abbrev Points := Fin 4 → Vector 3
private theorem fin4_val_three : (3 : Fin 4).val = 3 := rfl
attribute [local simp] fin4_val_three

def cross (a b : Vector 3) : Vector 3 :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
def determinant (a b c : Vector 3) : ℝ := dot a (cross b c)
def triangle (a b c : Vector 3) : Vector 3 := (1 / 2 : ℝ) • cross (b - a) (c - a)
def sixVolume (p : Points) : ℝ := determinant (p 1 - p 0) (p 2 - p 0) (p 3 - p 0)
def volume (p : Points) : ℝ := |sixVolume p| / 6
def midpoint (p : Points) (i j : Fin 4) : Vector 3 := (1 / 2 : ℝ) • (p i + p j)
def faceCenter (p : Points) (i j k : Fin 4) : Vector 3 := (1 / 3 : ℝ) • (p i + p j + p k)
def cellCenter (p : Points) : Vector 3 := (1 / 4 : ℝ) • (p 0 + p 1 + p 2 + p 3)

def valid (i j k l : Fin 4) : Prop :=
  i.val ≠ j.val ∧ i.val ≠ k.val ∧ i.val ≠ l.val ∧ j.val ≠ k.val ∧ j.val ≠ l.val ∧ k.val ≠ l.val
instance (i j k l : Fin 4) : Decidable (valid i j k l) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def frameSign (i j k l : Fin 4) : ℝ := (-1 : ℝ) ^
  ((if i.val > j.val then 1 else 0) + (if i.val > k.val then 1 else 0) +
   (if i.val > l.val then 1 else 0) + (if j.val > k.val then 1 else 0) +
   (if j.val > l.val then 1 else 0) + (if k.val > l.val then 1 else 0) : ℕ)

def faceVector (p : Points) (i : Fin 4) : Vector 3 :=
  ![triangle (p 1) (p 2) (p 3), -triangle (p 0) (p 2) (p 3),
    triangle (p 0) (p 1) (p 3), -triangle (p 0) (p 1) (p 2)] i

def faceBase (p : Points) (i : Fin 4) : Vector 3 := ![p 1, p 0, p 0, p 0] i

def flagPoints (p : Points) (i j k _l : Fin 4) : Points :=
  ![p i, midpoint p i j, faceCenter p i j k, cellCenter p]

def outwardTriangle (p : Points) (i j k l : Fin 4) : Vector 3 :=
  frameSign i j k l • triangle (midpoint p i j) (faceCenter p i j k) (cellCenter p)

def flagBoundary (p : Points) (i j k l r : Fin 4) : Vector 3 :=
  frameSign i j k l • faceVector (flagPoints p i j k l) r

def localInterface (p : Points) (i j : Fin 4) : Vector 3 :=
  ∑ k, ∑ l, if valid i j k l then outwardTriangle p i j k l else 0

def localPatch (p : Points) (opp owner : Fin 4) : Vector 3 :=
  ∑ j, ∑ k, if valid owner j k opp then flagBoundary p owner j k opp 3 else 0

theorem faceVector_sum (p : Points) : ∑ i, faceVector p i = 0 := by
  ext q
  fin_cases q <;> simp [Fin.sum_univ_four, faceVector, triangle, cross] <;> ring

theorem faceVector_opposite_dot (p : Points) (i : Fin 4) :
    dot (faceVector p i) (p i - faceBase p i) = -sixVolume p / 2 := by
  fin_cases i <;> simp [faceVector, faceBase, triangle, cross, sixVolume, determinant, dot_three] <;> ring

theorem faceVector_tangent (p : Points) (i j : Fin 4) (h : i.val ≠ j.val) :
    dot (faceVector p i) (p j - faceBase p i) = 0 := by
  fin_cases i <;> fin_cases j <;> revert h <;> norm_num <;>
    simp [faceVector, faceBase, triangle, cross, dot_three] <;> ring

theorem frameSign_abs (i j k l : Fin 4) : |frameSign i j k l| = 1 := by
  simp [frameSign, abs_pow]

theorem ordered_determinant (p : Points) (i j k l : Fin 4) (h : valid i j k l) :
    determinant (p j - p i) (p k - p i) (p l - p i) = frameSign i j k l * sixVolume p := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    revert h <;> norm_num [valid, frameSign] <;> simp [sixVolume, determinant, cross, dot_three] <;> ring

theorem fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  fin_cases i <;> decide

theorem frame_sum (p : Points) (i j k l : Fin 4) (h : valid i j k l) :
    p i + p j + p k + p l = p 0 + p 1 + p 2 + p 3 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases k with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases l with rfl | rfl | rfl | rfl <;>
    revert h <;> norm_num [valid] <;> ac_rfl

theorem barycentric_determinant (a b c d : Vector 3) :
    determinant ((1 / 2 : ℝ) • (a + b) - a) ((1 / 3 : ℝ) • (a + b + c) - a)
      ((1 / 4 : ℝ) • (a + b + c + d) - a) = determinant (b - a) (c - a) (d - a) / 24 := by
  simp [determinant, cross, dot_three]
  ring

theorem barycentric_triangle_dot (a b c d : Vector 3) :
    dot (triangle ((1 / 2 : ℝ) • (a + b)) ((1 / 3 : ℝ) • (a + b + c))
      ((1 / 4 : ℝ) • (a + b + c + d))) (b - a) = determinant (b - a) (c - a) (d - a) / 24 := by
  simp [triangle, determinant, cross, dot_three]
  ring

theorem dot_smul_left (a : ℝ) (v w : Vector 3) : dot (a • v) w = a * dot v w := by
  simp [dot_three]
  ring

theorem frameSign_sq (i j k l : Fin 4) : frameSign i j k l ^ 2 = 1 := by
  rw [← sq_abs, frameSign_abs]
  norm_num

theorem flag_determinant (p : Points) (i j k l : Fin 4) (h : valid i j k l) :
    sixVolume (flagPoints p i j k l) = frameSign i j k l * sixVolume p / 24 := by
  have hc : cellCenter p = (1 / 4 : ℝ) • (p i + p j + p k + p l) := by
    rw [frame_sum p i j k l h]
    rfl
  change determinant (midpoint p i j - p i) (faceCenter p i j k - p i) (cellCenter p - p i) = _
  rw [hc]
  change determinant ((1 / 2 : ℝ) • (p i + p j) - p i)
    ((1 / 3 : ℝ) • (p i + p j + p k) - p i) ((1 / 4 : ℝ) • (p i + p j + p k + p l) - p i) = _
  rw [barycentric_determinant, ordered_determinant p i j k l h]

theorem flag_volume (p : Points) (i j k l : Fin 4) (h : valid i j k l) :
    volume (flagPoints p i j k l) = volume p / 24 := by
  unfold volume
  rw [flag_determinant p i j k l h, abs_div, abs_mul, frameSign_abs]
  norm_num
  ring

theorem outwardTriangle_dot (p : Points) (i j k l : Fin 4) (h : valid i j k l) :
    dot (outwardTriangle p i j k l) (p j - p i) = sixVolume p / 24 := by
  have hc : cellCenter p = (1 / 4 : ℝ) • (p i + p j + p k + p l) := by
    rw [frame_sum p i j k l h]
    rfl
  unfold outwardTriangle midpoint faceCenter
  rw [dot_smul_left, hc, barycentric_triangle_dot, ordered_determinant p i j k l h]
  calc
    _ = frameSign i j k l ^ 2 * sixVolume p / 24 := by ring
    _ = _ := by rw [frameSign_sq]; ring

theorem flagBoundary_three (p : Points) (i j k l : Fin 4) :
    flagBoundary p i j k l 3 = frameSign i j k l •
      (-triangle (p i) (midpoint p i j) (faceCenter p i j k)) := rfl

set_option maxHeartbeats 1000000 in
theorem localInterface_eq (p : Points) (i j : Fin 4) :
    localInterface p i j = (1 / 12 : ℝ) • (faceVector p i - faceVector p j) := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
    simp +decide only [localInterface, Fin.sum_univ_four, valid, add_zero, zero_add, ite_true, ite_false]
  all_goals
    ext q
    fin_cases q <;> simp +decide [outwardTriangle, frameSign, midpoint, faceCenter, cellCenter, faceVector, triangle, cross]
    all_goals ring

set_option maxHeartbeats 1000000 in
theorem localPatch_eq (p : Points) (opp owner : Fin 4) :
    localPatch p opp owner = if owner.val = opp.val then 0 else (1 / 3 : ℝ) • faceVector p opp := by
  rcases fin4_cases opp with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases owner with rfl | rfl | rfl | rfl <;>
    simp +decide only [localPatch, Fin.sum_univ_four, valid, add_zero, zero_add, ite_true, ite_false]
  all_goals simp only [flagBoundary_three]
  all_goals
    ext q
    fin_cases q <;> (simp +decide [frameSign, midpoint, faceCenter, faceVector, triangle, cross]; ring)

theorem localInterface_reverse (p : Points) (i j : Fin 4) :
    localInterface p j i = -localInterface p i j := by
  rw [localInterface_eq, localInterface_eq]
  module

theorem localInterface_self (p : Points) (i : Fin 4) : localInterface p i i = 0 := by
  rw [localInterface_eq, sub_self, smul_zero]


abbrev VertexFlags (i : Fin 4) := {q : Fin 4 × Fin 4 × Fin 4 // valid i q.1 q.2.1 q.2.2}

theorem vertexFlags_card (i : Fin 4) : Fintype.card (VertexFlags i) = 6 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide

def localDualVolume (p : Points) (i : Fin 4) : ℝ :=
  ∑ f : VertexFlags i, volume (flagPoints p i f.1.1 f.1.2.1 f.1.2.2)

theorem localDualVolume_eq (p : Points) (i : Fin 4) : localDualVolume p i = volume p / 4 := by
  calc
    localDualVolume p i = ∑ _f : VertexFlags i, volume p / 24 := by
      unfold localDualVolume
      apply Finset.sum_congr rfl
      intro f _
      exact flag_volume p i f.1.1 f.1.2.1 f.1.2.2 f.prop
    _ = volume p / 4 := by simp [vertexFlags_card]; ring

theorem flag_card : Fintype.card (Σ i : Fin 4, VertexFlags i) = 24 := by
  simp [Fintype.card_sigma, vertexFlags_card]

theorem flagBoundary_sum (p : Points) (i j k l : Fin 4) : ∑ r, flagBoundary p i j k l r = 0 := by
  simp only [flagBoundary, ← Finset.smul_sum, faceVector_sum, smul_zero]

theorem frameSign_swapJK (i j k l : Fin 4) (h : valid i j k l) :
    frameSign i k j l = -frameSign i j k l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    revert h <;> norm_num [valid, frameSign]

theorem frameSign_swapKL (i j k l : Fin 4) (h : valid i j k l) :
    frameSign i j l k = -frameSign i j k l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    revert h <;> norm_num [valid, frameSign]

theorem faceCenter_swap (p : Points) (i j k : Fin 4) : faceCenter p i k j = faceCenter p i j k := by
  unfold faceCenter
  congr 1
  ac_rfl

theorem internal_face_one_pair (p : Points) (i j k l : Fin 4) (h : valid i j k l) :
    flagBoundary p i j k l 1 + flagBoundary p i k j l 1 = 0 := by
  change frameSign i j k l • (-triangle (p i) (faceCenter p i j k) (cellCenter p)) +
    frameSign i k j l • (-triangle (p i) (faceCenter p i k j) (cellCenter p)) = 0
  rw [frameSign_swapJK i j k l h, faceCenter_swap]
  module

theorem internal_face_two_pair (p : Points) (i j k l : Fin 4) (h : valid i j k l) :
    flagBoundary p i j k l 2 + flagBoundary p i j l k 2 = 0 := by
  change frameSign i j k l • triangle (p i) (midpoint p i j) (cellCenter p) +
    frameSign i j l k • triangle (p i) (midpoint p i j) (cellCenter p) = 0
  rw [frameSign_swapKL i j k l h]
  module

theorem valid_swapJK {i j k l : Fin 4} (h : valid i j k l) : valid i k j l :=
  ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1.symm, h.2.2.2.2.2, h.2.2.2.2.1⟩

theorem valid_swapKL {i j k l : Fin 4} (h : valid i j k l) : valid i j l k :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.2.symm⟩

def swapJK (i : Fin 4) (f : VertexFlags i) : VertexFlags i :=
  ⟨(f.1.2.1, f.1.1, f.1.2.2), valid_swapJK f.prop⟩
def swapKL (i : Fin 4) (f : VertexFlags i) : VertexFlags i :=
  ⟨(f.1.1, f.1.2.2, f.1.2.1), valid_swapKL f.prop⟩

theorem swapJK_involutive (i : Fin 4) : Function.Involutive (swapJK i) := by
  intro f
  apply Subtype.ext
  rfl

theorem swapKL_involutive (i : Fin 4) : Function.Involutive (swapKL i) := by
  intro f
  apply Subtype.ext
  rfl

theorem swapJK_ne (i : Fin 4) (f : VertexFlags i) : swapJK i f ≠ f := by
  intro h
  have hv := congrArg (fun q : VertexFlags i => q.1.1.val) h
  exact f.prop.2.2.2.1 hv.symm

theorem swapKL_ne (i : Fin 4) (f : VertexFlags i) : swapKL i f ≠ f := by
  intro h
  have hv := congrArg (fun q : VertexFlags i => q.1.2.1.val) h
  exact f.prop.2.2.2.2.2 hv.symm

theorem sum_internal_one (p : Points) (i : Fin 4) :
    (∑ f : VertexFlags i, flagBoundary p i f.1.1 f.1.2.1 f.1.2.2 1) = 0 := by
  apply Finset.sum_involution (fun f _ => swapJK i f)
  · intro f _
    exact internal_face_one_pair p i f.1.1 f.1.2.1 f.1.2.2 f.prop
  · intro f _ _
    exact swapJK_ne i f
  · intro f _
    exact Finset.mem_univ _
  · intro f _
    exact swapJK_involutive i f

theorem sum_internal_two (p : Points) (i : Fin 4) :
    (∑ f : VertexFlags i, flagBoundary p i f.1.1 f.1.2.1 f.1.2.2 2) = 0 := by
  apply Finset.sum_involution (fun f _ => swapKL i f)
  · intro f _
    exact internal_face_two_pair p i f.1.1 f.1.2.1 f.1.2.2 f.prop
  · intro f _ _
    exact swapKL_ne i f
  · intro f _
    exact Finset.mem_univ _
  · intro f _
    exact swapKL_involutive i f

def localHullVector (p : Points) (i : Fin 4) : Vector 3 :=
  ∑ f : VertexFlags i, (flagBoundary p i f.1.1 f.1.2.1 f.1.2.2 0 + flagBoundary p i f.1.1 f.1.2.1 f.1.2.2 3)

theorem flag_boundaries_identify (p : Points) (i : Fin 4) :
    (∑ f : VertexFlags i, ∑ r, flagBoundary p i f.1.1 f.1.2.1 f.1.2.2 r) = localHullVector p i := by
  simp only [Fin.sum_univ_four, Finset.sum_add_distrib, localHullVector]
  rw [sum_internal_one, sum_internal_two]
  module

theorem vertexFlags_sum (i : Fin 4) (f : Fin 4 → Fin 4 → Fin 4 → Vector 3) :
    (∑ a : VertexFlags i, f a.1.1 a.1.2.1 a.1.2.2) =
      ∑ j, ∑ k, ∑ l, if valid i j k l then f j k l else 0 := by
  let s : Finset (Fin 4 × Fin 4 × Fin 4) := Finset.univ.filter (fun q => valid i q.1 q.2.1 q.2.2)
  have h := (Finset.sum_subtype (F := inferInstance) (p := fun q => valid i q.1 q.2.1 q.2.2) s (by intro q; simp [s]) (fun q => f q.1 q.2.1 q.2.2)).symm
  simpa only [s, Finset.sum_filter, Fintype.sum_prod_type] using h

theorem localHull_identification (p : Points) (i : Fin 4) :
    localHullVector p i = (∑ j, localInterface p i j) + ∑ j, localPatch p j i := by
  unfold localHullVector
  rw [vertexFlags_sum i (fun j k l => flagBoundary p i j k l 0 + flagBoundary p i j k l 3)]
  have hi (j k l : Fin 4) :
      (if valid i j k l then flagBoundary p i j k l 0 + flagBoundary p i j k l 3 else 0) =
      (if valid i j k l then flagBoundary p i j k l 0 else 0) +
      (if valid i j k l then flagBoundary p i j k l 3 else 0) := by
    by_cases h : valid i j k l <;> simp [h]
  simp_rw [hi, Finset.sum_add_distrib]
  congr 1
  calc
    _ = ∑ j, ∑ l, ∑ k, if valid i j k l then flagBoundary p i j k l 3 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]; rfl

theorem local_closure (p : Points) (i : Fin 4) :
    (∑ j, localInterface p i j) + ∑ j, localPatch p j i = 0 := by
  rw [← localHull_identification, ← flag_boundaries_identify]
  simp only [flagBoundary_sum, Finset.sum_const_zero]

theorem faceBase_succAbove (p : Points) (i : Fin 4) : faceBase p i = p (i.succAbove 0) := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> rfl

theorem faceVector_triangle_or_neg (p : Points) (i : Fin 4) :
    faceVector p i = triangle (p (i.succAbove 0)) (p (i.succAbove 1)) (p (i.succAbove 2)) ∨
    faceVector p i = -triangle (p (i.succAbove 0)) (p (i.succAbove 1)) (p (i.succAbove 2)) := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · left; rfl
  · right; rfl
  · left; rfl
  · right; rfl

theorem triangle_cyclic (a b c : Vector 3) : triangle b c a = triangle a b c := by
  ext q
  fin_cases q <;> simp [triangle, cross] <;> ring

theorem triangle_reverse (a b c : Vector 3) : triangle a c b = -triangle a b c := by
  ext q
  fin_cases q <;> simp [triangle, cross] <;> ring

theorem sixVolume_swap12 (p : Points) : sixVolume ![p 0, p 2, p 1, p 3] = -sixVolume p := by
  simp [sixVolume, determinant, cross, dot_three]
  ring

theorem nonzero_has_positive_order (p : Points) (h : sixVolume p ≠ 0) :
    0 < sixVolume p ∨ 0 < sixVolume ![p 0, p 2, p 1, p 3] := by
  rcases lt_or_gt_of_ne h with hn | hp
  · right
    rw [sixVolume_swap12]
    linarith
  · exact Or.inl hp

end CFDLean.MedianDual
