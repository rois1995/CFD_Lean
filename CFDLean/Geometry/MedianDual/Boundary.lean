import CFDLean.Geometry.MedianDual.Edges

noncomputable section
namespace CFDLean.MedianDual.MeshData
open Coordinates
open scoped BigOperators
variable {n m : ℕ}

/-- The exterior patch retains its owning cell, primal face and primal node identity. -/
abbrev Boundary (M : MeshData n m) :=
  {an : M.Occurrence × Fin n // M.faceCount (M.faceID an.1) = 1 ∧ an.2 ∈ M.faceID an.1}
instance (M : MeshData n m) : Fintype M.Boundary := Fintype.ofFinite _

def boundaryArea (M : MeshData n m) (b : M.Boundary) : Vector 3 := (1 / 3 : ℝ) • M.faceArea b.1.1

def ownedPatch (M : MeshData n m) (a : M.Occurrence) (i : Fin n) : Vector 3 :=
  if i ∈ M.faceID a then (1 / 3 : ℝ) • M.faceArea a else 0

theorem ownedPatch_local (M : MeshData n m) (a : M.Occurrence) (i : Fin n) :
    M.ownedPatch a i = ∑ j, if M.vertex a.1 j = i then localPatch (M.points a.1) a.2 j else 0 := by
  classical
  simp_rw [localPatch_eq]
  have he (j : Fin 4) :
      (if M.vertex a.1 j = i then if j.val = a.2.val then 0 else (1/3 : ℝ) • faceVector (M.points a.1) a.2 else 0) =
      if j = a.2 then 0 else if M.vertex a.1 j = i then (1/3 : ℝ) • M.faceArea a else 0 := by
    by_cases h : j = a.2
    · simp [h]
    · have hv : j.val ≠ a.2.val := fun hh => h (Fin.ext hh)
      simp [h, hv, faceArea]
  simp_rw [he]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a.2)]
  simp only [if_pos rfl, add_zero]
  rw [Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
  simpa only [ownedPatch, faceID, faceNodes, if_true, add_zero] using
    (M.index_indicator a.1 (Finset.univ.erase a.2) i ((1/3 : ℝ) • M.faceArea a)).symm

theorem faceCount_pos (M : MeshData n m) (a : M.Occurrence) : 0 < M.faceCount (M.faceID a) := by
  apply Finset.card_pos.mpr
  exact ⟨a, by simp [faceOccurrences]⟩

theorem face_other (M : MeshData n m) (a : M.Occurrence) (h : M.faceCount (M.faceID a) = 2) :
    ∃! b, b ≠ a ∧ M.faceID b = M.faceID a := by
  classical
  obtain ⟨b, c, hbc, hset⟩ := Finset.card_eq_two.mp h
  have ha : a ∈ M.faceOccurrences (M.faceID a) := by simp [faceOccurrences]
  rw [hset] at ha
  have members (d : M.Occurrence) : M.faceID d = M.faceID a ↔ d = b ∨ d = c := by
    have : d ∈ M.faceOccurrences (M.faceID a) ↔ d = b ∨ d = c := by rw [hset]; simp
    simpa only [faceOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] using this
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · refine ⟨c, ⟨hbc.symm, (members c).mpr (Or.inr rfl)⟩, ?_⟩
    intro d hd
    exact ((members d).mp hd.2).resolve_left hd.1
  · refine ⟨b, ⟨hbc, (members b).mpr (Or.inl rfl)⟩, ?_⟩
    intro d hd
    exact ((members d).mp hd.2).resolve_right hd.1

abbrev Interior (M : MeshData n m) := {a : M.Occurrence // M.faceCount (M.faceID a) = 2}
instance (M : MeshData n m) : Fintype M.Interior := Fintype.ofFinite _

def partner (M : MeshData n m) (a : M.Interior) : M.Interior :=
  ⟨Classical.choose (M.face_other a.1 a.prop), by
    rw [(Classical.choose_spec (M.face_other a.1 a.prop)).1.2]
    exact a.prop⟩

theorem partner_ne (M : MeshData n m) (a : M.Interior) : M.partner a ≠ a := by
  intro h
  exact (Classical.choose_spec (M.face_other a.1 a.prop)).1.1 (congrArg Subtype.val h)

theorem partner_face (M : MeshData n m) (a : M.Interior) : M.faceID (M.partner a).1 = M.faceID a.1 :=
  (Classical.choose_spec (M.face_other a.1 a.prop)).1.2

theorem partner_involutive (M : MeshData n m) : Function.Involutive M.partner := by
  intro a
  apply Subtype.ext
  exact ((Classical.choose_spec (M.face_other (M.partner a).1 (M.partner a).prop)).2 a.1
    ⟨fun h => M.partner_ne a (Subtype.ext h.symm), (M.partner_face a).symm⟩).symm

theorem interior_cancel (M : MeshData n m) (h : M.Conforming) (i : Fin n) :
    (∑ a : M.Interior, M.ownedPatch a.1 i) = 0 := by
  classical
  apply Finset.sum_involution (fun a _ => M.partner a)
  · intro a _
    have hc := M.faceArea_cancel h a.1 (M.partner a).1
      (fun hh => M.partner_ne a (Subtype.ext hh.symm)) (M.partner_face a).symm
    simp only [ownedPatch, M.partner_face a, hc]
    split_ifs <;> module
  · intro a _ _
    exact M.partner_ne a
  · intro a _
    exact Finset.mem_univ _
  · intro a _
    exact M.partner_involutive a

theorem boundary_sum (M : MeshData n m) (i : Fin n) :
    (∑ b : M.Boundary, if b.1.2 = i then M.boundaryArea b else 0) =
      ∑ a : M.Occurrence, if M.faceCount (M.faceID a) = 1 then M.ownedPatch a i else 0 := by
  classical
  simp only [boundaryArea]
  rw [← Finset.sum_subtype (F := inferInstance)
    (Finset.univ.filter (fun an : M.Occurrence × Fin n =>
      M.faceCount (M.faceID an.1) = 1 ∧ an.2 ∈ M.faceID an.1)) (by simp)
    (fun an => if an.2 = i then (1/3 : ℝ) • M.faceArea an.1 else 0)]
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : M.faceCount (M.faceID a) = 1
  · simp [h, ownedPatch, and_comm, ite_and]
  · simp [h]

theorem all_patches_boundary (M : MeshData n m) (h : M.Conforming) (i : Fin n) :
    (∑ a : M.Occurrence, M.ownedPatch a i) =
      ∑ b : M.Boundary, if b.1.2 = i then M.boundaryArea b else 0 := by
  classical
  rw [M.boundary_sum]
  have hi : (∑ a : M.Occurrence, if M.faceCount (M.faceID a) = 2 then M.ownedPatch a i else 0) = 0 := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (F := inferInstance) (p := fun a => M.faceCount (M.faceID a) = 2)
      (Finset.univ.filter (fun a => M.faceCount (M.faceID a) = 2)) (by simp)]
    exact M.interior_cancel h i
  have hs : (∑ a : M.Occurrence, M.ownedPatch a i) =
      (∑ a : M.Occurrence, if M.faceCount (M.faceID a) = 1 then M.ownedPatch a i else 0) +
      ∑ a : M.Occurrence, if M.faceCount (M.faceID a) = 2 then M.ownedPatch a i else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have hp := M.faceCount_pos a
    have hl := h.faceMultiplicity (M.faceID a)
    have he : M.faceCount (M.faceID a) = 1 ∨ M.faceCount (M.faceID a) = 2 := by omega
    rcases he with he | he <;> simp [he]
  rw [hs, hi, add_zero]

theorem faceCount_one_unique (M : MeshData n m) (a b : M.Occurrence)
    (ha : M.faceCount (M.faceID a) = 1) (hab : M.faceID b = M.faceID a) : a = b := by
  classical
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp ha
  have hma : a ∈ M.faceOccurrences (M.faceID a) := by simp [faceOccurrences]
  have hmb : b ∈ M.faceOccurrences (M.faceID a) := by simp [faceOccurrences, hab]
  rw [hc, Finset.mem_singleton] at hma hmb
  exact hma.trans hmb.symm

def boundaryKey (M : MeshData n m) (b : M.Boundary) : Finset (Fin n) × Fin n :=
  (M.faceID b.1.1, b.1.2)

theorem boundaryKey_injective (M : MeshData n m) : Function.Injective M.boundaryKey := by
  intro a b hab
  have hf := congrArg Prod.fst hab
  have hn := congrArg Prod.snd hab
  apply Subtype.ext
  exact Prod.ext (M.faceCount_one_unique a.1.1 b.1.1 a.prop.1 hf.symm) hn

/-- Exactly one record for each exterior primal face and each of its three owning nodes. -/
theorem boundaryKey_range (M : MeshData n m) (F : Finset (Fin n)) (i : Fin n) :
    (∃ b : M.Boundary, M.boundaryKey b = (F,i)) ↔ M.faceCount F = 1 ∧ i ∈ F := by
  classical
  constructor
  · rintro ⟨b, hb⟩
    have hf : M.faceID b.1.1 = F := congrArg Prod.fst hb
    have hi : b.1.2 = i := congrArg Prod.snd hb
    simpa only [hf, hi] using b.prop
  · rintro ⟨hc, hi⟩
    have hp : 0 < (M.faceOccurrences F).card := by change 0 < M.faceCount F; omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
    have hf : M.faceID a = F := (Finset.mem_filter.mp ha).2
    exact ⟨⟨(a,i), by simpa [hf] using And.intro hc hi⟩, Prod.ext hf rfl⟩

end CFDLean.MedianDual.MeshData
