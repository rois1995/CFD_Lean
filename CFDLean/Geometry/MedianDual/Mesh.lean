import CFDLean.Geometry.MedianDual.Local
import Mathlib.Analysis.Convex.Hull

noncomputable section
namespace CFDLean.MedianDual
open Coordinates
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

/-- Positively ordered nondegenerate cells; the conforming embedding is a separate predicate. -/
structure MeshData (n m : ℕ) where
  position : Fin n → Vector 3
  vertex : Fin m → (Fin 4 ↪ Fin n)
  positive : ∀ t, 0 < sixVolume (fun i => position (vertex t i))

namespace MeshData
variable {n m : ℕ}

def points (M : MeshData n m) (t : Fin m) : Points := fun i => M.position (M.vertex t i)
def cellNodes (M : MeshData n m) (t : Fin m) : Finset (Fin n) := Finset.univ.map (M.vertex t)
def faceNodes (M : MeshData n m) (t : Fin m) (j : Fin 4) : Finset (Fin n) :=
  (Finset.univ.erase j).map (M.vertex t)
def Used (M : MeshData n m) (a : Fin n) : Prop := ∃ t i, M.vertex t i = a
abbrev Occurrence (_M : MeshData n m) := Fin m × Fin 4

def faceID (M : MeshData n m) (a : M.Occurrence) : Finset (Fin n) := M.faceNodes a.1 a.2
def faceOccurrences (M : MeshData n m) (F : Finset (Fin n)) : Finset M.Occurrence :=
  Finset.univ.filter (fun a => M.faceID a = F)
def faceCount (M : MeshData n m) (F : Finset (Fin n)) : ℕ := (M.faceOccurrences F).card

def faceArea (M : MeshData n m) (a : M.Occurrence) : Vector 3 := faceVector (M.points a.1) a.2
def baseNode (M : MeshData n m) (a : M.Occurrence) : Fin n := M.vertex a.1 (a.2.succAbove 0)
def oppositeNode (M : MeshData n m) (a : M.Occurrence) : Fin n := M.vertex a.1 a.2

/-- Caller geometry assumptions; neither area closure nor a volume conclusion is included. -/
structure Conforming (M : MeshData n m) : Prop where
  uniqueCells : Function.Injective M.cellNodes
  injectiveUsed : ∀ a b, M.Used a → M.Used b → M.position a = M.position b → a = b
  intersections : ∀ t u, t ≠ u →
    convexHull ℝ (Set.range (M.points t)) ∩ convexHull ℝ (Set.range (M.points u)) =
      convexHull ℝ (M.position '' ((M.cellNodes t ∩ M.cellNodes u : Finset (Fin n)) : Set (Fin n)))
  faceMultiplicity : ∀ F, M.faceCount F ≤ 2
  oppositeSides : ∀ a b : M.Occurrence, a ≠ b → M.faceID a = M.faceID b →
    0 < dot (M.faceArea a) (M.position (M.oppositeNode b) - M.position (M.baseNode a))

theorem cellNodes_card (M : MeshData n m) (t : Fin m) : (M.cellNodes t).card = 4 := by
  simp [cellNodes]

theorem faceNodes_card (M : MeshData n m) (t : Fin m) (j : Fin 4) : (M.faceNodes t j).card = 3 := by
  simp [faceNodes]

theorem mem_cellNodes (M : MeshData n m) (t : Fin m) (a : Fin n) :
    a ∈ M.cellNodes t ↔ ∃ i, M.vertex t i = a := by simp [cellNodes]

theorem mem_faceNodes (M : MeshData n m) (t : Fin m) (j : Fin 4) (a : Fin n) :
    a ∈ M.faceNodes t j ↔ ∃ i, i ≠ j ∧ M.vertex t i = a := by
  constructor
  · intro h
    obtain ⟨i, hi, hv⟩ := Finset.mem_map.mp h
    exact ⟨i, (Finset.mem_erase.mp hi).1, hv⟩
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_map.mpr ⟨i, by simp [hi], rfl⟩

theorem faceNodes_injective (M : MeshData n m) (t : Fin m) : Function.Injective (M.faceNodes t) := by
  intro i j hij
  by_contra hne
  have hv : M.vertex t i ∈ M.faceNodes t j := (M.mem_faceNodes t j _).mpr ⟨i, hne, rfl⟩
  rw [← hij] at hv
  obtain ⟨k, hk, hki⟩ := (M.mem_faceNodes t i _).mp hv
  exact hk ((M.vertex t).injective hki)

theorem faceNodes_subset (M : MeshData n m) (t : Fin m) (j : Fin 4) :
    M.faceNodes t j ⊆ M.cellNodes t := by
  intro a ha
  obtain ⟨i, _, hi⟩ := (M.mem_faceNodes t j a).mp ha
  exact (M.mem_cellNodes t a).mpr ⟨i, hi⟩

theorem faceNodes_eq_erase (M : MeshData n m) (t : Fin m) (j : Fin 4) :
    M.faceNodes t j = (M.cellNodes t).erase (M.vertex t j) := by
  ext a
  simp only [M.mem_faceNodes, Finset.mem_erase, M.mem_cellNodes]
  constructor
  · rintro ⟨i, hij, rfl⟩
    exact ⟨fun h => hij ((M.vertex t).injective h), i, rfl⟩
  · rintro ⟨hne, i, rfl⟩
    exact ⟨i, fun h => hne (congrArg (M.vertex t) h), rfl⟩

theorem faceNodes_succAbove (M : MeshData n m) (t : Fin m) (j : Fin 4) :
    M.faceNodes t j = Finset.univ.map ((Fin.succAboveEmb j).trans (M.vertex t)) := by
  ext a
  simp only [M.mem_faceNodes, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
    Fin.succAboveEmb_apply]
  constructor
  · rintro ⟨i, hij, hi⟩
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    exact ⟨k, by simpa [hk] using hi⟩
  · rintro ⟨k, hk⟩
    exact ⟨j.succAbove k, Fin.succAbove_ne j k, hk⟩

theorem own_opposite_negative (M : MeshData n m) (a : M.Occurrence) :
    dot (M.faceArea a) (M.position (M.oppositeNode a) - M.position (M.baseNode a)) < 0 := by
  have hb : M.position (M.baseNode a) = faceBase (M.points a.1) a.2 := by
    unfold baseNode points faceBase
    generalize a.2 = i
    fin_cases i <;> rfl
  rw [hb]
  change dot (faceVector (M.points a.1) a.2) (M.points a.1 a.2 - faceBase (M.points a.1) a.2) < 0
  rw [faceVector_opposite_dot]
  have hp := M.positive a.1
  change 0 < sixVolume (M.points a.1) at hp
  linarith

theorem baseNode_mem (M : MeshData n m) (a : M.Occurrence) : M.baseNode a ∈ M.faceID a := by
  exact (M.mem_faceNodes a.1 a.2 _).mpr ⟨a.2.succAbove 0, Fin.succAbove_ne _ _, rfl⟩

theorem tangent_at_face_node (M : MeshData n m) (a : M.Occurrence) (v : Fin n) (hv : v ∈ M.faceID a) :
    dot (M.faceArea a) (M.position v - M.position (M.baseNode a)) = 0 := by
  obtain ⟨i, hi, rfl⟩ := (M.mem_faceNodes a.1 a.2 v).mp hv
  have hb : M.position (M.baseNode a) = faceBase (M.points a.1) a.2 := by
    unfold baseNode points faceBase
    generalize a.2 = i
    fin_cases i <;> rfl
  rw [hb]
  exact faceVector_tangent (M.points a.1) a.2 i (fun he => hi (Fin.ext he).symm)

theorem face_membership (M : MeshData n m) (t : Fin m) (F : Finset (Fin n)) (hc : F.card = 3) :
    F ⊆ M.cellNodes t ↔ ∃ j, M.faceNodes t j = F := by
  constructor
  · intro hsub
    have hex : ∃ a ∈ M.cellNodes t, a ∉ F := by
      by_contra! h
      have hh := Finset.card_le_card h
      rw [M.cellNodes_card, hc] at hh
      omega
    obtain ⟨a, ha, hnot⟩ := hex
    obtain ⟨j, rfl⟩ := (M.mem_cellNodes t a).mp ha
    refine ⟨j, ?_⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · rw [M.faceNodes_eq_erase]
      intro a ha
      exact Finset.mem_erase.mpr ⟨fun he => hnot (he ▸ ha), hsub ha⟩
    · rw [M.faceNodes_card, hc]
  · rintro ⟨j, rfl⟩
    exact M.faceNodes_subset t j

theorem faceCount_le_cells (M : MeshData n m) (F : Finset (Fin n)) : M.faceCount F ≤ m := by
  have hi : Set.InjOn (fun a : M.Occurrence => a.1) (M.faceOccurrences F : Set M.Occurrence) := by
    intro a ha b hb hab
    apply Prod.ext hab
    apply M.faceNodes_injective b.1
    have hfa : M.faceNodes a.1 a.2 = F := (Finset.mem_filter.mp ha).2
    have hfb : M.faceNodes b.1 b.2 = F := (Finset.mem_filter.mp hb).2
    simpa only [hab] using hfa.trans hfb.symm
  calc
    M.faceCount F = ((M.faceOccurrences F).image (fun a => a.1)).card :=
      (Finset.card_image_of_injOn hi).symm
    _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = m := by simp

theorem faceNodes_triple (M : MeshData n m) (a : M.Occurrence) :
    M.faceID a = {M.vertex a.1 (a.2.succAbove 0), M.vertex a.1 (a.2.succAbove 1),
      M.vertex a.1 (a.2.succAbove 2)} := by
  change M.faceNodes a.1 a.2 = _
  rw [M.faceNodes_succAbove]
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [hu]
  simp

theorem triangle_same_nodes (x : Fin n → Vector 3) (a b c d e f : Fin n)
    (hs : ({d, e, f} : Finset (Fin n)) = {a, b, c})
    (hd : d ≠ e ∧ d ≠ f ∧ e ≠ f) :
    triangle (x d) (x e) (x f) = triangle (x a) (x b) (x c) ∨
      triangle (x d) (x e) (x f) = -triangle (x a) (x b) (x c) := by
  have hD : d = a ∨ d = b ∨ d = c := by
    have hh : d ∈ ({a, b, c} : Finset (Fin n)) := hs ▸ (by simp)
    simpa using hh
  have hE : e = a ∨ e = b ∨ e = c := by
    have hh : e ∈ ({a, b, c} : Finset (Fin n)) := hs ▸ (by simp)
    simpa using hh
  have hF : f = a ∨ f = b ∨ f = c := by
    have hh : f ∈ ({a, b, c} : Finset (Fin n)) := hs ▸ (by simp)
    simpa using hh
  rcases hD with rfl | rfl | rfl <;> rcases hE with rfl | rfl | rfl <;> rcases hF with rfl | rfl | rfl
  all_goals simp_all
  all_goals
    first
    | left
      ext q
      fin_cases q
      all_goals simp [triangle, cross]
      all_goals ring1
    | right
      ext q
      fin_cases q
      all_goals simp [triangle, cross]
      all_goals ring1

theorem eq_or_neg_trans {a b c : Vector 3} (hab : a = b ∨ a = -b) (hbc : b = c ∨ b = -c) :
    a = c ∨ a = -c := by
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc <;> simp_all

theorem eq_or_neg_symm {a b : Vector 3} (h : a = b ∨ a = -b) : b = a ∨ b = -a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [h, neg_neg]

theorem faceArea_eq_or_neg (M : MeshData n m) (a b : M.Occurrence) (hf : M.faceID a = M.faceID b) :
    M.faceArea b = M.faceArea a ∨ M.faceArea b = -M.faceArea a := by
  let va : Fin 3 → Fin n := fun k => M.vertex a.1 (a.2.succAbove k)
  let vb : Fin 3 → Fin n := fun k => M.vertex b.1 (b.2.succAbove k)
  have hi : Function.Injective vb := (M.vertex b.1).injective.comp Fin.succAbove_right_injective
  have hd : vb 0 ≠ vb 1 ∧ vb 0 ≠ vb 2 ∧ vb 1 ≠ vb 2 :=
    ⟨fun h => (by decide : (0 : Fin 3) ≠ 1) (hi h),
     fun h => (by decide : (0 : Fin 3) ≠ 2) (hi h),
     fun h => (by decide : (1 : Fin 3) ≠ 2) (hi h)⟩
  have hs : ({vb 0, vb 1, vb 2} : Finset (Fin n)) = {va 0, va 1, va 2} := by
    simpa only [va, vb, M.faceNodes_triple] using hf.symm
  have ht := triangle_same_nodes M.position (va 0) (va 1) (va 2) (vb 0) (vb 1) (vb 2) hs hd
  have ha := faceVector_triangle_or_neg (M.points a.1) a.2
  have hb := faceVector_triangle_or_neg (M.points b.1) b.2
  exact eq_or_neg_trans hb (eq_or_neg_trans ht (eq_or_neg_symm ha))

theorem faceArea_cancel_of_side (M : MeshData n m) (a b : M.Occurrence)
    (hf : M.faceID a = M.faceID b)
    (hs : 0 < dot (M.faceArea a) (M.position (M.oppositeNode b) - M.position (M.baseNode a))) :
    M.faceArea b = -M.faceArea a := by
  rcases M.faceArea_eq_or_neg a b hf with he | he
  · have hb := M.own_opposite_negative b
    rw [he] at hb
    have ht := M.tangent_at_face_node a (M.baseNode b) (by rw [hf]; exact M.baseNode_mem b)
    have hdot : dot (M.faceArea a) (M.position (M.oppositeNode b) - M.position (M.baseNode a)) =
        dot (M.faceArea a) (M.position (M.oppositeNode b) - M.position (M.baseNode b)) := by
      calc
        _ = dot (M.faceArea a) (M.position (M.oppositeNode b) - M.position (M.baseNode b)) +
            dot (M.faceArea a) (M.position (M.baseNode b) - M.position (M.baseNode a)) := by
              simp [dot_three]
              ring
        _ = _ := by rw [ht]; ring
    rw [hdot] at hs
    linarith
  · exact he

theorem faceArea_cancel (M : MeshData n m) (h : M.Conforming) (a b : M.Occurrence)
    (hne : a ≠ b) (hf : M.faceID a = M.faceID b) : M.faceArea b = -M.faceArea a :=
  M.faceArea_cancel_of_side a b hf (h.oppositeSides a b hne hf)

end MeshData
end CFDLean.MedianDual
