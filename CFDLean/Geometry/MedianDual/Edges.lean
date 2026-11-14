import CFDLean.Geometry.MedianDual.Mesh

noncomputable section
namespace CFDLean.MedianDual.MeshData
open Coordinates
open scoped BigOperators
variable {n m : ℕ}

theorem index_indicator {A : Type*} [AddCommMonoid A] (M : MeshData n m) (t : Fin m)
    (s : Finset (Fin 4)) (a : Fin n) (x : A) :
    (∑ i ∈ s, if M.vertex t i = a then x else 0) = if a ∈ s.map (M.vertex t) then x else 0 := by
  rw [← Finset.sum_map s (M.vertex t) (fun b => if b = a then x else 0)]
  simp

/-- A primal edge is a pair of distinct used node identities in increasing order. -/
def IsEdge (M : MeshData n m) (a b : Fin n) : Prop :=
  a < b ∧ ∃ t, a ∈ M.cellNodes t ∧ b ∈ M.cellNodes t
abbrev Edge (M : MeshData n m) := {ab : Fin n × Fin n // M.IsEdge ab.1 ab.2}
instance (M : MeshData n m) : Fintype M.Edge := Fintype.ofFinite _

/-- Oriented sum of all local median-dual triangles, before any Roe evaluation. -/
def assembledArea (M : MeshData n m) (a b : Fin n) : Vector 3 :=
  ∑ t, ∑ i, ∑ j, if M.vertex t i = a ∧ M.vertex t j = b then localInterface (M.points t) i j else 0

def edgeArea (M : MeshData n m) (e : M.Edge) : Vector 3 := M.assembledArea e.1.1 e.1.2

theorem assembledArea_reverse (M : MeshData n m) (a b : Fin n) :
    M.assembledArea b a = -M.assembledArea a b := by
  unfold assembledArea
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : M.vertex t i = a ∧ M.vertex t j = b
  · rw [if_pos ⟨h.2, h.1⟩, if_pos h]
    exact localInterface_reverse _ _ _
  · have h' : ¬(M.vertex t j = b ∧ M.vertex t i = a) := fun hh => h hh.symm
    simp [h, h']

theorem assembledArea_self (M : MeshData n m) (a : Fin n) : M.assembledArea a a = 0 := by
  unfold assembledArea
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with h
  · have hij := (M.vertex t).injective (h.1.trans h.2.symm)
    subst j
    exact localInterface_self _ _
  · rfl

theorem assembledArea_support (M : MeshData n m) (a b : Fin n)
    (h : ¬∃ t, a ∈ M.cellNodes t ∧ b ∈ M.cellNodes t) : M.assembledArea a b = 0 := by
  unfold assembledArea
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact h ⟨t, (M.mem_cellNodes t _).mpr ⟨i, rfl⟩, (M.mem_cellNodes t _).mpr ⟨j, rfl⟩⟩

theorem assembledArea_row (M : MeshData n m) (a : Fin n) :
    (∑ b, M.assembledArea a b) =
      ∑ t, ∑ i, if M.vertex t i = a then ∑ j, localInterface (M.points t) i j else 0 := by
  unfold assembledArea
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  by_cases h : M.vertex t i = a
  · simp [h]
  · simp [h]

/-- Exact compression of an antisymmetric supported row into one record per unordered edge. -/
theorem edge_incidence_sum (M : MeshData n m) (a : Fin n) :
    (∑ e : M.Edge, ((if e.1.1 = a then (1 : ℝ) else 0) -
      (if e.1.2 = a then 1 else 0)) • M.edgeArea e) = ∑ b, M.assembledArea a b := by
  classical
  let f : Fin n × Fin n → Vector 3 := fun ab =>
    ((if ab.1 = a then (1 : ℝ) else 0) - (if ab.2 = a then 1 else 0)) • M.assembledArea ab.1 ab.2
  change (∑ e : M.Edge, f e.1) = _
  rw [← Finset.sum_subtype (F := inferInstance) (p := fun ab : Fin n × Fin n => M.IsEdge ab.1 ab.2)
    (Finset.univ.filter (fun ab => M.IsEdge ab.1 ab.2)) (by simp)]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have hf (i j : Fin n) : (if M.IsEdge i j then f (i,j) else 0) =
      if i < j then f (i,j) else 0 := by
    by_cases hij : i < j
    · by_cases hs : ∃ t, i ∈ M.cellNodes t ∧ j ∈ M.cellNodes t
      · simp [IsEdge, hij, hs]
      · simp [IsEdge, hij, hs, f, M.assembledArea_support i j hs]
    · simp [IsEdge, hij]
  simp_rw [hf]
  have hd (i j : Fin n) : (if i < j then f (i,j) else 0) =
      (if i = a ∧ i < j then M.assembledArea a j else 0) -
      (if j = a ∧ i < j then M.assembledArea i a else 0) := by
    dsimp [f]
    by_cases hij : i < j <;> by_cases hi : i = a <;> by_cases hj : j = a <;> simp [hij, hi, hj]
    all_goals split_ifs <;> simp_all
  simp_rw [hd, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => if i = a ∧ i < j then M.assembledArea a j else 0)]
  have hs (j : Fin n) : (∑ i, if i = a ∧ i < j then M.assembledArea a j else 0) =
      if a < j then M.assembledArea a j else 0 := by simp [ite_and]
  have ht (i : Fin n) : (∑ j, if j = a ∧ i < j then M.assembledArea i a else 0) =
      if i < a then M.assembledArea i a else 0 := by simp [ite_and]
  have hn (i : Fin n) : (if i < a then M.assembledArea i a else 0) =
      -(if i < a then M.assembledArea a i else 0) := by
    rw [M.assembledArea_reverse i a]
    split_ifs <;> simp
  simp_rw [hs, ht, hn]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rcases lt_trichotomy a b with hab | rfl | hba
  · simp [hab, not_lt_of_ge (le_of_lt hab)]
  · simp [M.assembledArea_self]
  · simp [hba, not_lt_of_ge (le_of_lt hba)]

end CFDLean.MedianDual.MeshData
