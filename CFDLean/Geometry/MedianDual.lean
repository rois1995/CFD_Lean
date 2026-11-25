import CFDLean.Geometry.MedianDual.Boundary

noncomputable section
namespace CFDLean.MedianDual.MeshData
open Coordinates
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
variable {n m : ℕ}

/-- Sum of the six actual barycentric sub-tetrahedron volumes at each incident cell vertex. -/
def dualVolume (M : MeshData n m) (a : Fin n) : ℝ :=
  ∑ t, ∑ i, if M.vertex t i = a then localDualVolume (M.points t) i else 0

theorem dualVolume_formula (M : MeshData n m) (a : Fin n) :
    M.dualVolume a = ∑ t, if a ∈ M.cellNodes t then volume (M.points t) / 4 else 0 := by
  unfold dualVolume
  simp_rw [localDualVolume_eq]
  apply Finset.sum_congr rfl
  intro t _
  simp only [cellNodes]
  exact M.index_indicator t Finset.univ a (volume (M.points t) / 4)

theorem cellVolume_pos (M : MeshData n m) (t : Fin m) : 0 < volume (M.points t) := by
  have h := M.positive t
  change 0 < sixVolume (M.points t) at h
  unfold volume
  rw [abs_of_pos h]
  positivity

theorem dualVolume_pos (M : MeshData n m) (a : Fin n) (ha : M.Used a) : 0 < M.dualVolume a := by
  rw [M.dualVolume_formula]
  obtain ⟨t, i, hi⟩ := ha
  have hm : a ∈ M.cellNodes t := (M.mem_cellNodes t a).mpr ⟨i, hi⟩
  apply Finset.sum_pos'
  · intro u _
    split_ifs
    · exact le_of_lt (div_pos (M.cellVolume_pos u) (by norm_num))
    · exact le_rfl
  · exact ⟨t, Finset.mem_univ _, by rw [ite_eq_left hm]; exact div_pos (M.cellVolume_pos t) (by norm_num)⟩

theorem dualVolume_unused (M : MeshData n m) (a : Fin n) (ha : ¬M.Used a) : M.dualVolume a = 0 := by
  rw [M.dualVolume_formula]
  apply Finset.sum_eq_zero
  intro t _
  have hm : a ∉ M.cellNodes t := by
    intro h
    obtain ⟨i, hi⟩ := (M.mem_cellNodes t a).mp h
    exact ha ⟨t, i, hi⟩
  rw [ite_eq_right hm]

theorem volume_partition_raw (M : MeshData n m) : ∑ a, M.dualVolume a = ∑ t, volume (M.points t) := by
  unfold dualVolume
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  simp only [localDualVolume_eq]
  simp
  ring

theorem volume_partition (M : MeshData n m) (_h : M.Conforming) :
    ∑ a, M.dualVolume a = ∑ t, volume (M.points t) := M.volume_partition_raw

/-- Canonical edge orientation and the exact exterior face-node patch owners. -/
def interfaces (M : MeshData n m) : Assembly.Interfaces (Fin n) M.Edge M.Boundary where
  tail e := e.1.1
  head e := e.1.2
  distinct e := ne_of_lt e.prop.1
  owner b := b.1.2

theorem all_patches_local (M : MeshData n m) (a : Fin n) :
    (∑ o : M.Occurrence, M.ownedPatch o a) =
      ∑ t, ∑ i, if M.vertex t i = a then ∑ j, localPatch (M.points t) j i else 0 := by
  simp_rw [M.ownedPatch_local]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : M.vertex t i = a <;> simp [h]

/-- Closure follows from the actual local flag-face pairings and shared primal-face cancellation. -/
theorem metric_closed (M : MeshData n m) (h : M.Conforming) (a : Fin n) :
    Assembly.metricDefect M.interfaces M.edgeArea M.boundaryArea a = 0 := by
  change (∑ e : M.Edge, ((if e.1.1 = a then (1 : ℝ) else 0) -
      (if e.1.2 = a then 1 else 0)) • M.edgeArea e) +
    (∑ b : M.Boundary, if b.1.2 = a then M.boundaryArea b else 0) = 0
  rw [M.edge_incidence_sum, M.assembledArea_row, ← M.all_patches_boundary h a, M.all_patches_local]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro t _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : M.vertex t i = a
  · simp only [ite_eq_left hi]
    exact local_closure (M.points t) i
  · simp [hi]

/-- The actual accepted Roe flux is evaluated once on each aggregated edge vector. -/
theorem roe_boundary_balance (M : MeshData n m) (γ : ℝ) (U : Fin n → Conservative 3)
    (g : M.Boundary → StateCoordinates) :
    (∑ a, Assembly.residual M.interfaces (Assembly.roeTransfer M.interfaces γ U M.edgeArea) g a) =
      ∑ b, g b := Assembly.roe_global_balance M.interfaces γ U M.edgeArea g

/-- Compatible boundary transfer on the same concrete geometry preserves every common state. -/
theorem constant_state (M : MeshData n m) (h : M.Conforming) (γ : ℝ) (U : Conservative 3) (a : Fin n) :
    Assembly.residual M.interfaces (Assembly.roeTransfer M.interfaces γ (fun _ => U) M.edgeArea)
      (fun b => Assembly.physicalTransfer γ U (M.boundaryArea b)) a = 0 :=
  Assembly.constant_state_closed M.interfaces γ U M.edgeArea M.boundaryArea a (M.metric_closed h a)

end CFDLean.MedianDual.MeshData
