import CFDLean.Geometry.MedianDual.Controls

noncomputable section
namespace CFDLean.MedianDual.Controls
open Coordinates MeshData
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

def twoPosition : Fin 5 → Vector 3 := ![![0,0,0],![1,0,0],![0,1,0],![0,0,1],![0,0,-1]]
def upperVertex : Fin 4 ↪ Fin 5 := ⟨fun i => ![0,1,2,3] i, by decide⟩
def lowerVertex : Fin 4 ↪ Fin 5 := ⟨fun i => ![0,2,1,4] i, by decide⟩
def twoVertex (t : Fin 2) : Fin 4 ↪ Fin 5 := if t = 0 then upperVertex else lowerVertex

def twoCells : MeshData 5 2 where
  position := twoPosition
  vertex := twoVertex
  positive t := by fin_cases t <;> norm_num [twoVertex, upperVertex, lowerVertex, twoPosition, sixVolume, determinant, cross, dot_three]

def sharedNodes : Finset (Fin 5) := {0,1,2}

theorem two_shared : twoCells.cellNodes 0 ∩ twoCells.cellNodes 1 = sharedNodes := by decide

def upperRegion : Set (Vector 3) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ x 0 + x 1 + x 2 ≤ 1}

theorem upperRegion_convex : Convex ℝ upperRegion := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x 0 + b * y 0 ∧ 0 ≤ a * x 1 + b * y 1 ∧
    0 ≤ a * x 2 + b * y 2 ∧ (a*x 0+b*y 0)+(a*x 1+b*y 1)+(a*x 2+b*y 2) ≤ 1
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1),
    add_nonneg (mul_nonneg ha hx.2.2.1) (mul_nonneg hb hy.2.2.1), ?_⟩
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.2.2), mul_nonneg hb (sub_nonneg.mpr hy.2.2.2)]

theorem upper_hull_bounds : convexHull ℝ (Set.range (twoCells.points 0)) ⊆ upperRegion := by
  apply convexHull_min _ upperRegion_convex
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> norm_num [upperRegion, points, twoCells, twoVertex, upperVertex, twoPosition]

theorem lower_hull_bound : convexHull ℝ (Set.range (twoCells.points 1)) ⊆ {x | x 2 ≤ 0} := by
  apply convexHull_min
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> norm_num [points, twoCells, twoVertex, lowerVertex, twoPosition]
  · intro x hx y hy a b ha hb _
    change a * x 2 + b * y 2 ≤ 0
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx) (mul_nonpos_of_nonneg_of_nonpos hb hy)

theorem shared_triangle (x : Vector 3) (hx : upperRegion x) (hz : x 2 = 0) :
    x ∈ convexHull ℝ (twoCells.position '' (sharedNodes : Set (Fin 5))) := by
  refine mem_convexHull_of_exists_fintype
    (![1-x 0-x 1,x 0,x 1] : Fin 3 → ℝ) (![![0,0,0],![1,0,0],![0,1,0]] : Fin 3 → Vector 3) ?_ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    · change 0 ≤ 1 - x 0 - x 1
      have := hx.2.2.2; linarith
    · exact hx.1
    · exact hx.2.1
  · simp [Fin.sum_univ_three]; ring
  · intro i
    fin_cases i
    · exact ⟨0, by simp [sharedNodes], rfl⟩
    · exact ⟨1, by simp [sharedNodes], rfl⟩
    · exact ⟨2, by simp [sharedNodes], rfl⟩
  · ext i
    fin_cases i <;> simp [Fin.sum_univ_three, hz]

theorem two_hull_intersection :
    convexHull ℝ (Set.range (twoCells.points 0)) ∩ convexHull ℝ (Set.range (twoCells.points 1)) =
      convexHull ℝ (twoCells.position '' (sharedNodes : Set (Fin 5))) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hu := upper_hull_bounds hx.1
    have hl := lower_hull_bound hx.2
    exact shared_triangle x hu (le_antisymm hl hu.2.2.1)
  · apply Set.subset_inter
    · apply convexHull_mono
      rintro _ ⟨i, hi, rfl⟩
      simp only [sharedNodes, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    · apply convexHull_mono
      rintro _ ⟨i, hi, rfl⟩
      simp only [sharedNodes, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨2,rfl⟩
      · exact ⟨1,rfl⟩

theorem two_cells_conforming : twoCells.Conforming := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro a b _ _ hab
    have hp : Function.Injective twoPosition := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> first | rfl | (have h0 := congrFun hab 0; have h1 := congrFun hab 1; have h2 := congrFun hab 2; norm_num [twoPosition] at h0 h1 h2)
    exact hp hab
  · intro t u htu
    fin_cases t <;> fin_cases u
    · exact False.elim (htu rfl)
    · change convexHull ℝ (Set.range (twoCells.points 0)) ∩ convexHull ℝ (Set.range (twoCells.points 1)) = _
      simpa only [two_shared] using two_hull_intersection
    · change convexHull ℝ (Set.range (twoCells.points 1)) ∩ convexHull ℝ (Set.range (twoCells.points 0)) = _
      rw [Set.inter_comm, Finset.inter_comm]
      simpa only [two_shared] using two_hull_intersection
    · exact False.elim (htu rfl)
  · intro F
    exact twoCells.faceCount_le_cells F
  · intro a b hab hf
    rcases a with ⟨t,i⟩
    rcases b with ⟨u,j⟩
    fin_cases t <;> fin_cases u <;> fin_cases i <;> fin_cases j
    all_goals first
      | exact False.elim (hab rfl)
      | (exfalso; exact (by decide : ¬ twoCells.faceID _ = twoCells.faceID _) hf)
      | norm_num [faceArea, points, faceVector, triangle, cross, dot_three, oppositeNode, baseNode, twoCells, twoVertex, upperVertex, lowerVertex, twoPosition]

theorem two_cells_closed (a : Fin 5) :
    Assembly.metricDefect twoCells.interfaces twoCells.edgeArea twoCells.boundaryArea a = 0 :=
  twoCells.metric_closed two_cells_conforming a

theorem two_cells_volume (a : Fin 5) : twoCells.dualVolume a = if a.val < 3 then 1/12 else 1/24 := by
  rw [dualVolume_formula]
  fin_cases a <;> norm_num [Fin.exists_fin_succ, Fin.sum_univ_two, cellNodes, volume, points, twoCells, twoVertex, upperVertex, lowerVertex, twoPosition, sixVolume, determinant, cross, dot_three]
  all_goals simp +decide <;> norm_num

theorem two_cells_total_volume : (∑ a, twoCells.dualVolume a) = 1/3 := by
  rw [volume_partition_raw]
  norm_num [Fin.sum_univ_two, volume, points, twoCells, twoVertex, upperVertex, lowerVertex, twoPosition, sixVolume, determinant, cross, dot_three]

theorem two_cells_assembled_area : twoCells.assembledArea 0 1 = ![1/6,1/12,0] := by
  simp +decide only [assembledArea, Fin.sum_univ_two, Fin.sum_univ_four, twoCells, twoVertex,
    upperVertex, lowerVertex, Function.Embedding.coeFn_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, ite_true, ite_false, zero_add, add_zero]
  ext q
  fin_cases q <;> norm_num [points, twoCells, twoVertex, upperVertex, lowerVertex, twoPosition,
    localInterface_eq, faceVector, triangle, cross]

theorem shared_patches_cancel (i : Fin 5) :
    twoCells.ownedPatch (0,3) i + twoCells.ownedPatch (1,3) i = 0 := by
  have hf : twoCells.faceID (0,3) = twoCells.faceID (1,3) := by decide
  have hc := twoCells.faceArea_cancel two_cells_conforming (0,3) (1,3) (by decide) hf
  simp only [ownedPatch, ← hf, hc]
  split_ifs <;> module

end CFDLean.MedianDual.Controls
