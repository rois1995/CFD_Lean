import CFDLean.Geometry.MedianDual
import Mathlib.Analysis.Convex.Combination

noncomputable section
namespace CFDLean.MedianDual.Controls
open Coordinates MeshData
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

 theorem points_injective (p : Points) (h : sixVolume p ≠ 0) : Function.Injective p := by
  intro i j hij
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases j with rfl | rfl | rfl | rfl
  all_goals first | rfl | (exfalso; apply h; simp [sixVolume, determinant, cross, dot_three, hij] <;> ring)

 def oneCell (p : Points) (hp : 0 < sixVolume p) : MeshData 4 1 where
  position := p
  vertex _ := Function.Embedding.refl _
  positive _ := hp

 theorem oneCell_conforming (p : Points) (hp : 0 < sixVolume p) : (oneCell p hp).Conforming := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b _; exact Subsingleton.elim a b
  · intro a b _ _ hab
    exact points_injective p (ne_of_gt hp) hab
  · intro a b hab
    exact False.elim (hab (Subsingleton.elim a b))
  · intro F
    exact le_trans ((oneCell p hp).faceCount_le_cells F) (by norm_num)
  · intro a b hab hf
    have ht : a.1 = b.1 := Subsingleton.elim _ _
    have hj : a.2 = b.2 := (oneCell p hp).faceNodes_injective a.1 (by simpa [faceID, ht] using hf)
    exact False.elim (hab (Prod.ext ht hj))

 def standardPoints : Points := ![![0,0,0], ![1,0,0], ![0,1,0], ![0,0,1]]
 theorem standard_positive : 0 < sixVolume standardPoints := by norm_num [sixVolume, standardPoints, determinant, cross, dot_three]
 def standard : MeshData 4 1 := oneCell standardPoints standard_positive
 theorem standard_conforming : standard.Conforming := oneCell_conforming _ _

 def obliquePoints : Points := ![![2,-1,1], ![4,0,1], ![3,2,2], ![2,1,4]]
 theorem oblique_positive : 0 < sixVolume obliquePoints := by norm_num [sixVolume, obliquePoints, determinant, cross, dot_three]
 def oblique : MeshData 4 1 := oneCell obliquePoints oblique_positive
 theorem oblique_conforming : oblique.Conforming := oneCell_conforming _ _

 theorem standard_volume (a : Fin 4) : standard.dualVolume a = 1/24 := by
  rw [dualVolume_formula]
  norm_num [standard, oneCell, cellNodes, points, volume, standardPoints, sixVolume, determinant, cross, dot_three]

 theorem standard_local_area : localInterface standardPoints 0 1 = ![1/12,1/24,1/24] := by
  rw [localInterface_eq]
  ext q
  fin_cases q <;> norm_num [faceVector, standardPoints, triangle, cross]

 theorem standard_assembled_area : standard.assembledArea 0 1 = ![1/12,1/24,1/24] := by
  ext q
  fin_cases q <;> norm_num [assembledArea, Fin.sum_univ_one, Fin.sum_univ_four, standard, oneCell, points,
    localInterface_eq, faceVector, standardPoints, triangle, cross]
  all_goals simp +decide

 theorem standard_closed (a : Fin 4) :
    Assembly.metricDefect standard.interfaces standard.edgeArea standard.boundaryArea a = 0 :=
  standard.metric_closed standard_conforming a

 theorem oblique_closed (a : Fin 4) :
    Assembly.metricDefect oblique.interfaces oblique.edgeArea oblique.boundaryArea a = 0 :=
  oblique.metric_closed oblique_conforming a

 theorem standard_flags (i j k l : Fin 4) (h : valid i j k l) :
    volume (flagPoints standardPoints i j k l) = 1/144 := by
  rw [flag_volume _ _ _ _ _ h]
  norm_num [volume, sixVolume, standardPoints, determinant, cross, dot_three]

 theorem oblique_flags (i j k l : Fin 4) (h : valid i j k l) :
    volume (flagPoints obliquePoints i j k l) = volume obliquePoints / 24 := flag_volume _ _ _ _ _ h

 theorem unused_volume {n m : ℕ} (M : MeshData n m) (a : Fin n) (h : ¬ M.Used a) : M.dualVolume a = 0 :=
  M.dualVolume_unused a h

 theorem degenerate_excluded : ¬ (0 < sixVolume (fun _ : Fin 4 => (0 : Vector 3))) := by
  norm_num [sixVolume, determinant, cross, dot_three]

 theorem nonmanifold_excluded {n m : ℕ} (M : MeshData n m) (F : Finset (Fin n))
    (h : 3 ≤ M.faceCount F) : ¬ M.Conforming := by
  intro hc
  have := hc.faceMultiplicity F
  omega

/-- A one-patch incompatible boundary perturbation survives in the actual Roe residual. -/
theorem boundary_perturbation {n m : ℕ} (M : MeshData n m) (h : M.Conforming)
    (γ : ℝ) (U : Conservative 3) (b₀ : M.Boundary) (δ : StateCoordinates) :
    Assembly.residual M.interfaces (Assembly.roeTransfer M.interfaces γ (fun _ => U) M.edgeArea)
      (fun b => Assembly.physicalTransfer γ U (M.boundaryArea b) + if b = b₀ then δ else 0)
      b₀.1.2 = δ := by
  classical
  have hc := M.constant_state h γ U b₀.1.2
  have hb : (∑ b : M.Boundary, if b.1.2 = b₀.1.2 then
      Assembly.physicalTransfer γ U (M.boundaryArea b) + (if b = b₀ then δ else 0) else 0) =
      (∑ b : M.Boundary, if b.1.2 = b₀.1.2 then Assembly.physicalTransfer γ U (M.boundaryArea b) else 0) + δ := by
    have hs (b : M.Boundary) : (if b.1.2 = b₀.1.2 then
        Assembly.physicalTransfer γ U (M.boundaryArea b) + (if b = b₀ then δ else 0) else 0) =
        (if b.1.2 = b₀.1.2 then Assembly.physicalTransfer γ U (M.boundaryArea b) else 0) +
        (if b = b₀ then δ else 0) := by
      by_cases hh : b = b₀
      · subst b; simp
      · simp [hh]
    simp_rw [hs, Finset.sum_add_distrib]
    simp
  change (∑ e, Assembly.incidence M.interfaces b₀.1.2 e •
      Assembly.roeTransfer M.interfaces γ (fun _ => U) M.edgeArea e) +
      (∑ b : M.Boundary, if b.1.2 = b₀.1.2 then
        Assembly.physicalTransfer γ U (M.boundaryArea b) + (if b = b₀ then δ else 0) else 0) = δ
  rw [hb]
  change (∑ e, Assembly.incidence M.interfaces b₀.1.2 e •
      Assembly.roeTransfer M.interfaces γ (fun _ => U) M.edgeArea e) +
      (∑ b : M.Boundary, if b.1.2 = b₀.1.2 then Assembly.physicalTransfer γ U (M.boundaryArea b) else 0) = 0 at hc
  rw [← add_assoc, hc, zero_add]

def standardBoundary : standard.Boundary := ⟨((0,3),0), by decide⟩
def resting : Conservative 3 := ⟨1,![0,0,0],1⟩

theorem resting_admissible : resting.Admissible 2 := by
  norm_num [resting, Conservative.Admissible, Conservative.pressure, squareSum_three]

theorem compatible_standard (a : Fin 4) :
    Assembly.residual standard.interfaces (Assembly.roeTransfer standard.interfaces 2 (fun _ => resting) standard.edgeArea)
      (fun b => Assembly.physicalTransfer 2 resting (standard.boundaryArea b)) a = 0 :=
  standard.constant_state standard_conforming 2 resting a

theorem incompatible_standard :
    Assembly.residual standard.interfaces (Assembly.roeTransfer standard.interfaces 2 (fun _ => resting) standard.edgeArea)
      (fun b => Assembly.physicalTransfer 2 resting (standard.boundaryArea b) +
        if b = standardBoundary then (![1,0,0,0,0] : StateCoordinates) else 0) 0 ≠ 0 := by
  have he := boundary_perturbation standard standard_conforming 2 resting standardBoundary (![1,0,0,0,0] : StateCoordinates)
  intro h
  have hh := congrFun (he.symm.trans h) 0
  norm_num at hh

end CFDLean.MedianDual.Controls
