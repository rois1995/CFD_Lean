import CFDLean.Schemes.ScalarAdvection
import ReviewCases.OrientedTriangles

/-! Direct exact-real checks of the production flux on two meshes. -/
namespace ReviewCases.ScalarAdvection
open CFDLean CFDLean.ScalarAdvection

private theorem zero_speed_control : flux (![2,-1] : Vector 2) ![1,2] 3 7 = 0 := by
  apply flux_zero_speed
  norm_num [dotProduct, Fin.sum_univ_two]

namespace Triangles
open OrientedTriangles (Point area areaVector)
private def a : Point := (0,0)
private def b : Point := (2,0)
private def c : Point := (2,1)
private def d : Point := (0,2)
private def vector (p q : Point) : Vector 2 := ![(areaVector p q).1, (areaVector p q).2]
private def m : Assembly.Interfaces Bool Unit (Fin 4) where
  tail _ := false
  head _ := true
  distinct _ := by decide
  owner := ![false,false,true,true]
private def v : Vector 2 := ![1,2]
private def A (_ : Unit) := vector c a
private def T : Fin 4 → Vector 2 := ![vector a b, vector b c, vector c d, vector d a]
private def U (i : Bool) : ℝ := if i then 5 else 2
private def V (i : Bool) : ℝ := if i then (area a c d : ℝ) else (area a b c : ℝ)
private def g (_ : Fin 4) : ℝ := 1

theorem shared : interiorFlux v m A U () = 6 ∧ flux v (vector a c) (U true) (U false) = -6 := by
  norm_num [interiorFlux, flux, dotProduct, Fin.sum_univ_two, A, U, v, vector, areaVector, m, a, c]

theorem exterior (e : Fin 4) : boundaryFlux v m T U g e = ![-4,2,25,-2] e := by
  fin_cases e <;> norm_num [boundaryFlux, flux, dotProduct, Fin.sum_univ_two, m, T, U, g, v, vector, areaVector, a, b, c, d]

theorem closure (i : Bool) : FixedMesh.residual m A T i = 0 := by
  funext j
  cases i <;> fin_cases j <;> norm_num [FixedMesh.residual, FixedMesh.interior, Fin.sum_univ_four, m, A, T, vector, areaVector, a, b, c, d]

theorem constant_field (k dt : ℝ) (i : Bool) :
    FixedMesh.step V dt (fun _ => k)
      (CFDLean.ScalarAdvection.residual v m A T (fun _ => k) (fun _ => k)) i = k :=
  constant_step v m A T k dt V i (closure i)

theorem cells (i : Bool) : CFDLean.ScalarAdvection.residual v m A T U g i = if i then 17 else 4 := by
  simp only [CFDLean.ScalarAdvection.residual, FixedMesh.residual, Finset.univ_unique, Finset.sum_singleton, shared.1, exterior]
  cases i <;> norm_num [FixedMesh.interior, Fin.sum_univ_four, m]

theorem updated (i : Bool) : FixedMesh.step V (1/8) U (CFDLean.ScalarAdvection.residual v m A T U g) i =
    if i then 63/16 else 3/2 := by
  cases i <;> norm_num [FixedMesh.step, V, U, cells, area, a, b, c, d]

theorem amounts : (∑ i, V i * U i) = 12 ∧ (∑ e, boundaryFlux v m T U g e) = 21 ∧
    (∑ i, V i * FixedMesh.step V (1/8) U (CFDLean.ScalarAdvection.residual v m A T U g) i) = 75/8 := by
  norm_num [Fintype.sum_bool, Fin.sum_univ_four, updated, V, U, area, a, b, c, d, exterior]

end Triangles
namespace Patch

/-- Cells are SW, SE, NW, NE. The internal faces point east, east, north, north. -/
private def m : Assembly.Interfaces (Fin 4) (Fin 4) (Fin 4 × Bool) where
  tail := ![0,2,0,1]
  head := ![1,3,2,3]
  distinct f := by fin_cases f <;> decide
  owner := Prod.fst
private def v : Vector 2 := ![2,-1]
private def A : Fin 4 → Vector 2 := ![![1,0], ![1,0], ![0,1], ![0,1]]
/-- Each cell has an outer vertical edge and an outer horizontal edge. -/
private def T (b : Fin 4 × Bool) : Vector 2 :=
  if b.2 then ![0, (![-1,-1,1,1] : Fin 4 → ℝ) b.1] else ![(![-1,1,-1,1] : Fin 4 → ℝ) b.1, 0]
private def U : Fin 4 → ℝ := ![1,3,2,4]
private def g (_ : Fin 4 × Bool) : ℝ := 0

theorem shared (f : Fin 4) : interiorFlux v m A U f = ![2,4,-2,-4] f := by
  fin_cases f <;> norm_num [interiorFlux, m, A, U, flux, v, dotProduct, Fin.sum_univ_two]

theorem exterior (b : Fin 4 × Bool) : boundaryFlux v m T U g b =
    if b.2 then (![1,3,0,0] : Fin 4 → ℝ) b.1 else (![0,6,0,8] : Fin 4 → ℝ) b.1 := by
  rcases b with ⟨i,side⟩
  fin_cases i <;> cases side <;> norm_num [boundaryFlux, m, T, U, g, flux, v, dotProduct, Fin.sum_univ_two]

theorem boundary_cells (i : Fin 4) :
    (∑ b, if m.owner b = i then boundaryFlux v m T U g b else 0) = ![1,9,0,8] i := by
  simp only [exterior]
  fin_cases i <;> norm_num [Fintype.sum_prod_type, Fin.sum_univ_four, Fintype.sum_bool, m]

theorem closure (i : Fin 4) : FixedMesh.residual m A T i = 0 := by
  funext j
  fin_cases i <;> fin_cases j <;>
    norm_num [FixedMesh.residual, FixedMesh.interior, Fintype.sum_prod_type, Fin.sum_univ_four, Fintype.sum_bool, m, A, T]

theorem constant_field (k dt : ℝ) (i : Fin 4) :
    FixedMesh.step (fun _ => 1) dt (fun _ => k)
      (CFDLean.ScalarAdvection.residual v m A T (fun _ => k) (fun _ => k)) i = k :=
  constant_step v m A T k dt (fun _ => 1) i (closure i)

theorem cells (i : Fin 4) : CFDLean.ScalarAdvection.residual v m A T U g i = ![1,3,6,8] i := by
  unfold CFDLean.ScalarAdvection.residual FixedMesh.residual
  rw [boundary_cells]
  simp only [shared]
  fin_cases i <;> norm_num [FixedMesh.interior, Fin.sum_univ_four, m]

theorem updated (i : Fin 4) : FixedMesh.step (fun _ => 1) (1/8) U (CFDLean.ScalarAdvection.residual v m A T U g) i =
    ![7/8,21/8,5/4,3] i := by
  simp only [FixedMesh.step, cells]
  fin_cases i <;> norm_num [U]

theorem amounts : (∑ i, U i) = 10 ∧ (∑ b, boundaryFlux v m T U g b) = 18 ∧
    (∑ i, FixedMesh.step (fun _ => 1) (1/8) U (CFDLean.ScalarAdvection.residual v m A T U g) i) = 31/4 := by
  simp only [updated, exterior]
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_four, Fintype.sum_bool, U]

end Patch
end ReviewCases.ScalarAdvection
