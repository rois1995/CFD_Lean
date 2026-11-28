import CFDLean.Discrete.FixedMesh
import ReviewCases.OrientedTriangles

/-! The frozen rational triangle data evaluated through the generic real-valued assembly. -/
namespace ReviewCases.FixedMeshAssembly
open CFDLean FixedMesh OrientedTriangles

private def mesh : Assembly.Interfaces Bool Unit (Fin 4) where
  tail _ := false
  head _ := true
  distinct _ := by decide
  owner := ![false, false, true, true]

private def a : Point := (0,0)
private def b : Point := (2,0)
private def c : Point := (2,1)
private def d : Point := (0,2)
private def edges : Fin 4 → Point × Point := ![(a,b), (b,c), (c,d), (d,a)]
private def mean (i : Bool) : ℚ := if i then 5 else 2

private def transfer (p q : Point) (l r : ℚ) : ℚ :=
  let n := areaVector p q
  upwind (n.1 + 2 * n.2) l r

private def F (f : Unit) : ℝ := transfer c a (mean (mesh.tail f)) (mean (mesh.head f))
private def G (e : Fin 4) : ℝ := transfer (edges e).1 (edges e).2 (mean (mesh.owner e)) 1
private def volume (i : Bool) : ℝ := if i then (area a c d : ℝ) else (area a b c : ℝ)

private theorem values : F () = 6 ∧ ∀ e, G e = ![-4,2,25,-2] e := by
  constructor
  · norm_num [F, mesh, mean, transfer, upwind, areaVector, a, c]
  · intro e
    fin_cases e <;> norm_num [G, edges, mesh, mean, transfer, upwind, areaVector, a, b, c, d]

theorem cell_residuals : FixedMesh.residual mesh F G false = 4 ∧ FixedMesh.residual mesh F G true = 17 := by
  norm_num [FixedMesh.residual, FixedMesh.interior, values.1, values.2, mesh, Fin.sum_univ_four]

theorem unequal_volume_update :
    FixedMesh.step volume (1/8) (fun i => (mean i : ℝ)) (FixedMesh.residual mesh F G) false = 3/2 ∧
    FixedMesh.step volume (1/8) (fun i => (mean i : ℝ)) (FixedMesh.residual mesh F G) true = 63/16 := by
  norm_num [FixedMesh.step, cell_residuals.1, cell_residuals.2, volume, area, mean, a, b, c, d]

end ReviewCases.FixedMeshAssembly
