import CFDLean.Papers.JST1.Proofs.GeomBase
import CFDLean.Geometry.MeshBoundary
import CFDLean.Geometry.MedianDualBridge

/-! P1-5.0a/b: a facet pairing at a vertex makes it closed (`B i k = 0` for all `k`); on a conforming CFD_Lean
tetrahedral mesh the pairing exists at every vertex lying on no boundary face. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

theorem p1_5_0a : Spec.P1_5_0a := CFDLean.Num.WMesh.closed_of_facetPaired

namespace Closure
open CFDLean.MedianDual

/-! ### d = 3: CFD_Lean tetrahedral meshes -/

theorem det_edgeMat (p : Points) : (simplexOfPoints p).edgeMat.det = sixVolume p := by
  rw [Matrix.det_fin_three]
  simp [Simplex.edgeMat, simplexOfPoints, sixVolume, determinant, cross, CFDLean.Coordinates.dot_three]
  ring

theorem nondeg_of_pos (p : Points) (hp : 0 < sixVolume p) : (simplexOfPoints p).Nondeg := by
  unfold Simplex.Nondeg
  rw [det_edgeMat]
  exact hp.ne'

theorem ofMeshData_valid {n m : ℕ} (M : MeshData n m) : (ofMeshData M).Valid :=
  ⟨fun _ => zero_le_one, fun t => nondeg_of_pos (M.points t) (M.positive t)⟩

end Closure

theorem p1_5_0b : Spec.P1_5_0b := CFDLean.Num.ofMeshData_closed

end CFDLean.JST1.Proofs
