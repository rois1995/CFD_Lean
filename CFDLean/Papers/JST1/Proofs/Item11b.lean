import CFDLean.Papers.JST1.Spec.Item11b
import CFDLean.Papers.JST1.Proofs.Geom3
import CFDLean.Geometry.Simplex
import CFDLean.Geometry.MeshBoundary
import CFDLean.Papers.JST1.Proofs.Chunks

/-! Proofs of item 11, stage 2 (P3): facet vectors from sorted vertex lists (3D and 2D), side balance implies facet
balance, and the pseudomanifold and face-weight computations on the pulling splits. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs

namespace Avg11b

open CFDLean.JST1.Spec Geo3

/-! ### 2D facet vectors -/

/-! ### Facet vectors of a mesh from the sorted vertex list of the facet -/

section Mesh
variable {ι C : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C]

theorem simplex_x {d : ℕ} (M : WMesh ι C d) (T : C) (e : Fin (d + 1)) :
    (M.simplex T).x e = M.pos (M.vert T e) := rfl

end Mesh
end Avg11b

open Avg11b

theorem p3_11_4 : Spec.P3_11_4 := CFDLean.Num.WMesh.facetBalanced_of_sideBalanced

theorem p3_11_4b : Spec.P3_11_4b := CFDLean.Num.WMesh.facetBalanced_of_sideBalanced2

theorem p3_11_2b : Spec.P3_11_2b := CFDLean.Num.Simplex.facet_perp2

/-! The hexahedron parts of P3-11.5 and P3-11.6 are checked in chunks (`all_of_chunks`), one declaration each. -/

section Chunked
open CFDLean.JST1.RefCell CFDLean.JST1.Spec

/-- Every face of every sub-tetrahedron of the split `s` occurs once on a cell face and twice inside. -/
def faceOK {n : ℕ} (C : Cell3 n) (s : Fin n × List Bool) : Bool :=
  (C.pull s.1 s.2).all fun t => (tetFaces t).all fun f =>
    faceCount (C.pull s.1 s.2) f == (if onCellFace C f then 1 else 2)

theorem faceOK_hex0 : ((hex.splits.drop (8 * 0)).take 8).all (faceOK hex) = true := by decide +kernel
theorem faceOK_hex1 : ((hex.splits.drop (8 * 1)).take 8).all (faceOK hex) = true := by decide +kernel
theorem faceOK_hex2 : ((hex.splits.drop (8 * 2)).take 8).all (faceOK hex) = true := by decide +kernel
theorem faceOK_hex3 : ((hex.splits.drop (8 * 3)).take 8).all (faceOK hex) = true := by decide +kernel
theorem faceOK_hex4 : ((hex.splits.drop (8 * 4)).take 8).all (faceOK hex) = true := by decide +kernel
theorem faceOK_hex5 : ((hex.splits.drop (8 * 5)).take 8).all (faceOK hex) = true := by decide +kernel
theorem faceOK_hex6 : ((hex.splits.drop (8 * 6)).take 8).all (faceOK hex) = true := by decide +kernel
theorem faceOK_hex7 : ((hex.splits.drop (8 * 7)).take 8).all (faceOK hex) = true := by decide +kernel

/-- Total weight of the face triangle `f` of a quadrilateral face of the cell. -/
def quadOK {n : ℕ} (C : Cell3 n) (q : Quad n) : Bool :=
  (q.tris false ++ q.tris true).all fun f =>
    2 * (C.splits.countP fun s => faceCount (C.pull s.1 s.2) f == 1) == C.splits.length

theorem quadOK_hex0 : ((hex.quads.drop (1 * 0)).take 1).all (quadOK hex) = true := by decide +kernel
theorem quadOK_hex1 : ((hex.quads.drop (1 * 1)).take 1).all (quadOK hex) = true := by decide +kernel
theorem quadOK_hex2 : ((hex.quads.drop (1 * 2)).take 1).all (quadOK hex) = true := by decide +kernel
theorem quadOK_hex3 : ((hex.quads.drop (1 * 3)).take 1).all (quadOK hex) = true := by decide +kernel
theorem quadOK_hex4 : ((hex.quads.drop (1 * 4)).take 1).all (quadOK hex) = true := by decide +kernel
theorem quadOK_hex5 : ((hex.quads.drop (1 * 5)).take 1).all (quadOK hex) = true := by decide +kernel

end Chunked

/-- Closed computation on the pulling splits, checked by the kernel (the hexahedron in chunks). -/
theorem p3_11_5 : Spec.P3_11_5 := by
  unfold Spec.P3_11_5
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  change RefCell.hex.splits.all (faceOK RefCell.hex) = true
  refine all_of_chunks _ _ 8 8 (by decide +kernel) fun i hi => ?_
  interval_cases i
  exacts [faceOK_hex0, faceOK_hex1, faceOK_hex2, faceOK_hex3, faceOK_hex4, faceOK_hex5, faceOK_hex6, faceOK_hex7]

/-- Closed computation on the pulling splits, checked by the kernel (the hexahedron in chunks). -/
theorem p3_11_6 : Spec.P3_11_6 := by
  unfold Spec.P3_11_6
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  change RefCell.hex.quads.all (quadOK RefCell.hex) = true
  refine all_of_chunks _ _ 1 6 (by decide +kernel) fun i hi => ?_
  interval_cases i
  exacts [quadOK_hex0, quadOK_hex1, quadOK_hex2, quadOK_hex3, quadOK_hex4, quadOK_hex5]

end CFDLean.JST1.Proofs
