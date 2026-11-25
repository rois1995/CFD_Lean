import CFDLean.Papers.JST1.Spec.Item11b
import CFDLean.Papers.JST1.Proofs.Geom3
import CFDLean.Geometry.Simplex
import CFDLean.Geometry.MeshBoundary

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

/-- Closed computation on the pulling splits, checked by the kernel. -/
theorem p3_11_5 : Spec.P3_11_5 := by
  unfold Spec.P3_11_5
  decide +kernel

/-- Closed computation on the pulling splits, checked by the kernel. -/
theorem p3_11_6 : Spec.P3_11_6 := by
  unfold Spec.P3_11_6
  decide +kernel

end CFDLean.JST1.Proofs
