import CFDLean.Papers.JST1.Proofs.Item6
import CFDLean.Papers.JST1.Spec.Item11a
import CFDLean.Geometry.MeshBoundary

/-! Proofs of item 11, stage 1 (P3): `lem:avg` closure from facet balance and the face balance of the pulling
splits. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs

theorem p3_11_1 : Spec.P3_11_1 := CFDLean.Num.WMesh.facetBalanced_boundary

/-- Closed computation on the reference cells, checked by the kernel. -/
theorem p3_11_3 : Spec.P3_11_3 := by
  unfold Spec.P3_11_3
  decide

end CFDLean.JST1.Proofs
