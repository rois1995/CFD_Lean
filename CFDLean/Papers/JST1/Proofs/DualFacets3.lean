import CFDLean.Papers.JST1.Proofs.Closure
import CFDLean.Papers.JST1.Proofs.DualFacets
import CFDLean.Geometry.MedianDualBridge

noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

theorem p1_5_6 : Spec.P1_5_6 := CFDLean.Num.dualFacets_grad

theorem p1_5_7 : Spec.P1_5_7 := CFDLean.Num.ofMeshData_fv_galerkin

end CFDLean.JST1.Proofs
