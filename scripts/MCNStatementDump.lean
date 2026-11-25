import CFDLean.Num
import Lean

/-! MC-N evidence: print the types of the MC-N theorems with the settings of the JST_Paper_Lean statement dumps
(`scripts/DumpStmts.lean`: `STMT`; `scripts/DumpStmtsRaw.lean`: `XSTMT`, no notation, no coercions). Run with
`lake env lean scripts/MCNStatementDump.lean`. -/
open Lean Elab Command

set_option pp.fullNames true in
elab "#dumpmcn" : command => do
  let env ← getEnv
  for n in [`CFDLean.Num.logMean_properties,`CFDLean.Num.Simplex.calculus,`CFDLean.Num.Simplex.facet_cross3,`CFDLean.Num.Simplex.facet_perp2,`CFDLean.Num.pathSimplex_nonobtuse,`CFDLean.Num.WMesh.nW_row_sum,`CFDLean.Num.WMesh.sbp_defect,`CFDLean.Num.Simplex.median_defect_iff,`CFDLean.Num.WMesh.dissGeom_edge,`CFDLean.Num.WMesh.dissGeom_outer,`CFDLean.Num.WMesh.dissGeom_calibration,`CFDLean.Num.quadratic_edge_expansion,`CFDLean.Num.dissTensor_loewner,`CFDLean.Num.WMesh.dissTensor_trace,`CFDLean.Num.WMesh.closed_of_facetPaired,`CFDLean.Num.WMesh.conforming_boundary,`CFDLean.Num.WMesh.facetBalanced_boundary,`CFDLean.Num.WMesh.facetBalanced_of_sideBalanced,`CFDLean.Num.WMesh.facetBalanced_of_sideBalanced2,`CFDLean.Num.antisymmetric_pairFlux,`CFDLean.Num.entropyConservative_production,`CFDLean.Num.dissipativePairFlux_conservation,`CFDLean.Num.dissipativePairFlux_freeStream,`CFDLean.Num.edgeForm_boundary_split,`CFDLean.Num.WMesh.standardClosure_entropy,`CFDLean.Num.WMesh.standardClosure_linear,`CFDLean.Num.quadratureClosure_entropy,`CFDLean.Num.quadratureClosure_freeStream,`CFDLean.Num.quadratureClosure_linear,`CFDLean.Num.WMesh.faceRule_beta_B,`CFDLean.Num.WMesh.galerkin_identity,`CFDLean.Num.WMesh.fvRes_eq_galerkinRes,`CFDLean.Num.WMesh.closed_mean_galerkin,`CFDLean.Num.pair_production_integral,`CFDLean.Num.ofMeshData_closed,`CFDLean.Num.dualFacets_grad,`CFDLean.Num.ofMeshData_fv_galerkin] do
    match env.find? n with
    | some ci =>
        let fmt ← liftTermElabM <| Meta.ppExpr ci.type
        logInfo m!"STMT {n} :: {fmt}"
    | none => logInfo m!"STMT {n} :: MISSING"

set_option pp.fullNames true in
#dumpmcn

set_option pp.coercions false
set_option pp.notation false
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.funBinderTypes true
set_option format.width 1000000

elab "#dumpmcnraw" : command => do
  let env ← getEnv
  for n in [`CFDLean.Num.logMean_properties,`CFDLean.Num.Simplex.calculus,`CFDLean.Num.Simplex.facet_cross3,`CFDLean.Num.Simplex.facet_perp2,`CFDLean.Num.pathSimplex_nonobtuse,`CFDLean.Num.WMesh.nW_row_sum,`CFDLean.Num.WMesh.sbp_defect,`CFDLean.Num.Simplex.median_defect_iff,`CFDLean.Num.WMesh.dissGeom_edge,`CFDLean.Num.WMesh.dissGeom_outer,`CFDLean.Num.WMesh.dissGeom_calibration,`CFDLean.Num.quadratic_edge_expansion,`CFDLean.Num.dissTensor_loewner,`CFDLean.Num.WMesh.dissTensor_trace,`CFDLean.Num.WMesh.closed_of_facetPaired,`CFDLean.Num.WMesh.conforming_boundary,`CFDLean.Num.WMesh.facetBalanced_boundary,`CFDLean.Num.WMesh.facetBalanced_of_sideBalanced,`CFDLean.Num.WMesh.facetBalanced_of_sideBalanced2,`CFDLean.Num.antisymmetric_pairFlux,`CFDLean.Num.entropyConservative_production,`CFDLean.Num.dissipativePairFlux_conservation,`CFDLean.Num.dissipativePairFlux_freeStream,`CFDLean.Num.edgeForm_boundary_split,`CFDLean.Num.WMesh.standardClosure_entropy,`CFDLean.Num.WMesh.standardClosure_linear,`CFDLean.Num.quadratureClosure_entropy,`CFDLean.Num.quadratureClosure_freeStream,`CFDLean.Num.quadratureClosure_linear,`CFDLean.Num.WMesh.faceRule_beta_B,`CFDLean.Num.WMesh.galerkin_identity,`CFDLean.Num.WMesh.fvRes_eq_galerkinRes,`CFDLean.Num.WMesh.closed_mean_galerkin,`CFDLean.Num.pair_production_integral,`CFDLean.Num.ofMeshData_closed,`CFDLean.Num.dualFacets_grad,`CFDLean.Num.ofMeshData_fv_galerkin] do
    match env.find? n with
    | some ci =>
        let s ← liftTermElabM do return toString (← Meta.ppExpr ci.type)
        logInfo m!"XSTMT {n} :: {s}"
    | none => logInfo m!"XSTMT {n} :: MISSING"

#dumpmcnraw
