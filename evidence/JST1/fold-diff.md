# MR-2 statement comparison: JST_Paper_Lean -> CFDLean.JST1

Inputs: `evidence/JST1/statements-v4.36.txt` and `evidence/JST1/statements-raw-v4.36.txt` (copied from JST_Paper_Lean
branch `v436`, commit `afdf4f9b4f98f089af82074bf7e4db99177844ad`, printed there by `scripts/DumpStmts.lean` and
`scripts/DumpStmtsRaw.lean`) and `evidence/JST1/statements-cfd.txt`, printed here by `lake env lean scripts/JST1Dump.lean`
with the same settings (`STMT`: value of each bound statement definition, `pp.fullNames`; `XSTMT`: additionally
`pp.notation false`, `pp.coercions false`, `pp.proofs true`, `pp.funBinderTypes true`).

Comparison rule: in the JST text rename `Paper1.Spec.X` and `Paper1.X` -> `CFDLean.Num.X` for the definitions that MC-N
moved verbatim into the core (`cross3`, `perp2`, `pathSimplex`, `facetSide`, `SideBalanced`, `stdWeight`, `facetSide2`,
`SideBalanced2`; `rot90`, `dualFacet2`, `ofMeshData`, `simplexOfPoints`), then `Paper1.` -> `CFDLean.JST1.` and
`NumCore.` -> `CFDLean.Num.`; collapse whitespace (line breaks move because the names are longer) and compare.

Result: **92 of 92 identical in the pretty dump, 92 of 92 identical in the raw dump.** No statement
differs beyond the namespace map, so no statement changed meaning.

## Source differences and why they do not change meaning

The folded files are the JST files with these mechanical edits only (statement and definition files hash-listed in
`specifications/JST1/frozen.sha256`):

1. `import Paper1.*` -> `import CFDLean.Papers.JST1.*`; `import NumCore.*` -> the core modules (`Basic`, `LogMean` ->
   `CFDLean.Foundations.*`, `Simplex` -> `CFDLean.Geometry.Simplex`, `WMesh` -> `CFDLean.Discrete.Mesh`, `Boundary`,
   `Balance` -> `CFDLean.Geometry.MeshBoundary`); `Spec/Item6.lean` also imports `CFDLean.Entropy.PairFlux` (for
   `stdWeight`), and proof files that delegate import the module of their MC-N theorem.
2. `namespace/open/end Paper1...` -> `CFDLean.JST1...`, `NumCore` -> `CFDLean.Num`, paths `Paper1/` in comments ->
   `CFDLean/Papers/JST1/`.
3. The moved definitions are deleted from `Spec/Item11a.lean` (`cross3`), `Spec/Item11b.lean` (`perp2`, `facetSide`,
   `SideBalanced`, `facetSide2`, `SideBalanced2`), `Spec/Item12.lean` (`pathSimplex`), `Spec/Item6.lean` (`stdWeight`);
   `Geometry/Dual2D.lean` and `Geometry/CFDBridge.lean` keep only an import of the core module that holds `rot90`,
   `dualFacet2` resp. `ofMeshData`, `simplexOfPoints`. The core copies are text-identical (checked by MC-N and again
   here before deleting); the references resolve to them through `open CFDLean.Num` (qualified `Spec.X` -> `CFDLean.Num.X`).
4. Unqualified `dot` -> `Num.dot` (in code only; 260 occurrences in the committed files). Inside `namespace CFDLean.JST1` Lean
   resolves an unqualified name through the enclosing namespaces before the `open` declarations, so `dot` would bind
   to M1's `CFDLean.dot` (`CFDLean.Physics.Euler.PhysicalFlux`) instead of `CFDLean.Num.dot`. A first build without
   this edit showed the capture (failed `rw`/`simp` with `CFDLean.dot`). `Num.dot` resolves to `CFDLean.Num.dot`, the
   image of JST's `NumCore.dot`. A scan of every identifier of the folded sources against all 954 M1-M5 constant
   names in `CFDLean` found `dot` as the only collision.

Resolution check (`JST1DEP` lines of `statements-cfd.txt`): the constants in `CFDLean` outside `CFDLean.JST1` that the
JST1 statement and definition declarations use are `CFDLean.Num.*` (the image of `NumCore.*` and of the moved
definitions) and, besides them, only:

- `CFDLean.MedianDual.MeshData`
- `CFDLean.MedianDual.MeshData.Conforming`
- `CFDLean.MedianDual.MeshData.Occurrence`
- `CFDLean.MedianDual.MeshData.faceCount`
- `CFDLean.MedianDual.MeshData.faceID`
- `CFDLean.MedianDual.MeshData.points`
- `CFDLean.MedianDual.MeshData.vertex`
- `CFDLean.MedianDual.Points`
- `CFDLean.MedianDual.localInterface`
- `CFDLean.MedianDual.sixVolume`
- `CFDLean.MedianDual.volume`
- `CFDLean.Vector`

The `CFDLean.MedianDual.*` constants are written with their full name in the JST sources (`Spec/Item5.lean`) and are
the same M3 constants JST used (pinned CFD_Lean revision). `CFDLean.Vector` is not written anywhere: it is the
implicit type argument of `=` in `P1_5_6`, the result type of `CFDLean.MedianDual.localInterface` (`Vector 3`), as in
JST. So no identifier of the folded sources was captured by another M1-M5 constant.

Proofs: a separate build of the fold without delegation (all 92 original JST proofs, renamed as above) succeeded, so
every JST proof also checks against the core. In the committed fold the 37 statements proved by MC-N theorems are
one-line applications of them (`core_theorem` in the result maps; `scripts/verify.py` checks that each such proof uses
its MC-N theorem directly). Proof helpers that were reachable from the 92 proofs before delegation and not after were
removed (121 declarations in 13 proof files); helpers already unreachable in JST (18, e.g. `rfl` lemmas used by
`simp`/`dsimp`, or unused) were kept, with the two helpers one of them needs.

## Statements

| ID | Statement | pretty = | raw = | Moved definitions used | Proof |
|---|---|---|---|---|---|
| P1-1.0 | `CFDLean.JST1.Spec.P1_1_0` | yes | yes | - | JST proof |
| P1-1.1 | `CFDLean.JST1.Spec.P1_1_1` | yes | yes | - | JST proof |
| P1-1.2 | `CFDLean.JST1.Spec.P1_1_2` | yes | yes | - | JST proof |
| P1-1.3 | `CFDLean.JST1.Spec.P1_1_3` | yes | yes | - | JST proof |
| P1-1.4 | `CFDLean.JST1.Spec.P1_1_4` | yes | yes | - | JST proof |
| P1-1.5 | `CFDLean.JST1.Spec.P1_1_5` | yes | yes | - | JST proof |
| P1-1.6 | `CFDLean.JST1.Spec.P1_1_6` | yes | yes | - | JST proof |
| P1-2.0 | `CFDLean.JST1.Spec.P1_2_0` | yes | yes | - | JST proof |
| P1-2.1 | `CFDLean.JST1.Spec.P1_2_1` | yes | yes | - | `CFDLean.Num.antisymmetric_pairFlux` |
| P1-2.2 | `CFDLean.JST1.Spec.P1_2_2` | yes | yes | - | `CFDLean.Num.entropyConservative_production` |
| P1-2.3 | `CFDLean.JST1.Spec.P1_2_3` | yes | yes | - | `CFDLean.Num.WMesh.nW_row_sum` |
| P1-2.4 | `CFDLean.JST1.Spec.P1_2_4` | yes | yes | - | `CFDLean.Num.logMean_properties` |
| P1-2.5 | `CFDLean.JST1.Spec.P1_2_5` | yes | yes | - | JST proof |
| P1-2.6 | `CFDLean.JST1.Spec.P1_2_6` | yes | yes | - | `CFDLean.Num.dissipativePairFlux_conservation` |
| P1-2.7 | `CFDLean.JST1.Spec.P1_2_7` | yes | yes | - | `CFDLean.Num.dissipativePairFlux_freeStream` |
| P1-3.1 | `CFDLean.JST1.Spec.P1_3_1` | yes | yes | - | JST proof |
| P1-3.2 | `CFDLean.JST1.Spec.P1_3_2` | yes | yes | - | JST proof |
| P1-3.3 | `CFDLean.JST1.Spec.P1_3_3` | yes | yes | - | JST proof |
| P1-3.4 | `CFDLean.JST1.Spec.P1_3_4` | yes | yes | - | JST proof |
| P1-4.0 | `CFDLean.JST1.Spec.P1_4_0` | yes | yes | - | JST proof |
| P1-4.1 | `CFDLean.JST1.Spec.P1_4_1` | yes | yes | - | `CFDLean.Num.WMesh.galerkin_identity` |
| P1-4.2 | `CFDLean.JST1.Spec.P1_4_2` | yes | yes | - | JST proof |
| P1-4.3 | `CFDLean.JST1.Spec.P1_4_3` | yes | yes | - | JST proof |
| P1-4.3b | `CFDLean.JST1.Spec.P1_4_3b` | yes | yes | - | JST proof |
| P1-4.4 | `CFDLean.JST1.Spec.P1_4_4` | yes | yes | - | JST proof |
| P1-5.0a | `CFDLean.JST1.Spec.P1_5_0a` | yes | yes | - | `CFDLean.Num.WMesh.closed_of_facetPaired` |
| P1-5.0b | `CFDLean.JST1.Spec.P1_5_0b` | yes | yes | `ofMeshData` | `CFDLean.Num.ofMeshData_closed` |
| P1-5.1 | `CFDLean.JST1.Spec.P1_5_1` | yes | yes | - | `CFDLean.Num.Simplex.calculus` |
| P1-5.2 | `CFDLean.JST1.Spec.P1_5_2` | yes | yes | - | `CFDLean.Num.WMesh.dissGeom_edge` |
| P1-5.3 | `CFDLean.JST1.Spec.P1_5_3` | yes | yes | - | `CFDLean.Num.WMesh.dissGeom_outer` |
| P1-5.4 | `CFDLean.JST1.Spec.P1_5_4` | yes | yes | - | `CFDLean.Num.WMesh.dissGeom_calibration` |
| P1-5.4b | `CFDLean.JST1.Spec.P1_5_4b` | yes | yes | - | JST proof |
| P1-5.5 | `CFDLean.JST1.Spec.P1_5_5` | yes | yes | - | `CFDLean.Num.WMesh.fvRes_eq_galerkinRes` |
| P1-5.6 | `CFDLean.JST1.Spec.P1_5_6` | yes | yes | `dualFacet2`, `simplexOfPoints` | `CFDLean.Num.dualFacets_grad` |
| P1-5.7 | `CFDLean.JST1.Spec.P1_5_7` | yes | yes | `ofMeshData` | `CFDLean.Num.ofMeshData_fv_galerkin` |
| P1-5.8 | `CFDLean.JST1.Spec.P1_5_8` | yes | yes | `dualFacet2` | JST proof |
| P2-6.1 | `CFDLean.JST1.Spec.P2_6_1` | yes | yes | - | `CFDLean.Num.WMesh.sbp_defect` |
| P2-6.2 | `CFDLean.JST1.Spec.P2_6_2` | yes | yes | - | `CFDLean.Num.Simplex.median_defect_iff` |
| P2-6.3 | `CFDLean.JST1.Spec.P2_6_3` | yes | yes | - | `CFDLean.Num.WMesh.conforming_boundary` |
| P2-6.4 | `CFDLean.JST1.Spec.P2_6_4` | yes | yes | - | `CFDLean.Num.edgeForm_boundary_split` |
| P2-6.5 | `CFDLean.JST1.Spec.P2_6_5` | yes | yes | `stdWeight` | `CFDLean.Num.WMesh.standardClosure_entropy` |
| P2-6.5b | `CFDLean.JST1.Spec.P2_6_5b` | yes | yes | `stdWeight` | `CFDLean.Num.WMesh.standardClosure_linear` |
| P2-6.6 | `CFDLean.JST1.Spec.P2_6_6` | yes | yes | - | JST proof |
| P2-6.7 | `CFDLean.JST1.Spec.P2_6_7` | yes | yes | - | `CFDLean.Num.WMesh.closed_mean_galerkin` |
| P2-7.1 | `CFDLean.JST1.Spec.P2_7_1` | yes | yes | - | `CFDLean.Num.quadratic_edge_expansion` |
| P2-7.2 | `CFDLean.JST1.Spec.P2_7_2` | yes | yes | - | `CFDLean.Num.dissTensor_loewner` |
| P2-7.3 | `CFDLean.JST1.Spec.P2_7_3` | yes | yes | - | `CFDLean.Num.WMesh.dissTensor_trace` |
| P2-7.4 | `CFDLean.JST1.Spec.P2_7_4` | yes | yes | - | JST proof |
| P2-8.0 | `CFDLean.JST1.Spec.P2_8_0` | yes | yes | - | JST proof |
| P2-8.1 | `CFDLean.JST1.Spec.P2_8_1` | yes | yes | - | `CFDLean.Num.quadratureClosure_entropy` |
| P2-8.2 | `CFDLean.JST1.Spec.P2_8_2` | yes | yes | - | `CFDLean.Num.quadratureClosure_freeStream` |
| P2-8.3 | `CFDLean.JST1.Spec.P2_8_3` | yes | yes | - | `CFDLean.Num.quadratureClosure_linear` |
| P2-8.4 | `CFDLean.JST1.Spec.P2_8_4` | yes | yes | - | `CFDLean.Num.WMesh.faceRule_beta_B` |
| P2-8.5 | `CFDLean.JST1.Spec.P2_8_5` | yes | yes | - | JST proof |
| P2-8.6 | `CFDLean.JST1.Spec.P2_8_6` | yes | yes | - | JST proof |
| P2-9.0 | `CFDLean.JST1.Spec.P2_9_0` | yes | yes | - | JST proof |
| P2-9.1 | `CFDLean.JST1.Spec.P2_9_1` | yes | yes | - | JST proof |
| P2-9.2 | `CFDLean.JST1.Spec.P2_9_2` | yes | yes | - | JST proof |
| P2-9.3 | `CFDLean.JST1.Spec.P2_9_3` | yes | yes | - | JST proof |
| P2-9.4 | `CFDLean.JST1.Spec.P2_9_4` | yes | yes | - | JST proof |
| P2-10.1 | `CFDLean.JST1.Spec.P2_10_1` | yes | yes | - | JST proof |
| P2-10.2 | `CFDLean.JST1.Spec.P2_10_2` | yes | yes | - | JST proof |
| P2-10.3 | `CFDLean.JST1.Spec.P2_10_3` | yes | yes | - | JST proof |
| P2-10.4 | `CFDLean.JST1.Spec.P2_10_4` | yes | yes | - | JST proof |
| P2-10.5 | `CFDLean.JST1.Spec.P2_10_5` | yes | yes | - | JST proof |
| P2-10.6 | `CFDLean.JST1.Spec.P2_10_6` | yes | yes | - | JST proof |
| P2-10.7 | `CFDLean.JST1.Spec.P2_10_7` | yes | yes | - | JST proof |
| P2-10.8 | `CFDLean.JST1.Spec.P2_10_8` | yes | yes | - | JST proof |
| P2-8.0b | `CFDLean.JST1.Spec.P2_8_0b` | yes | yes | - | JST proof |
| P2-9.2b | `CFDLean.JST1.Spec.P2_9_2b` | yes | yes | - | JST proof |
| P2-10.8b | `CFDLean.JST1.Spec.P2_10_8b` | yes | yes | - | JST proof |
| P2-10.8c | `CFDLean.JST1.Spec.P2_10_8c` | yes | yes | - | JST proof |
| P3-11.1 | `CFDLean.JST1.Spec.P3_11_1` | yes | yes | - | `CFDLean.Num.WMesh.facetBalanced_boundary` |
| P3-11.2 | `CFDLean.JST1.Spec.P3_11_2` | yes | yes | `cross3` | `CFDLean.Num.Simplex.facet_cross3` |
| P3-11.3 | `CFDLean.JST1.Spec.P3_11_3` | yes | yes | - | JST proof |
| P3-12.1 | `CFDLean.JST1.Spec.P3_12_1` | yes | yes | - | JST proof |
| P3-12.2 | `CFDLean.JST1.Spec.P3_12_2` | yes | yes | - | JST proof |
| P3-12.3 | `CFDLean.JST1.Spec.P3_12_3` | yes | yes | - | JST proof |
| P3-12.4 | `CFDLean.JST1.Spec.P3_12_4` | yes | yes | - | JST proof |
| P3-12.5 | `CFDLean.JST1.Spec.P3_12_5` | yes | yes | `pathSimplex` | `CFDLean.Num.pathSimplex_nonobtuse` |
| P3-13.1 | `CFDLean.JST1.Spec.P3_13_1` | yes | yes | - | `CFDLean.Num.pair_production_integral` |
| P3-13.2 | `CFDLean.JST1.Spec.P3_13_2` | yes | yes | - | JST proof |
| P3-11.2b | `CFDLean.JST1.Spec.P3_11_2b` | yes | yes | `perp2` | `CFDLean.Num.Simplex.facet_perp2` |
| P3-11.4 | `CFDLean.JST1.Spec.P3_11_4` | yes | yes | `SideBalanced` | `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced` |
| P3-11.4b | `CFDLean.JST1.Spec.P3_11_4b` | yes | yes | `SideBalanced2` | `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced2` |
| P3-11.5 | `CFDLean.JST1.Spec.P3_11_5` | yes | yes | - | JST proof |
| P3-11.6 | `CFDLean.JST1.Spec.P3_11_6` | yes | yes | - | JST proof |
| P3-14.1 | `CFDLean.JST1.Spec.P3_14_1` | yes | yes | - | JST proof |
| P3-14.2 | `CFDLean.JST1.Spec.P3_14_2` | yes | yes | - | JST proof |
| P3-14.3 | `CFDLean.JST1.Spec.P3_14_3` | yes | yes | - | JST proof |
| P3-11.7 | `CFDLean.JST1.Spec.P3_11_7` | yes | yes | - | JST proof |
| P3-11.8 | `CFDLean.JST1.Spec.P3_11_8` | yes | yes | - | JST proof |
