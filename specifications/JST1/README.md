# Paper 1 (JST): specifications folded from JST_Paper_Lean (MR-2)

Source: JST_Paper_Lean branch `v436`, commit `afdf4f9b4f98f089af82074bf7e4db99177844ad` (Lean v4.36.0, Mathlib
`fc4f59e`). All 92 frozen statements are proved there and here.

| File | Content |
|---|---|
| `P1.md`, `P2.md`, `P3.md`, `*-proposal.md`, `P1-approval.md` | frozen specifications, proposals and approval, copied verbatim (they name the JST paths `Paper1/...`, `NumCore/...`) |
| `PAPER_GAPS.md`, `REPORT.md` | paper notes, copied verbatim |
| `P1-results.json`, `P2-results.json`, `P3-results.json` | result maps with the new names: `Paper1.Spec.X` -> `CFDLean.JST1.Spec.X`, `Paper1.Proofs.x` -> `CFDLean.JST1.Proofs.x`, files under `CFDLean/Papers/JST1/Proofs/`; `core_theorem` marks the 37 proofs that apply an MC-N theorem |
| `frozen.sha256` | sha256 of the folded statement and definition files (`CFDLean/Papers/JST1/**` except `Proofs/`) and of the core files that now hold the JST `NumCore` definitions and the moved definitions; pinned in `scripts/verify.py` |
| `source-hashes/` | the JST frozen and pin hash lists, for reference only (they list JST paths) |

Path map JST -> CFD_Lean: `Paper1/<sub>/<F>.lean` -> `CFDLean/Papers/JST1/<sub>/<F>.lean`; `NumCore/Basic.lean`,
`LogMean.lean` -> `CFDLean/Foundations/`; `NumCore/Simplex.lean` -> `CFDLean/Geometry/Simplex.lean`;
`NumCore/WMesh.lean` -> `CFDLean/Discrete/Mesh.lean`; `NumCore/Boundary.lean`, `Balance.lean` ->
`CFDLean/Geometry/MeshBoundary.lean` (`EW` in `Discrete/Mesh.lean`). Definitions that MC-N moved verbatim into the core
and that the folded files use from there: `cross3`, `perp2`, `pathSimplex`, `rot90`, `dualFacet2`
(`Geometry/Simplex.lean`), `facetSide`, `SideBalanced`, `facetSide2`, `SideBalanced2` (`Geometry/MeshBoundary.lean`),
`stdWeight` (`Entropy/PairFlux.lean`), `ofMeshData`, `simplexOfPoints` (`Geometry/MedianDualBridge.lean`).

Statement comparison: `evidence/JST1/fold-diff.md`.
