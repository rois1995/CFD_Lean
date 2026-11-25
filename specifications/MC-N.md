# MC-N: numerical core library in CFD_Lean (scope frozen 2026-11-25)

Authorization: `specifications/MC-approval.md` (split MC-T / MC-N; review waived; merge allowed). Source of the code:
JST_Paper_Lean branch `v436` (commit afdf4f9), where every item below is already proved on Lean v4.36.0.

## Modules (new, namespace `CFDLean.Num`, directory `CFDLean/Num/`)

| Module | Content (JST origin) |
|---|---|
| `Basic` | `Vec`, `dot`, `len`, `outer`, `pairF`, `frob`, `pairCLM` (NumCore/Basic) |
| `LogMean` | log mean (NumCore/LogMean, P1-2.4) |
| `Simplex` | P1 simplex: edge matrix, gradients, volume, facets; calculus (P1-5.1); 3D facet = ½ cross product and shared facets (P3-11.2); 2D rotated edge (P3-11.2b); Kuhn path simplices (P3-12.5) |
| `Mesh` | weighted simplex meshes `WMesh` and their P1 operators (NumCore/WMesh); row/column sums and β (P1-2.3); SBP form and defect (P2-6.1, 6.2); dissipation geometry (P1-5.2-5.4); dissipation tensor (P2-7.1-7.3) |
| `Boundary` | conforming meshes, boundary facets, facet balance, side balance (NumCore/Boundary, Balance); P1-5.0a, P2-6.3, P3-11.1, P3-11.4, P3-11.4b |
| `PairFlux` | antisymmetric pair fluxes and entropy-conservative two-point fluxes (P1-2.1, 2.2, 2.6, 2.7 generic); quadrature boundary closure (P2-8.1-8.4); eq. pf-B2 (P2-6.4); standard closure (P2-6.5, 6.5b) |
| `Galerkin` | Galerkin identity (P1-4.1), finite-volume ⇔ Galerkin (P1-5.5), consistency(b) (P2-6.7) |
| `Production` | exact pair production by the fundamental theorem of calculus (P3-13.1) |
| `Bridge` | `ofMeshData`: the M3 median dual as a `WMesh` (JST Geometry/CFDBridge); P1-5.0b, P1-5.6, P1-5.7 |

## Rules

- Definitions are moved verbatim (namespace change only). Each theorem is stated directly (no `Prop` wrapper) with the
  same mathematical content as its JST statement; the result map `specifications/MC-N-results.json` records
  ID → JST statement → CFD theorem name.
- M1-M5 sources, contracts and types are not changed. MC-N adds no axiom.
- JST_Paper_Lean then imports `CFDLean.Num`; its `NumCore` files become thin aliases and its frozen statements keep
  their meaning (checked by the statement dumps as in the v4.36 port; the expected difference is the namespace of the
  constants).

## Catalog (MC-C)

`catalog/theorems.json` + generated `catalog/README.md`: every promised theorem of M1-M5 and MC-N with layer
(Foundations / Geometry / Discrete operators / Entropy framework / Physics models / Schemes / Time), method tags
(FEM / FVM / both / method-free), status (accepted / pending / candidate) and source. The verifier checks coverage.
