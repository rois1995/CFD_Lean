# MR: final library layout (scope frozen 2026-11-25)

Authorization: `specifications/MC-approval.md` (user option A). No new mathematics. Branch `final-layout` from
`main` 5a072de.

## MR-1: layered folders

Every module moves to the folder of its main catalog layer. File contents change only in `import` lines (and the
umbrella files). Namespaces and declaration names do not change, so every promised theorem keeps its name and type.

| Old module | New module |
|---|---|
| `CFDLean.Num.Basic`, `CFDLean.Num.LogMean` | `CFDLean.Foundations.Basic`, `CFDLean.Foundations.LogMean` |
| `CFDLean.Core.Coordinates` | `CFDLean.Foundations.Coordinates` |
| `CFDLean.Core.State`, `.PhysicalFlux`, `.PhysicalJacobian` | `CFDLean.Physics.Euler.State`, `.PhysicalFlux`, `.PhysicalJacobian` |
| `CFDLean.Flux.Roe.Averages`, `.Linearization`, `.Spectral` | `CFDLean.Physics.Roe.Averages`, `.Linearization`, `.Spectral` |
| `CFDLean.Flux.Roe.Flux` | `CFDLean.Schemes.Roe.Flux` |
| `CFDLean.Num.Simplex`, `CFDLean.Num.Boundary`, `CFDLean.Num.Bridge` | `CFDLean.Geometry.Simplex`, `CFDLean.Geometry.MeshBoundary`, `CFDLean.Geometry.MedianDualBridge` |
| `CFDLean.Geometry.MedianDual` and `CFDLean.Geometry.MedianDual.*` | unchanged |
| `CFDLean.Num.Mesh`, `CFDLean.Num.Galerkin` | `CFDLean.Discrete.Mesh`, `CFDLean.Discrete.Galerkin` |
| `CFDLean.Discretization.Assembly` | `CFDLean.Discrete.Assembly` |
| `CFDLean.Num.PairFlux`, `CFDLean.Num.Production` | `CFDLean.Entropy.PairFlux`, `CFDLean.Entropy.Production` |
| `CFDLean.Boundary.Assembly`, `.Stationary`, `.Controls`, `.AssemblyControls` | `CFDLean.Schemes.Boundary.Assembly`, `.Stationary`, `.Controls`, `.AssemblyControls` |
| `CFDLean.Time.*` | unchanged |
| `CFDLean.Num.Internal.*` | `CFDLean.Internal.*` |
| `CFDLean.Num` (umbrella) | removed; `CFDLean` imports everything |

Verifier: the accepted-source guard accepts a moved file only through `specifications/MR-paths.json`
(old path → new path) and only if the new file equals the accepted (or MC-T port) file except for `import` lines.
Catalog `module` fields follow the move.

## MR-2: paper 1 in `CFDLean/Papers/JST1/`

The JST_Paper_Lean formalization (branch `v436`, all 92 statements proved) moves into CFD_Lean:
`CFDLean/Papers/JST1/` with sub-folders as in JST (`Euler`, `Viscous`, `SST`, `Mixed`, `Geometry`, `Scheme`,
`Spec`, `Proofs`). Namespace `Paper1` becomes `CFDLean.JST1`; it uses the core modules (namespace `CFDLean.Num`) instead of its own
`NumCore` (identical definitions). The 92 statements keep their meaning: statement dumps before/after must agree up
to the namespace change. Frozen statement hashes, result maps (P1/P2/P3), paper notes (`PAPER_GAPS.md`,
`REPORT.md`) and reviews move to `specifications/JST1/` and `reviews/JST1/`; the paper check joins `verify.py`
and the catalog (layer and method tags for the 92 theorems). JST_Paper_Lean becomes an archive pointing here.
The paper's own Euler definitions stay separate from M1 (unifying them is later mathematical work).

## MR-3: verifier

Compare promised types also with `pp.notation false` / `pp.coercions false` (raw types recorded in evidence).
Replace the per-milestone inherited-type code paths (M2, M3, M4) by one table-driven check with identical
behaviour (same accepted revisions, same failures), covered by fixtures.

## Validation

`lake build`, `verify.py`, fixtures, catalog check, an AI statement review, and `lake check --paranoid` (sandboxed)
before the merge to `main`.
