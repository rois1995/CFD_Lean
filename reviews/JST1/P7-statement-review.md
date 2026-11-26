# P7 statement review (item 22)

Independent reviewer: one fresh agent (Opus, high effort), 2026-11-26. It received the paper lines (`sec:mixed`,
`lem:avg` and its proof), the statement file `Spec/Item22.lean`, the definitions it uses (reference cells, pulling
splits, assembly, `Conform`, `FacetBalanced`), the proposal and the numerics, but not the author's opinion.
Read-only review; one `lake env lean` run on a scratch copy (elaboration, `.det` is `ContinuousLinearMap.det`, 384
hexahedron tets of length 4, `Conform`/`ConformT` of the one-cell mesh proved by the first disjunct) and numpy in the
Lean vertex numbering: `twistX` is the stated rotation; Jacobian minimum on an 11³ grid 0.8 = (1 + cos θ)/2;
`tetDet X · tetDet ref`: 352 positive, 32 negative, none zero; 24 of 32 interior triangles unbalanced.

**Verdict: no BLOCKING finding**; all four statements true, well typed, not vacuous (affine meshes satisfy both
hypotheses; split orientation is an open condition); no name capture.

## Findings and follow-up

| # | Severity | Finding | Follow-up (before freeze) |
|---|---|---|---|
| 1 | should-fix | 22.4 refuted facet balance only (a sufficient condition); on a one-cell mesh no vertex is interior, so "the closure fails" was not what was proved. Numerically `β_i` differs from the boundary formula at all 8 vertices. | Added the clause `∃ i, β_i ≠ ⅓ Σ` (boundary facet vectors at `i`), the conclusion of P3-11.1 under facet balance; docstring reworded. |
| 2 | minor | `twistMesh.Conform` is trivial for one cell. | Also states `ConformT twistMesh twistBd`; docstring says both are trivial, so split orientation is the only failing hypothesis of 22.2. |
| 3 | minor | 22.1 dropped the analogue of P3-11.7 clause 3 (sub-tets at a cell-face triangle on one side), which 22.2 needs. | Added as a third clause (over all sub-tetrahedra of all splits). |
| 4 | minor | Numbering differs from the proposal; the Kuhn item is dropped. | Proposal updated (22.3 = affine special case, 22.4 = twisted cube; Kuhn item not stated). |
| 5 | minor | `twistMesh` sets the unused affine fields `A = 1, b = 0`. | Accepted (docstring says unused). |

Paper notes of the reviewer (recorded in `PAPER_GAPS.md`, G8): `β_i = ∮ φ_i N` is ambiguous for non-planar faces (it
should be the mean over the split traces, both diagonals with weight ½); conformity at shared faces must hold at
the level of sub-tetrahedra for non-convex cells; "valid mesh" is not defined.
