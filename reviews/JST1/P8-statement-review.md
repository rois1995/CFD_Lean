# P8 statement review (item 23)

Independent reviewer: one fresh agent (Opus, high effort), 2026-11-26, two rounds. It received the paper lines
(`sec:mixed`, `lem:avg` with its proof, `prop:splits`), the statement file `Spec/Item23.lean`, the definitions it uses,
the proposal and the numerics, but not the author's opinion. Round 1: one `lake env lean` run on a scratch copy and an
independent exact-fraction Python check. Round 2 (after the fix): Python only.

**Round 1 verdict: BLOCKING** (P8-23.2 false as written). **Round 2 verdict: not blocking.**

## Findings and follow-up

| # | Severity | Finding | Follow-up (before freeze) |
|---|---|---|---|
| 1 | blocking | `blockMesh` set the affine fields `A = 1, b = 0`, so `Cell.centroid` was (½,½,½) for every cell and the centroid test of `Mesh.Conform` could not hold at the 48 shared triangles (the author found the same issue independently; `P8-search.py` had used the true centroids). | `b` now makes `Cell.centroid` the vertex average of each cell; docstring says the cells are not affine. Round 2: all 48 shared triangles pass under all 6 orderings. |
| 2 | should-fix | The failure depends on inverted sub-tetrahedra entering with the positive measure `|T|`; with orientation-signed volumes the sum is exactly 0. | Docstring states the cause. |
| 3 | minor | `Σ_k n = -β` identically; state the exact value. | Last clause is now `Σ_k n_13,k = (0, 0, 7/30)` (round 2 confirmed the value and sign). |
| 4 | minor | The trilinear vertex clauses hold for any positions. | Kept as a sanity clause (as P7-22.4). |
| 5 | minor | The spec file contains `blockIdx_inj` (by `decide`). | Accepted; needed for the embedding. |

Checked true in round 1: `kuhnX` is the stated rotation, Jacobian minimum 9/25; 8 neighbour-fan splits, 64 same-side
witnesses (product 7/25); block indices ≤ 26 (`% 27` inert); vertex 13 interior; 48 shared and 96 boundary triangles;
no degenerate sub-tetrahedron, 128 inverted. Also: the block fails `ConformT` at 16 shared triangles (noted in the
docstring). Paper notes: as G8 (`lem:avg` needs positively oriented sub-tetrahedra, or orientation-signed volumes,
which would lose the positivity of `V` and of the weights); the Kuhn splits recommended by `prop:splits` fail too.
