# CFD_Lean

Independent exact-real Lean 4 contracts for compressible CFD. M1 specifies ideal-gas Euler states, conditional primitive/conservative conversion identities, admissibility and physical flux for oriented area vectors in arbitrary finite dimension. See [the contract](specifications/M1.md), [source/proof map](references/M1.md) and [approval record](specifications/M0-approval.md).

The library imports mathlib only. A future SU2 verification package may depend on an immutable CFD_Lean revision, using separate working trees and build directories.

## Reproduce the independently reviewed M1 candidate

Frozen mathematical candidate: `0a88e36b3810cd5adc3881db526ca8a35f81afbb`.

Use a fresh, clean, detached checkout of that commit with no `.lake`. Put Lean/Lake 4.19.0, Git, Python 3, Node, npm, sha256sum and realpath on PATH. Keep a separate copy of [the published review bundle](reviews/M1/) outside the fresh checkout. Its scripts and logs are preserved byte-for-byte from the submitted reviewer evidence, with their original SHA256SUMS.

From the fresh candidate checkout, replace `/absolute/path/to/published-review` below with that separate `reviews/M1` directory, and choose log directories outside the checkout:

```bash
git checkout --detach 0a88e36b3810cd5adc3881db526ca8a35f81afbb
sha256sum -c evidence/SHA256SUMS
bash /absolute/path/to/published-review/reviewer/ReproduceM1.sh ../M1-replay-logs
bash /absolute/path/to/published-review/reviewer/RunReviewerChecks.sh ../M1-independent-checks
```

The tested reproduction script checks the frozen snapshot, fetches all nine manifest-pinned source trees, disables both binary-cache mechanisms (`LAKE_NO_CACHE=1` and `MATHLIB_NO_CACHE_ON_UPDATE=1`), builds pinned ProofWidgets JavaScript locally using its npm lockfile, and runs the original verifier. The widget bootstrap is necessary: the pinned mathlib blocks a missing widget asset build during the normal downstream build. Setting only the mathlib update-hook variable is insufficient for a fresh source-only reproduction.

Check the committed hashes **before** verification: the verifier regenerates evidence/SHA256SUMS. The frozen Git commit remains the baseline. The reviewer independently completed and replayed the source-only procedure; detailed commands and results are in [the report](reviews/M1/CFD_Lean_M1_Independent_Review.md).

## MC-T: Lean v4.36.0 (current toolchain)

Since MC-T the library builds with `leanprover/lean4:v4.36.0` and Mathlib tag `v4.36.0`
(`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). The port changed proofs and imports only; all 199 promised theorems
keep their names, stages and meaning. Type map: [MC-port-types.json](specifications/MC-port-types.json) (191
identical, 8 notation/rename), notes in [evidence/port-types.md](evidence/port-types.md). The verifier accepts an
accepted source only if it equals its accepted revision or the reviewed port revision `4f249ae`, and an accepted type
only through the pinned map. Status: implemented and AI-reviewed; independent human review waived by the user
([MC-approval.md](specifications/MC-approval.md)). The v4.19 sections below are kept as history.

## MC-N: numerical core library (`CFDLean.Num`)

The modules `CFDLean/Num/{Basic,LogMean,Simplex,Mesh,Boundary,PairFlux,Galerkin,Production,Bridge}.lean` (since
MR-1 in the layer folders below) hold the generic simplex/mesh/pair-flux results moved from JST_Paper_Lean (`v436`, `afdf4f9`): scope
[MC-N.md](specifications/MC-N.md), bindings [MC-N-results.json](specifications/MC-N-results.json) (37 theorems),
statement map [evidence/mc-n-map.md](evidence/mc-n-map.md). Definitions are copied verbatim (namespace change only);
each JST `Prop` body is the type of a directly stated theorem, identical up to the namespace of its constants. Proof
helpers live in `CFDLean.Num.Internal`. The verifier checks that every MC-N theorem is a root theorem with standard
axioms in its module and that no pre-existing (M1-M5) `CFDLean` source differs from the MC-N base `497b356`.

## Library layout

Since MR-1 ([MR.md](specifications/MR.md)) each module sits in the folder of its main catalog layer; `CFDLean.lean`
imports every module. Namespaces and declaration names did not change (the MC-N core keeps namespace `CFDLean.Num`).

| Folder | Content |
|---|---|
| `CFDLean/Foundations/` | `Basic`, `LogMean`, state `Coordinates` |
| `CFDLean/Physics/` | `Euler/` (state, physical flux and Jacobian), `Roe/` (averages, linearization, eigenstructure) |
| `CFDLean/Geometry/` | `Simplex`, `MeshBoundary`, the median dual `MedianDual/`, `MedianDualBridge` |
| `CFDLean/Discrete/` | primal `Mesh` operators, `Galerkin` identities, edge `Assembly` |
| `CFDLean/Entropy/` | `PairFlux`, `Production` |
| `CFDLean/Schemes/` | `Roe/Flux` (numerical flux), `Boundary/` (boundary transfers, stationary residual, controls) |
| `CFDLean/Time/` | explicit Euler step and its controls |

The old -> new paths are in [MR-paths.json](specifications/MR-paths.json) (hash-pinned in `scripts/verify.py`); the
verifier finds an accepted source at its new path only through this map and accepts it only if it equals the accepted
(or MC-T port) file except for the `import` header.

## Development verification

Lean: `leanprover/lean4:v4.19.0`. Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Transitive dependencies are pinned in lake-manifest.json.

After the pinned dependency sources and widget assets have been bootstrapped, run:

```bash
sha256sum -c evidence/SHA256SUMS
LAKE_NO_CACHE=1 MATHLIB_NO_CACHE_ON_UPDATE=1 python3 scripts/verify.py
```

This incremental command is not the complete fresh-checkout bootstrap; use the source-only procedure above for the frozen M1 candidate. Project proof terms are checked by Lean's kernel. The current verifier inventories elaborated project modules, retains qualified declaration names, rejects duplicate rows, checks cumulative approved result bindings and their frozen contract hash, and protects accepted M1 source hashes. It reports all logical roots and compiler metadata separately. Run the parser/coverage fixtures with `python3 -m unittest discover -s scripts -p test_verify.py`. Historical M1 review scripts remain tied to the original frozen M1 revision.

## Review status

The independent decision is **Accept M1**, with both original review conditions closed. The accepted mathematical revision is `0a88e36b3810cd5adc3881db526ca8a35f81afbb`; documentation follow-up `180ff1be1aa95d943574efd9c05cd4de320a88b6` closed the conditions. See the supplied [final acceptance record](reviews/M1/CFD_Lean_M1_Acceptance.md). The original conditional report and evidence remain intact as review history.

Acceptance covers the exact-real M1 state algebra and oriented physical flux only. The [next-step handoff](reviews/M1/START_HERE_Agent_A.md) requests an original 3D Roe-flux proposal. The [M2 proposal](specifications/M2-proposal.md) received an independent recommendation for implementation. Andrea approved M2 and authorized M2a on 2026-11-13; see [the approval record](specifications/M2-approval.md), [frozen contract](specifications/M2.md), and [result bindings](specifications/M2-results.json). M2a (M2-J) is independently accepted without outstanding conditions at `3788009de306d80e002976e66ba2b1103e2dbd83`; see [the acceptance record](reviews/M2a/Acceptance.md). The original worker checkpoint remains identifiable at `4d845ad`. M2b (M2-A/R/L), preserving J, is independently accepted at `c92c0f66360f85c0a3339ab9b30fc00c39ee5f93`; see [the acceptance record](reviews/M2b/Acceptance.md). M2c (M2-E/D/O), preserving J/A/R/L, is independently accepted at `6ee9d53e79e0c6f11e75b1b387c21256572d0fcd`; see [the acceptance record](reviews/M2c/Acceptance.md). M2d and full M2 are independently accepted without blockers or outstanding conditions at `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`; see [M2d acceptance](reviews/M2d/Acceptance.md) and [full-M2 acceptance](reviews/M2/Acceptance.md). The immutable downstream mathematical pin is recorded in [accepted-M2.json](specifications/accepted-M2.json). The current checker compares all 140 accepted M2/M3/M4a bindings, stages, parts and types with the immutable accepted M4a revision and elaborates explicit expected-type checks. The replay script compares regenerated audit evidence with the candidate byte for byte.

The approved private remote is [rois1995/CFD_Lean](https://github.com/rois1995/CFD_Lean). The accepted M2 Roe interface feeds the approved M3 node-centered assembly, followed by selected boundary algorithms and explicit time update. Books and papers remain in the external reference collection; repository reference records contain metadata and source locators only.

## Accepted M2a checkpoint

See [M2a source/result traceability](references/M2a.md). This implements M2-J: coordinate round trips, the explicit physical Jacobian action, the Frechet derivative of the actual M1 flux for fixed arbitrary normal/area and nonzero density, admissible-domain openness, Euclidean area normalization and zero-area derivative. The M2b extension below proves the subsequent two-state obligations using this accepted baseline.

A fresh source-only replay for a new frozen checkpoint uses `bash scripts/reproduce.sh FULL_COMMIT_SHA /outside/checkout/logs` from a clean detached checkout of that exact full commit, without `.lake`. The script reuses the reviewed pinned-source and widget bootstrap, disables both binary-cache mechanisms and then runs the current audit and fixtures. It is separate from the historical M1-specific replay script.

## Accepted M2b checkpoint

See [M2b source/result traceability](references/M2b.md). M2-A proves square-root weight bounds, symmetry, the enthalpy variance identity and positive averaged sound speed. M2-R proves parameter-map recovery of the actual M1 state and flux, their Frechet derivatives B/C, exact midpoint jumps, a two-sided inverse of B, the C B-inverse matrix order and the arbitrary-normal/integrated secant identity. M2-L proves joint operator-norm continuity, diagonal equality with M2a's physical Jacobian and the full equal-state limit. These results use the unchanged approved contract and accepted mathematical sources.

The result map contains 37 active J/A/R/L theorem bindings, now all independently accepted at c92c0f6. `StatementChecks.lean` provides explicit inherited/new expected-type checks and exact stationary-contact/shear sound-speed examples. The generated `evidence/bindings-diff.patch` and `evidence/binding-type-diff.json` expose the full binding/type changes from accepted M2a. The independent acceptance includes a successful cold-source replay and exact deterministic evidence comparisons; the original worker and reviewer evidence remain separate. These historical M2b counts are preserved; the accepted M2c and current M2d extensions are described below.

## Accepted M2c checkpoint

See [M2c source/result traceability](references/M2c.md). The actual Roe matrix has the proved 1+3+1 eigenspace dimensions, a complete five-vector eigenbasis and the shifted cubic identity. The approved polynomial projectors have proved ranges, ranks, zero cross-products, idempotence and sum I. Contact/shear completeness holds for any tangent basis. The basis-free absolute-speed operator equals R diag(abs speeds) R-inverse for every complete eigenbasis, and the matrix/projectors/dissipation have proved reversal and state-swap behavior. Stationary and sonic speeds remain in the domain.

There are 58 active J/A/R/L/E/D/O theorem bindings: all independently accepted at 6ee9d53. All inherited definition/proof sources, scientific contracts, toolchain and dependency pins remain fixed; the import-only umbrella exports the new module. The 41 explicit Lean examples include zero-speed and oblique-normal controls. The independent acceptance includes a cold-source replay and exact deterministic evidence comparisons. The M2d extension below consumes this accepted baseline.

## Accepted M2d and complete M2

See [M2d traceability and complete obligation map](references/M2d.md). The public `CFDLean.Roe.numericalFlux` is the original integrated Roe flux on M1 states with an explicit zero-area branch. General proofs establish consistency, signed reversal, nonnegative area scaling and left/right full upwinding, including sonic equality. The approved receding-state witness uses the identical acoustic projector as the flux and proves negative intermediate density despite admissible endpoints and positive averaged sound-speed square.

All 12 approved M2 IDs are populated: 66 theorem bindings, including all 58 accepted inherited bindings/types. Exact controls include the approved moving/oblique/contact/shear examples and both sonic upwind directions. The frozen contract, accepted mathematical sources and dependency pins are unchanged. The complete fresh source replay and reviewer prompt are published in [the M2d checkpoint](reviews/M2d/README.md). The supplied independent decision accepts M2d and composed M2 within the approved exact-real scope, with no outstanding conditions. See [the preserved independent report](reviews/M2d/independent-ca1fc5e/report/Review.md). M3a is accepted; the concrete M3b candidate is described below.

## Accepted full M3 and next M4 proposal

Andrea approved the reviewed area-vector convention, conforming tetrahedral scope, six result groups and the complete M3a/M3b plan; see [approval](specifications/M3-approval.md), [frozen specification](specifications/M3.md) and [representation precision](specifications/M3-representation.md). The original proposal and independent reports remain unchanged in reviews/M3.

M3a is independently accepted without conditions at `a70270c3f771e66bcaaebc18b8480c32f9606b1e`; see [the acceptance record](reviews/M3a/Acceptance.md). It supplies I/R/O and conditional C. M3b began by protecting all 84 then-accepted M2/M3a bindings, exact stages/parts/types and mathematical sources, including Assembly.lean; the current full-M3 guard extends this to 117.

The [M3b source/result map](references/M3b.md) covers the concrete barycentric median dual. Explicit finite node/cell data and a conforming-embedding predicate exclude duplicate cells, coincident distinct used nodes, nonconforming hull intersections and face multiplicity above two. Face incidences are computed from the vertex identities. Closure and volume partition are derived conclusions, not supplied certificates.

Each edge is one increasing pair of co-cell node IDs. Its oriented partial triangle vectors are summed before evaluating one accepted integrated Roe flux. Exterior patches retain cell, primal face and owner identities, with proved exact multiplicities. Local flag-face pairing and shared primal-face cancellation derive the very same area closure used by assembly. The 24 determinant volumes give six pieces per vertex, the incident Vol(T)/4 formula, used-node positivity and total volume. No measure-theoretic volume of a union is asserted.

The concrete closure theorem instantiates the accepted common-state Roe residual with compatible physical boundary transfers and the global boundary balance. Exact controls include standard and oblique tetrahedra, a conforming pair sharing a face, all flag volumes/local closures, actual compatible/incompatible constant-state boundaries, excluded degenerate/unused/nonmanifold cases and nonparallel Roe nonadditivity. See [the M3b/full-M3 handoff](reviews/M3b/README.md).

M3b and composed full M3 are independently accepted without blockers or outstanding conditions at `e2ea538b8da38c01c098ef28a3ea31030d90c6bb`. See [M3b acceptance](reviews/M3b/Acceptance.md), [full-M3 acceptance](reviews/M3/Acceptance.md), [original independent report](reviews/M3b/independent-e2ea538/report/Review.md) and [immutable downstream pin](specifications/accepted-M3.json). The supplied replay and separate reviewer controls are preserved unchanged. All 117 cumulative bindings and all accepted mathematical sources are protected by the next-stage guard. Original M3b handoff/replay records retain their historical pending fields.

The [M4 proposal](specifications/M4-proposal.md) received an independent recommendation for approval without mandatory amendment. Andrea explicitly approved the reviewed choices and full two-stage plan; see [the approval record](specifications/M4-approval.md), [frozen contract](specifications/M4.md), [interface precision](specifications/M4-precision.md) and [original review](reviews/M4/proposal-936d20d/report/Review.md).

## Accepted full M4 and current M5 proposal

[M4a B/W/P](references/M4a.md) is independently accepted without conditions at `37c1e6ee4618b0183135c2795b3aa6ebea2f22d5`; see [acceptance](reviews/M4a/Acceptance.md), [original review](reviews/M4a/independent-37c1e6e/report/Review.md) and [scoped accepted pin](specifications/accepted-M4a.json). Before M4b work, the guard was extended and verified for all 140 accepted bindings/types and mathematical sources, including the boundary definitions/controls. The earlier M3 mathematical pin remains separately recorded.

The [M4b source/result map](references/M4b.md) implements R/O/C using the actual selected patchTransfer and the unchanged accepted Roe residual and concrete geometry. Global vector/component balances retain wall/symmetry pressure momentum and exclude those pieces from mass/energy transfer. Constructed kinds, prescribed data, nodal states, ownership and areas are all transported under finite node/edge/boundary relabeling. Concrete common-state preservation retains gamma>1, actual admissibility, per-wall tangency and matching prescribed exterior data; closure is derived from the accepted conforming median dual.

Controls include standard/oblique/two-cell compatible cases, all three boundary kinds at one corner, actual incompatible wall/exterior residuals, nonzero transported residuals, all-wall mass/energy balance for nonconstant admissible nodal data and retained nonzero pressure force in an abstract balance example. No correction is inserted into the algorithm. The accepted 153-example prefix is unchanged.

Both scoped M4b R/O/C and composed full M4 B/W/P/R/O/C are independently accepted without conditions at `3a586a42546cba1784cc79269e3f9d1c5d843f0c`; see [M4b acceptance](reviews/M4b/Acceptance.md), [full-M4 acceptance](reviews/M4/Acceptance.md), [original review](reviews/M4b/independent-3a586a4/report/Review.md) and [accepted pin](specifications/accepted-M4.json). All six IDs are populated, with 39 M4 bindings, 156 cumulative promises and no deferred M4 result. The current guard protects all 156 accepted types, all M4 records/stages and every accepted mathematical source. Original handoff/replay archives keep their historical pending fields/counts unchanged. The separate accepted-M3 pin is preserved.

The [M5 proposal](specifications/M5-proposal.md) received an independent recommendation to implement without mandatory amendments; the [original review](reviews/M5/proposal-3dcb73d/report/Review.md) remains unchanged. Under the [standing authorization](reviews/Standing_Authorization.md), its exact reviewed copy, authorization and six-ID map were [frozen](specifications/M5.md) before implementation at `9ee58a9a0226844cda835ac0b8285d64891f1dd0`. Historical pending wording in the copied proposal is superseded by [M5-approval.md](specifications/M5-approval.md).

[M5](references/M5.md) now implements the reviewed single lumped explicit Euler step at the OLD state on actual positive used-node volumes, with an explicit unused-node hold branch. It proves actual-boundary common-step vector/component balances, the exact unequal-step edge defect, qualified concrete common-state preservation and fully transported data. There are 43 new M5 bindings, 199 cumulative promises and no deferred M5 ID. All 156 accepted contracts remain protected. Exact controls include standard/oblique/two-cell geometry, unused allocation, admissible unequal-step nonconservation and an admissible-input large-step negative-density witness. These establish neither a CFL guarantee nor automatic update positivity. Independent M5 acceptance is pending; M6 remains separate.

No characteristic/nonreflecting boundary, projected or full symmetry update, time-accuracy/stability/CFL guarantee, entropy/update-positivity repair, mixed elements, mesh importer or SU2 correspondence is claimed.
