# M3a review checkpoint

Worker submission of the approved M3a abstract-assembly stage. M2 remains independently accepted at its immutable revision. M3a acceptance is pending; M3b's concrete geometry, volume and constant-state composition are not submitted here.

- Mathematical candidate: [`a70270c3f771e66bcaaebc18b8480c32f9606b1e`](https://github.com/rois1995/CFD_Lean/commit/a70270c3f771e66bcaaebc18b8480c32f9606b1e).
- Accepted inherited baseline: `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`, with all 66 M2 bindings/types; [full-M2 independent acceptance](../M2/Acceptance.md).
- M3 approval/freeze: `3189a603b3f6af953f0828d6b2e239320fd2cd20`; [Andrea's explicit approval](https://github.com/rois1995/CFD_Lean/blob/a70270c3f771e66bcaaebc18b8480c32f9606b1e/specifications/M3-approval.md), [frozen reviewed specification](https://github.com/rois1995/CFD_Lean/blob/a70270c3f771e66bcaaebc18b8480c32f9606b1e/specifications/M3.md), [approved representation precision](https://github.com/rois1995/CFD_Lean/blob/a70270c3f771e66bcaaebc18b8480c32f9606b1e/specifications/M3-representation.md).
- [Qualified M3 result/part map](https://github.com/rois1995/CFD_Lean/blob/a70270c3f771e66bcaaebc18b8480c32f9606b1e/specifications/M3-results.json), [proof/assumption map](https://github.com/rois1995/CFD_Lean/blob/a70270c3f771e66bcaaebc18b8480c32f9606b1e/references/M3a.md), [new assembly module](https://github.com/rois1995/CFD_Lean/blob/a70270c3f771e66bcaaebc18b8480c32f9606b1e/CFDLean/Discretization/Assembly.lean), [statement and exact controls](https://github.com/rois1995/CFD_Lean/blob/a70270c3f771e66bcaaebc18b8480c32f9606b1e/StatementChecks.lean).

## Scientific scope and declarations

All new names below have prefix CFDLean.Assembly. The underlying states and five-coordinate chart are the accepted M1/M2 objects.

| Approved part | New bindings | Delivered interface |
| --- | --- | --- |
| M3-I / M3a | 8 | Distinct endpoints, tail/head signs, exact positive/negative support, zero sum, scatter identity and filtered outgoing/incoming residual enumeration. |
| M3-R / M3a | 2 | For arbitrary finite five-vector edge/boundary transfers, sum of node residuals equals sum of owner-assigned exterior transfers; specialization to the actual accepted Roe flux. |
| M3-O / M3a | 6 | Independently evaluated outward Roe orientation equals the stored signed transfer; generic and actual-Roe reversal invariance; generic and actual-Roe simultaneous node/edge/boundary reindexing; explicit zero-area transfer. |
| M3-C / M3a | 2 | At a common state and explicitly compatible boundary transfers, residual equals actual M1 physical flux on the metric defect; zero defect implies zero residual conditionally. |
| M3-G/V and M3-C / M3b | Deferred | Concrete tetrahedral median-dual construction, derived geometry/volumes and concrete composition. No theorem or acceptance claimed. |

Interfaces is abstract finite incidence input: each interior interface record has two distinct endpoints and each exterior piece has one owner. No mesh validation or geometric closure is smuggled into the structure. The opaque B piece identities remain available for the later concrete face/owner representation. residual uses the same vector sum for three-component metric data and five-component conserved transfers. It adds no physical-state arithmetic instance, area multiplier, volume division or time update.

The generic balance proof exchanges finite sums and cancels the paired incidence signs. Independently, outwardTransfer evaluates the actual accepted numericalFlux at each endpoint's outward orientation; accepted M2 reversal connects this to the single stored transfer. Thus physical orientation and generic scatter cancellation have separate proof dependencies. Neither desired balance nor geometric closure is a premise of global_balance.

Arbitrary selected edge reversals swap endpoints and reverse area/transfer, preserving each node residual. Reindexing transports node states, endpoints, edge areas, piece owners and supplied boundary data together. The theorem quantifies over all three equivalences, not merely a reordered edge list.

The constant-state result consumes accepted M2 consistency and a real-linear area map built from the actual M1 physicalFlux using its accepted add/scalar laws. Boundary transfers in the statement are explicitly physicalFlux on their own outward areas. It computes the residual as physicalFlux on metricDefect. In M3a, a zero defect is a hypothesis. M3b must derive that defect's vanishing from the actual selected tetrahedral construction and instantiate this same assembly. M3a does not prove mesh closure.

These algebraic types often hold on larger raw domains. Physical use retains common gamma>1 and admissible M1 states; raw total-real expressions supply no extra physical interpretation outside that domain. No boundary algorithm, second-order reconstruction/accuracy, entropy property or update admissibility is asserted.

## Preservation and verifier changes

All accepted M2 mathematical definition/proof files, Integrity.lean, KernelAudit.lean, scientific M1/M2 specifications/result map, Lean toolchain and dependency pins are unchanged. The import-only umbrella exports Assembly.lean. All 56 prior Lean examples remain verbatim before the appended M3a checks.

The guard now pins the complete accepted M2 revision, freezes all 12 inherited result records and all 66 ordered bindings/stages/types, and checks accepted mathematical source hashes before building. It checks the new frozen M3 specification and representation companion against the immutable approval, including their contract metadata and part/stage layout. C has separate M3a and M3b parts; the future empty part remains deferred and fails coverage if M3b is activated without its proofs.

The 11 checker fixtures cover inherited binding replacement, stage changes and weakened types in all 12 groups, duplicate/forbidden/unsafe audit data, missing active declarations, frozen M3 metadata/layout, and conditional/concrete part separation. See [the complete full-index binding/type diff](bindings-and-types.patch), plus the candidate's [binding/type comparison](https://github.com/rois1995/CFD_Lean/blob/a70270c3f771e66bcaaebc18b8480c32f9606b1e/evidence/binding-type-diff.json) and [66 inherited comparisons](https://github.com/rois1995/CFD_Lean/blob/a70270c3f771e66bcaaebc18b8480c32f9606b1e/evidence/inherited-types.json). Exactly 18 accepted types are null for new claims; none of the 66 inherited types changes.

The complete owning-module inventory contains 672 qualified records. From 458 safe roots the audit reaches 20,297 declarations, precisely propext, Classical.choice and Quot.sound, and no unsafe declaration. All 139 unsafe compiler/executable auxiliaries and 75 metadata-only names remain visible as non-roots. Structure/transport definitions add compiler-generated records; none is hidden by name filtering. Per-root axiom queries skipped on non-roots are not evidence of verified executable code. Independent review of the additional classifications and closure is requested.

StatementChecks.lean has 73 examples: 56 inherited plus 17 new. The exact three-node cycle has independently supplied node values for all five components. Actual accepted Roe checks use an explicitly admissible rest state on a closed two-node metric example, distinguish compatible from incompatible boundary data, prove the incompatible residual is nonzero, and move that nonzero result to the corresponding node under simultaneous node/exterior relabeling. Generic expected-type checks cover all transported reindexings, arbitrary selected orientation reversals and zero area. The closed metric data are abstract test input; they are not a claimed tetrahedral construction.

## Fresh source-only replay

**Passed:** the worker completed the exact candidate replay from a clean detached checkout without .lake. All nine dependency source revisions were fetched afresh; both binary-cache controls were enabled and pinned widget assets were built locally. All 40 source hashes passed before and after the build. The full build, 11 fixtures, 73 Lean examples, 84 bindings, 66 inherited types and nine dependency pins passed. Only evidence/build.log changed in the fresh tracked checkout.

All five deterministic outputs match the exact candidate byte for byte. See [the comparison log](../../evidence/M3a-source-replay/audit-comparison.log), [complete replay logs](../../evidence/M3a-source-replay/), [replay record](../../evidence/M3a-source-replay/replay.json) and [archive checksums](../../evidence/M3a-source-replay/SHA256SUMS). Verify archive hashes with sha256sum -c SHA256SUMS from that archive directory. This was a worker reproduction, not an independent reviewer's run.

From a fresh clean full Git clone detached at the exact candidate, without .lake, place Lean/Lake 4.19.0, Git, Python 3, Node/npm, sha256sum and realpath on PATH and run:

```bash
bash scripts/reproduce.sh a70270c3f771e66bcaaebc18b8480c32f9606b1e /outside/checkout/M3a-replay-logs
```

The unchanged procedure fetches all nine pinned dependency sources, disables both binary-cache mechanisms, builds pinned ProofWidgets JavaScript locally, checks the candidate source hashes before regeneration, runs fixtures and full verification, and asserts exact agreement of all five deterministic outputs. The environment-dependent build transcript may differ. A full clone must include the historical accepted and approval objects used by the guard.

## Reviewer handoff and remaining work

Use Reviewer_Prompt.md for the ready-to-send scoped M3a request. Return a scoped verdict for I/R/O and conditional C, preservation of all 66 accepted M2 contracts, and audit/replay correctness. The worker's tests/replay do not supply independent scientific acceptance.

M3b's G/V and concrete C remain unfinished in the approved sequence. It must faithfully realize used-node embedding and exact interface/exterior multiplicities, derive the promised geometry and determinant-volume identities, and connect them to this exact residual. Full M3 acceptance requires both stages. No M4 boundary algorithm, time update, entropy/positivity repair, mixed-element extension or SU2 correspondence is submitted.
