# Independent M3a review

**Verdict — Accept M3a (M3-I/R/O and conditional M3-C). No blocking findings or outstanding acceptance conditions. Full M3 remains pending.**

Candidate `a70270c3f771e66bcaaebc18b8480c32f9606b1e`. Checkpoint `54ae08dd1fca40d0b1b8eccabe91f9435068eb8b`. Accepted M2 baseline `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`. M3 approval/freeze `3189a603b3f6af953f0828d6b2e239320fd2cd20`.

## Scientific findings

All names below have prefix CFDLean.Assembly and are in CFDLean/Discretization/Assembly.lean.

- `Interfaces` has tail/head, a distinct-endpoint proof and an exterior owner. It includes no closure, cancellation, volume or admissibility certificate. Edge and boundary types are finite for local assembly; global balance also requires the node type finite. The abstract interface allows multiple distinctly identified records between the same endpoints, which preserves generic cancellation. M3b must supply the approved unique concrete records.
- `incidence`, `incidence_tail/head/other`, `incidence_eq_one/neg_one`, `incidence_sum`, `incidence_smul` and `residual_outgoing` implement exact signed scatter and filtered enumeration. Boundary owners contribute once. The residual takes ordinary finite real vectors, including the accepted five-coordinate conserved-transfer layout, with no new state arithmetic or volume/time/area multiplier.
- `global_balance` exchanges finite sums, uses incidence_sum and sums each owner indicator once. Arbitrary vector transfers are permitted. Cancellation and closure are conclusions/irrelevant respectively, never premises. `roe_global_balance` specializes this same residual to `roeTransfer`, whose definition directly encodes the actual accepted numericalFlux at endpoint states and the supplied area vector. Its one integrated area factor remains inside M2.
- `outwardTransfer` independently evaluates the head using reversed endpoints and area. `encoded_reverse` reuses accepted M2 reversal, and `outwardTransfer_eq` identifies that value with the stored signed transfer. This supplies the physical orientation interpretation of the scatter, separately from its purely algebraic cancellation. `roeTransfer_zero` retains zero area.
- `Interfaces.reverse` selects any decidable subset of edges. `residual_reverse` negates exactly their transfers while swapping their endpoints. `roe_residual_reverse` derives this negation for the actual accepted flux. Neither result restricts reversal to all edges or one predefined ordering.
- `Interfaces.reindex`, `residual_reindex` and `roe_residual_reindex` quantify over arbitrary node/edge/boundary equivalences. Endpoints and exterior owners are pushed forward; states, areas and boundary data are pulled back using the correct inverse equivalences. The equality is evaluated at the transported original node. Boundary labels retain their identities through B.
- `physicalTransfer` is the actual M1 physicalFlux as a real-linear area map, proved from accepted physicalFlux_add/mul. `residual_map` commutes this map with the same assembly. `constant_state_residual` combines it with actual M2 consistency to give physicalFlux on metricDefect. `constant_state_closed` then uses an explicit zero-defect hypothesis. Compatible boundary transfers are built into these statements. These stronger raw algebraic types include the approved physical regime; physical use still requires common gamma>1 and admissible states.

## Scope and exact controls

All 18 new bindings implement M3-I/R/O and the conditional M3-C part. M3-G, M3-V and the concrete M3-C part have empty future-stage bindings and remain deferred. The abstract zero-defect hypothesis is appropriate here. It supplies no derived tetrahedral geometry or full-M3 acceptance.

The 17 appended Lean examples retain all 56 earlier examples verbatim. New controls include a nonzero five-component interface, three independently specified cycle-node residuals, an explicitly admissible actual-Roe resting state on a closed abstract metric pair, compatible boundary data giving zero, and incompatible data yielding the nonzero mass residual (1,0,0,0,0). Simultaneous node/exterior relabeling transports that nonzero residual to the corresponding node. These tests avoid relying exclusively on zero or empty inputs. The closed pair is abstract metric input and is correctly presented as such.

## Preservation, freeze and audit

Independent Git-blob comparisons found every accepted M2 mathematical source, Integrity.lean, KernelAudit.lean, M1/M2 scientific specifications/result map, Lean toolchain and Lake configuration/manifest unchanged. All 66 accepted elaborated theorem types remain identical. The full-index diff of M2/M3 binding maps and verification.json matches the checkpoint's literal patch byte for byte. All 56 prior statement examples are preserved as an exact prefix.

M3.md and M3-representation.md are byte-identical to the immutable approval snapshot. The companion includes the reviewed faithful embedding/incidence, exact concrete multiplicity and determinant-volume meaning requirements. M3-results.json freezes contract metadata and stage/part layout against that snapshot. C has separate M3a and M3b parts. Activating M3b requires the empty future parts to be populated; a conditional theorem cannot satisfy the concrete part through its existing binding.

The authorization record transcribes Andrea's approval and identifies its approved scope. As with earlier approval transcripts, the original platform export is not independently authenticated by this review. The explicit recorded decision and reviewed scope are consistent.

KernelAudit.lean is unchanged. Its owning-module inventory includes structure constructors/projections/recursors, transport/reverse definitions, generated compiler declarations and metadata. In Assembly alone, the submitted classification has 58 safe roots (37 theorem records, 18 definitions, one inductive, constructor and recursor), 68 unsafe compiler records (58 definitions and ten compiler-generated axiom records), and 39 metadata-only names. The generated unsafe _elambda/_cstage family is distinguished from mathematical axioms. Each safe root must still pass transitive permitted-axiom and unsafe-reachability checks. Per-root queries skipped on unsafe non-roots do not certify compiled executable correctness.

**Next-stage finding, nonblocking for M3a.** The current inherited baseline protects M2's 66 bindings/sources, as required for this submission. Before submitting M3b, extend inheritance to the newly accepted 18 M3a bindings, their exact stages/parts/types and Assembly.lean as well. Preserve separate C parts and full diffs. Otherwise a future safe theorem replacement or change to the assembly definition could pass the existing M2-only inheritance guard. References: scripts/verify.py, check_inherited/check_m3_layout and specifications/M3-results.json.

## Next permitted work

After recording the scoped M3a acceptance, the already approved M3b stage may proceed under the frozen M3 specification and representation companion. It must derive G/V from the selected conforming tetrahedral median dual and instantiate this exact assembly/constant-state interface. Preserve M3a as described above. Full M3 remains pending until those concrete results receive independent review. No additional boundary algorithm, time update, entropy/positivity repair or SU2 correspondence is approved by this review.

## Independent source-only replay and controls

Authenticated Git objects reconstructed the exact candidate tree b4abf2a7100e5a9734d3b2226099950ad5cfad6d, checkpoint tree 261da4ad3e2696e6a91765e09fd219385e83b464, approval and inherited baseline. From a clean detached candidate without .lake, I ran the submitted reproduce.sh unchanged with official Lean/Lake 4.19.0 and LEAN_NUM_THREADS=8. All nine dependencies were fetched as fresh pinned source checkouts, both cache controls were enabled, and pinned widget JavaScript was built locally. The procedure exited 0. The cold build, all 11 checker fixtures and all 73 explicit Lean examples passed. All 40 source checksum entries passed before and after regeneration. Only evidence/build.log differed in tracked files.

All five deterministic outputs matched both the candidate Git blobs and checkpoint archive byte for byte. Checkpoint archive checksums also passed independently. The reproduced audit contains 672 qualified records, all 84 bindings and all 66 inherited types. The separate reviewer traversal follows types, values, inductive constructors and recursor rules. It found 458 safe roots, 20,297 reached declarations, only propext/Classical.choice/Quot.sound and no reachable unsafe constant. The generated auxiliary classifications described above are therefore also freshly reproduced, with their safety significance checked through the separate traversal.

Two extra reviewer Lean examples connect global balance to the independently evaluated outward endpoint fluxes, and apply the common-state metric-defect result to independently supplied boundary data satisfying compatibility. Earlier reviewer secant and physical-derivative-limit checks also pass. The separate file elaborates with warnings treated as errors. The remote repository was not modified. These results support scoped M3a acceptance and supply no M3b geometry proof.
