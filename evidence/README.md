# Current M3a machine evidence

The current build.log, kernel-inventory.log, verification.json and SHA256SUMS report M3a's abstract assembly checkpoint on accepted full M2. M1/M2 acceptance remains tied to the immutable revisions and original review archives. M3 approval is in specifications/M3-approval.md; M3a independent acceptance remains pending.

The owning-module inventory contains 672 qualified records. Its 458 safe mathematical roots reach 20,297 declarations with precisely propext, Classical.choice and Quot.sound and no reachable unsafe declaration. All 139 unsafe compiler/executable auxiliaries and 75 metadata-only names remain visible as non-roots. Empty non-root axiom lists mean that query was skipped, not that compiler code was formally verified. The new structure/transport definitions introduce generated records; no unsafe declaration is reachable from accepted mathematical roots.

There are 84 active promises: all 66 accepted M2 bindings plus 18 new M3a bindings for I/R/O and conditional C. All 66 inherited ordered bindings, stages, elaborated types and accepted mathematical sources are protected against ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1. M3-G/V and the concrete M3-C part remain deferred to M3b. The frozen M3 specification and representation companion, metadata and part/stage layout are checked against approval commit 3189a603b3f6af953f0828d6b2e239320fd2cd20 before building.

StatementChecks.lean retains all 56 earlier examples and adds 17 (73 total). Actual Roe controls distinguish compatible and incompatible boundary data on a closed abstract metric example and transport the nonzero residual through simultaneous node/boundary relabeling. Generic controls cover all node/edge/boundary reindexings, reversal and zero area. Eleven checker fixtures include all 12 inherited M2 groups and M3 part/contract-metadata failures.

inherited-types.json compares all 66 accepted/current types. binding-type-diff.json includes all 84 claims, with precisely 18 null accepted types for new M3a claims. bindings-diff.patch includes the full current M3 result map against accepted full M2. Current machine metadata records M2 as independently accepted and M3a as pending; historical M2 pending fields in original archived evidence remain unchanged. A new worker cold replay must compare all five deterministic files byte for byte with the frozen M3a candidate; its final record will be under evidence/M3a-source-replay and reviews/M3a. A different cold-build transcript is expected.

No concrete tetrahedral geometry, mesh-validity checker, positive-volume theorem, boundary algorithm, time update, entropy/update-positivity or SU2 correspondence is claimed in M3a. The full approved M3 scope still requires M3b's derived geometry/volume results and composition with this same assembly.

## Historical M1 evidence narrative

# M1 verification evidence

- `dependency-build.log`: initial compilation of the independently checked-out pinned dependency sources, starting with empty dependency build directories; Lake release caching was not disabled. This run was intentionally interrupted after unused imports were removed.
- `first-project-build.log`: completes the remaining dependency source compilation, then records the first package compile before a proof-tactic import correction.
- `build.log`: the successful verification of the final M1 package. The original worker run disabled the mathlib update-hook cache only; it did not disable Lake release caching. A ProofWidgets release archive was downloaded by Lake. The original fully-source-only characterization was therefore incorrect.
- `axioms.log`: a fresh elaboration of Integrity.lean with warnings treated as errors; each project theorem prints its transitive axiom list.
- `verification.json`: compiler identity, complete project-theorem axiom lists and dependency-revision check count, generated only after all checks succeed.
- `SHA256SUMS`: hashes of the package sources, contracts, bibliography, full reference metadata inventory and verification command. Compare these with the frozen Git revision; rerunning verification regenerates the snapshot.

Run `python3 scripts/verify.py` with Lean/Lake 4.19.0 on PATH, then `sha256sum -c evidence/SHA256SUMS`. For a fully fresh source build, use the tested procedure now published in the root README and reviews/M1/reviewer/ReproduceM1.sh. It disables both cache mechanisms and builds the pinned widget assets locally. The reviewer independently completed two fresh source-only reproductions; see reviews/M1/logs/clean-pass-build.log and reviews/M1/logs/portable-replay/build.log. Current worker verification may reuse the already built local dependency artifacts and must not be described as an additional independent fresh source build.

Integrity checks include nonempty admissible states, zero area, zero density exclusion, gamma = 1 pressure collapse, and a moving 1D state with independently calculated flux (24, 92, 228). They are exact-real kernel checks, not compiled-solver or floating-point tests.

The checker accepts only the standard foundational axioms propext, Classical.choice and Quot.sound. It rejects any other transitive axiom and missing/extra theorem-audit coverage, and verifies each dependency's HEAD and tracked-source cleanliness. The axiom parser has positive and negative self-checks.

The final independent decision is Accept for mathematical revision 0a88e36b3810cd5adc3881db526ca8a35f81afbb; follow-up 180ff1be1aa95d943574efd9c05cd4de320a88b6 closed both original conditions. See reviews/M1/CFD_Lean_M1_Acceptance.md. The original reports and snapshots are historical records. Build success and axiom inspection do not establish that the selected mathematical specification is the intended physical method or that a CFD solver implements it.
