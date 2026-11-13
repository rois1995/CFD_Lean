# Current M2c machine evidence

The current build.log, kernel-inventory.log, verification.json and SHA256SUMS report the cumulative M2a/M2b/M2c candidate. M1, M2a and M2b acceptance remain attached to their immutable revisions; see reviews/M1, reviews/M2a/Acceptance.md and reviews/M2b/Acceptance.md. M2c is independently accepted; see reviews/M2c/Acceptance.md. M2d is the next approved stage.

The audit inventories 461 qualified records. Its 354 safe mathematical roots reach 20,068 declarations with precisely propext, Classical.choice and Quot.sound and no reachable unsafe declaration. The 71 unsafe compiler/executable records and 36 metadata-only names remain visible as non-roots. Empty non-root axiom lists mean the per-root query was skipped, not that executable code was verified.

All 58 active J/A/R/L/E/D/O bindings, all 58 inherited types/sources and all nine dependency pins are checked. StatementChecks.lean provides 41 expected-interface and exact examples, including literal spectral formulas, acoustic/contact/shear vectors, arbitrary-basis conjugation, zero-speed and oblique-unit-normal cases. Nine Python fixtures include binding/stage/type regressions across all four accepted inherited IDs.

inherited-types.json now compares all 58 accepted types with 6ee9d53. binding-type-diff.json exposes every current type; null accepted types mark the 21 new M2c claims. bindings-diff.patch is the complete qualified binding-file diff from that accepted revision. The fresh replay compares these and both full audit outputs with the exact candidate byte for byte. A different cold-build transcript is expected. Worker cold replay evidence is archived separately; it cannot supply independent scientific acceptance.

M2-F1/F2/F3/F4/C remain deferred, with no numerical flux or positivity witness claimed yet.

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
