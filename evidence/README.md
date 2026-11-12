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
