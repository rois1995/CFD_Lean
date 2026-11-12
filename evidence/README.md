# M1 verification evidence

- `dependency-build.log`: initial compilation of the independently checked-out pinned dependency sources, starting with empty dependency build directories. This run was intentionally interrupted after unused imports were removed.
- `first-project-build.log`: completes the remaining dependency source compilation, then records the first package compile before a proof-tactic import correction.
- `build.log`: the successful verification of the final M1 package. No dependency compiled caches were copied or fetched.
- `axioms.log`: a fresh elaboration of Integrity.lean with warnings treated as errors; each project theorem prints its transitive axiom list.
- `verification.json`: compiler identity, complete project-theorem axiom lists and dependency-revision check count, generated only after all checks succeed.
- `SHA256SUMS`: hashes of the package sources, contracts, bibliography, full reference metadata inventory and verification command. Compare these with the frozen Git revision; rerunning verification regenerates the snapshot.

Run `python3 scripts/verify.py` with Lean/Lake 4.19.0 on PATH, then `sha256sum -c evidence/SHA256SUMS`. For a fully fresh source build, start from a new checkout without `.lake`, preserve the committed manifest, set `MATHLIB_NO_CACHE_ON_UPDATE=1`, and do not run a cache-fetch command.

Integrity checks include nonempty admissible states, zero area, zero density exclusion, gamma = 1 pressure collapse, and a moving 1D state with independently calculated flux (24, 92, 228). They are exact-real kernel checks, not compiled-solver or floating-point tests.

The checker accepts only the standard foundational axioms propext, Classical.choice and Quot.sound. It rejects any other transitive axiom and missing/extra theorem-audit coverage, and verifies each dependency's HEAD and tracked-source cleanliness. The axiom parser has positive and negative self-checks.

Scientific acceptance and an independent evaluator review remain pending. Build success and axiom inspection do not establish that the selected mathematical specification is the intended physical method or that a CFD solver implements it.
