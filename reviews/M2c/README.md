# M2c review checkpoint

Worker submission, 2026-11-13. M1, M2a and M2b are independently accepted at their immutable revisions. M2c (M2-E/D/O) is awaiting independent scientific review; M2d and the complete M2 numerical flux remain unfinished.

- Frozen mathematical candidate: [`6ee9d53e79e0c6f11e75b1b387c21256572d0fcd`](https://github.com/rois1995/CFD_Lean/commit/6ee9d53e79e0c6f11e75b1b387c21256572d0fcd).
- Accepted inherited J/A/R/L baseline: `c92c0f66360f85c0a3339ab9b30fc00c39ee5f93`; [independent M2b acceptance and original review](../M2b/Acceptance.md).
- Approved scientific contract: [M2.md](https://github.com/rois1995/CFD_Lean/blob/6ee9d53e79e0c6f11e75b1b387c21256572d0fcd/specifications/M2.md), unchanged from `79fd2a03d7b15325c56a88ec83991b4fb4f498bb`.
- [Qualified declaration map](https://github.com/rois1995/CFD_Lean/blob/6ee9d53e79e0c6f11e75b1b387c21256572d0fcd/specifications/M2-results.json), [source/proof traceability](https://github.com/rois1995/CFD_Lean/blob/6ee9d53e79e0c6f11e75b1b387c21256572d0fcd/references/M2c.md), [expected-type checks](https://github.com/rois1995/CFD_Lean/blob/6ee9d53e79e0c6f11e75b1b387c21256572d0fcd/StatementChecks.lean).

## Scope and statements

| Result | Bindings | Delivered statements |
| --- | --- | --- |
| J/A/R/L | 37 inherited | Accepted state chart, physical derivative, Roe averages and positivity, parameter maps/secant identity and equal-state limit. Names, stages, types and definition/proof sources are fixed against c92c0f6. |
| M2-E | 13 new | Derived sound-speed parameters; shifted cubic; acoustic/contact/shear eigenrelations; projector algebra, sum, ranges and ranks; exact 1+3+1 dimensions; an actual complete five-vector eigenbasis; two-dimensional tangent plane, tangent-basis existence and contact/shear spanning for every tangent basis; spectral reconstruction. |
| M2-D | 2 new | Absolute-speed action on eigenvectors and equality with R diag(abs speeds) R-inverse in every complete eigenbasis. |
| M2-O | 6 new | Matrix/shift reversal, acoustic-projector swapping and convective preservation, speed relabeling, dissipation reversal invariance and state-swap invariance. |

The existing accepted supporting theorem `CFDLean.Roe.roeMatrix_swap` supplies symmetry of the actual matrix under state swapping; the new typed checks pair it with dissipation symmetry. All supporting declarations, including generated logical declarations, remain in the owning-module inventory.

The physical results use common gamma > 1, both M1-admissible endpoints and a Euclidean unit normal. Sound-speed positivity and its square relation come from accepted M2b. The generic algebra assumes no spectral conclusion or completeness. Each acoustic range is the span of a nonzero displayed vector. The convective space is the kernel of a proved surjective two-coordinate map, giving dimension 5-2=3. Projector spanning and eigenspace independence construct a complete basis. Arbitrary tangent-basis spanning is proved separately.

Dissipation is defined by the approved polynomial projectors and absolute characteristic speeds. It contains no chosen eigenbasis. The conjugation theorem uses the basis coordinate-to-state equivalence as R and its inverse as R-inverse. A cubic argument also proves the possible real eigenvalues rather than assuming them for an arbitrary eigenbasis. Zero characteristic speeds remain admissible; only sound speed or its square is inverted. No Euclidean self-adjointness, positive semidefiniteness, entropy correction or update positivity is asserted.

## Inheritance and review controls

The M2b review has no outstanding acceptance condition. Its next-stage audit finding is addressed: scripts/verify.py now freezes all four accepted IDs J/A/R/L and all 37 ordered bindings/types and mathematical source hashes against c92c0f6. Regression fixtures reject binding substitutions, stage changes and weakened types for each ID. The import-only umbrella adds the new spectral module; accepted definition/proof files are unchanged.

The [literal full Git diff](bindings-and-types.patch), [binding-file patch](https://github.com/rois1995/CFD_Lean/blob/6ee9d53e79e0c6f11e75b1b387c21256572d0fcd/evidence/bindings-diff.patch), [accepted/current types](https://github.com/rois1995/CFD_Lean/blob/6ee9d53e79e0c6f11e75b1b387c21256572d0fcd/evidence/binding-type-diff.json) and [inherited-type comparison](https://github.com/rois1995/CFD_Lean/blob/6ee9d53e79e0c6f11e75b1b387c21256572d0fcd/evidence/inherited-types.json) expose every claimed change. Null accepted types identify the 21 new M2c claims awaiting review.

StatementChecks.lean has 41 Lean examples. They include literal N/projector/absolute-speed definitions, literal acoustic/contact/shear eigenvectors, ranks, complete-basis existence, arbitrary-basis conjugation and orientation/state-swap interfaces. Exact controls include a stationary convective zero mode, a sonic acoustic zero mode and the genuinely oblique Euclidean unit normal (2,3,6)/7. The count is not a one-to-one independent specification of every binding; scientific review of the new types and definitions is still required.

## Verification

The local build, 58 active theorem bindings, all 37 inherited types/sources, 41 Lean examples, nine Python fixtures and nine dependency revisions pass. The inventory has 461 qualified records and 354 safe mathematical roots, reaching 20,068 kernel declarations. Only propext, Classical.choice and Quot.sound occur as axiom leaves, with no reachable unsafe declaration. The 71 unsafe executable/compiler records and 36 metadata-only names are explicitly reported as non-roots; empty per-row axiom fields on non-roots do not verify executable code.

The Lean/mathlib/dependency pins, M1 specification and approved M2 contract are unchanged. Original worker and independent review evidence for earlier stages is retained unmodified.

The fresh pinned-source replay of the exact candidate **passed**, starting from a clean detached checkout without `.lake`. Both binary-cache mechanisms were disabled, all nine dependency source revisions were fetched and the pinned widget assets were built locally. All 30 source hashes passed before and after the build. The full build, nine Python fixtures, 41 Lean examples, 58 theorem bindings, all 37 inherited types and nine dependency pins passed. Only `evidence/build.log` changed.

The [comparison log](../../evidence/M2c-source-replay/audit-comparison.log) records exact matches for all five deterministic outputs. The [complete replay logs](../../evidence/M2c-source-replay/), [replay record](../../evidence/M2c-source-replay/replay.json) and [log checksums](../../evidence/M2c-source-replay/SHA256SUMS) preserve the results. This was a worker reproduction, not an independent reviewer run.

To reproduce, put Lean/Lake 4.19.0, Git, Python 3, Node/npm, sha256sum and realpath on PATH. From a fresh clean checkout without `.lake`, with an external log directory:

```bash
git checkout --detach 6ee9d53e79e0c6f11e75b1b387c21256572d0fcd
bash scripts/reproduce.sh 6ee9d53e79e0c6f11e75b1b387c21256572d0fcd /outside/checkout/M2c-replay-logs
```

Use a normal full Git clone so the immutable accepted/approved revisions are available to the guard. The script refuses the wrong or dirty checkout, checks the original source hashes before regenerating evidence and asserts exact comparisons. Verify archived replay file hashes from `evidence/M2c-source-replay` with `sha256sum -c SHA256SUMS`.

## Reviewer handoff and remaining work

Use [the ready-to-send reviewer prompt](Reviewer_Prompt.md). Independently review E/D/O, preservation of all 37 inherited contracts, full domain assumptions, completeness, any-basis absolute-speed equivalence and orientation. Inspect the extended inherited guard and exact type checks, independently replay the source procedure, compare deterministic evidence and return a scoped M2c verdict with declaration/file references.

M2-F1/F2/F3/F4/C remain unimplemented with empty deferred bindings and no sorry/admit placeholders. No final integrated numerical flux, all-wave upwinding proof, positivity counterexample, mesh assembly or SU2 correspondence is claimed here.
