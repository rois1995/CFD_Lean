# Burgers implementation review: B0-B4, B3b, E0, E0b, E0c

Date: 2026-11-26. Reviewed revision: `4c77f6e145f1f5d8cdd812a02dce2e7324d179c0` (`develop`).

## Reviewers and authority

Three AI review agents (Claude Opus 5.5) did the review, each with read-only access to the repository. None of them
wrote the reviewed code or proofs. Their scope:

| Reviewer | Milestones |
| --- | --- |
| 1 | B0, B1, B2 |
| 2 | B3, B3b, B4 |
| 3 | E0, E0b, E0c and the `burgers1d` driver |

This is not a human review. Before the review finished, the repository owner wrote:

> I would accept your findings so do not worry

On that basis the verdicts below are recorded as the independent implementation acceptance of these milestones. The
human review of the trusted Burgers statements (roadmap Priority 0, item 2) stays open.

## Verdicts

| Milestone | Verdict | Condition |
| --- | --- | --- |
| B0 | Accept | none |
| B1 | Accept | none |
| B2 | Accept | none |
| B3 | Accept | none |
| B3b | Accept | none |
| B4 | Accept | none |
| E0 | Accept | none |
| E0b | Accept with condition | Record that E0c-X supersedes E0b-X. Done in [amendment 1](../../specifications/Burgers-E0b-amendment-1.md). |
| E0c | Accept | none |

There are no other mandatory findings.

## What the reviewers checked

- **Contract fidelity.** Each frozen Lean statement was compared with the bound declaration: same hypotheses, same
  conclusions, same constants. The constants include the CFL limits `1/2` (B1), `2·max(|m|,|M|)` (B2), `3/2` and
  `4+2θ` (B3, B3b) and the limiter constants `θ = 1, 2, 2, 2, 5/4`. Result maps and catalog entries agree, and every
  bound name exists.
- **Mathematics.** The reviewers derived the following by hand:
  - the Rusanov flux and its monotonicity;
  - the finite-volume orientation and the Harten incremental coefficients;
  - the SSPRK2 and SSPRK3 Shu-Osher forms;
  - the MUSCL face states and each limiter form and range;
  - the exact overshoot example `(1/32, 1/160, 147/160, 167/160)`;
  - the B4 entropy pair, the entropy-conservative split of the Rusanov flux and the sign of the entropy inequality.

  Exact-rational random tests found no violation. B0-B2 had 400 cases and B3/B3b had 30,000 cases (5 limiters ×
  Euler, SSPRK2 and SSPRK3 at the frozen CFL limits). These tests are evidence only.
- **Trusted boundary.** Each bridge proves its trusted statement about the trusted definitions. Each
  `Challenges/Burgers*.lean` file restates exactly the bridge theorems. Each comparator config lists exactly those
  names and allows only `propext`, `Quot.sound` and `Classical.choice`. The pinned hashes of the contracts, trusted
  files and challenges match.
- **Execution layer.** The array kernels use proof-carrying indices, with no `get!` and no default fallback. The
  periodic index arithmetic holds for `n = 1`. The kernels contain no `Float`; only the two frozen `Float` instances
  do. The ℝ instance is Mathlib's arithmetic. The driver maps each option to the right kernel, and every driver note
  says that `Float` arithmetic is not verified.
- **Hygiene.** There is no `sorry`, `axiom`, `unsafe`, `implemented_by`, `extern`, `native_decide` or `opaque` in the
  reviewed modules. The intended `sorry` holes in `Challenges/` are the only exception.

## Machine checks

Run locally on the reviewed revision:

- `lake build` (18575 jobs): passed.
- `python3 -m unittest discover -s scripts -p test_verify.py`: 75 tests, passed.
- `python3 scripts/catalog.py --check`: passed.

The full verifier, the kernel audit, the evidence comparison and `burgers1d` run in Integration CI on the acceptance
PR. The paranoid comparator for all trusted challenges runs on the same PR through the `paranoid` label. The PR
records both results.

## Follow-ups made with this record

- **E0b amendment 1.** It records that `--muscl` now runs the unlimited scheme and that the E0b minmod run is
  `--limiter minmod`.
- **B0-S decision.** B0 gets no dedicated trusted challenge. A Mathlib-only statement cannot name the implementation's
  `grid` or `step`, so the challenge would only restate B0-C, B0-K and B0-T. Instead,
  `CFDLean/Schemes/Burgers/GridControls.lean` proves `grid.next i = i + 1` and `grid.prev i = i - 1` and the explicit
  update formula. It also has an exact three-cell control that fixes the orientation. The reviewers checked
  `zmodGrid = Equiv.addRight 1` by reading it.
- **B1 proof map wording.** The Lean bounds proof needs CFL `1/2`. Only the coefficient lemma holds up to `2/3`.
- **`lakefile.toml` comment.** It now names all the modules that `Main.lean` imports.

## Optional remarks not acted on

These remarks would change accepted or frozen sources, so they are left for a later scoped change:

- `CFDLean/Discrete/Periodic/Muscl.lean:56`: the docstring says "B3-R" for a B3-L result.
- `CFDLean/Entropy/Scalar/Periodic.lean:14,16`: `variable {I : Type*}` is declared twice. This is harmless.
- `specifications/Burgers-B3b.md:24`: the name "Fromm's scheme" is loose for the unlimited central-slope scheme.
- The E0 contract's statement table lists 7 trusted statements, and the file has 10. The extra 3 only add guarantees.
- `Float` robustness for E1: van Leer and van Albada can overflow for differences of about `1e154`, and
  `Scalar.max` on `Float` can hide a NaN. Neither case can happen with the driver's initial condition.
- The CFL constants are sufficient, not sharp, as the contracts say.
