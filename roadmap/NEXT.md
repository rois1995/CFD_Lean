# Roadmap: next steps

This file contains work that is actionable or close enough to guide near-term implementation. Long-horizon ideas
belong in `FUTURE.md`; persistent architectural rules belong in `PRINCIPLES.md`.

Status date: 2026-11-26.

## Priority 0 - close the review / trust backlog

1. Complete the independent implementation review of M5.
2. Complete independent review of Burgers B0--B4, E0 and E0b.
3. Human-review the trusted Burgers statements that currently have only agent review.
4. Resolve the open B0 trusted-boundary question: the current trusted B0 statements do not separately state the
   assembled `ZMod N` scheme B0-S.

The mathematics is moving faster than independent acceptance. Closing this gap is important before many additional
solver layers accumulate.

## Priority 1 - non-uniform fixed 1D finite volume

Use a non-uniform fixed Burgers mesh as the next architectural stress test before ALE or AMR.

Target components:

1. Explicit 1D cell geometry: cell measure, centroid, left/right faces and face-to-centroid distances.
2. Scalar FV update with cell-dependent volumes rather than one global `dx`.
3. Volume-weighted conservation:
   `sum_i volume_i * u_i`.
4. Geometry-aware MUSCL reconstruction using distance-normalized differences and actual face offsets.
5. Proof that the current uniform formulas are recovered as a specialization.
6. Local CFL / bounds / TVD statements and a clear account of which B1--B3 lemmas remain reusable.
7. Avoid premature replacement of every current `Fin n` API: generalize only what the milestone actually exercises.

Success criterion: the extension should require local geometric generalization, not a rewrite of flux, entropy and time
composition layers.

## Priority 2 - E1 machine arithmetic strategy

The executable already uses the same kernel shape at `Real` and `Float`, but only the real-arithmetic refinement is
proved.

Before committing to a large floating-point development, write a small design proposal comparing viable routes:

- a formal IEEE model and a theorem relating it to the executable operations;
- interval/enclosure arithmetic for a reference mode;
- reproducible/exact accumulator techniques for selected reductions;
- external verified arithmetic kernels with a narrow trusted/refinement interface.

The required deliverable is a precise statement of what a future `Float` result could be certified to mean.

## Priority 3 - verified-run provenance and basic solver output

These are low-risk executable features that prepare the solver for reference simulations without changing numerical
mathematics.

1. Add step- or time-based solution snapshots, not only final `--dump`.
2. Define a machine-readable run manifest containing at least commit, scheme, parameters, arithmetic mode and input
   hashes.
3. Keep diagnostics separate from solution-field output.
4. Plan checkpoint/restart metadata so a restarted run can retain provenance.

The driver itself can remain outside the strongest proof boundary initially; the format should nevertheless be
designed so later certification can attach to it.

## Priority 4 - remaining mathematical Burgers extensions

Candidates, to be proposed/frozen separately:

- fully discrete entropy inequality;
- sharper CFL bounds for B1 and B3;
- limiters beyond the current minmod region (e.g. MC, superbee);
- accuracy/order statements;
- eventual convergence statements;
- adapter between the periodic scalar operator and `CFDLean.Num.antisymmetric_pairFlux`;
- B5 paper correspondence once the reference sources are chosen.

## Priority 5 - M6 composition

Continue the original Euler roadmap with multi-step evolution on top of M5
(`specifications/M2-proposal.md`).

Keep the generic time-evolution interfaces compatible with future variable-step and implicit methods.

## Priority 6 - numerical-core and paper housekeeping

- Narrow `CFDLean.Num.Basic`'s broad `import Mathlib` where practical.
- Move remaining generic JST results (P1-5.4b, P1-5.8) into the numerical core when justified.
- Add the archive pointer note in JST_Paper_Lean.
- Continue paper-1 gaps that need new mathematics, including non-affine mixed cells and simplex integration.
- Keep the theorem catalog and raw-type evidence synchronized with every milestone.
- Shorten the root README by moving historical detail into `references/` where useful.
