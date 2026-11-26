# Burgers E0b: review of the trusted statements, the MUSCL kernel and the driver

Date: 2026-11-26. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed files and
did not check the refinement proofs. This is not a human review and not the independent implementation review.

Reviewed: `CFDLean/Verification/BurgersE0bChallenge.lean`
(sha256 `ef7da3d912c415d2af27405a5b3172f8eb8a133eaaabb680435f88411813b5af`), `CFDLean/Exec/MusclKernel.lean`
(sha256 `adf7819d7da436a969a52c76443f61b2661691da03f2d8dd7086f8aa9acac380`), `Main.lean`.
Reference: `specifications/Burgers-E0b.md`; comparison with the E0 and B3 trusted files.

## Verdict

**Faithful, with remarks.** No blocker and nothing that had to be fixed before the merge.

## Checks made by the reviewer

- Kernel: the code is the contract listing. Elaborated terms inspected: slope, face states, flux arguments at each
  interface, the Shu-Osher form. The index `(i + n - 1) % n` cannot underflow.
- The comparison-free minmod equals the textbook minmod in every sign case and with zeros (by hand).
- Exact test: with a rational-number instance of the kernel arithmetic, the Euler, SSPRK2 and SSPRK3 kernels on arrays
  of size 0, 1, 2, 3, 6, 7 match an independent Python `Fraction` implementation digit for digit.
- Trusted file: same scheme as the B3 trusted file with `next i = i + 1` on `Fin n`; local names are not shadowed by
  the kernel names; every arithmetic operation, `min`, `max` and `|·|` in the trusted definitions is Mathlib's (the E0
  finding is fixed); every kernel call uses `instScalarReal`; hypotheses exactly as in the contract; the transfer
  statements hold for the empty array; none is vacuous; the pinned hashes match.
- Program: four runs and bad-argument cases behave as documented; the note line states the hypothesis of the theorem
  (`cfl ≤ 1/6` is `6 · dt · max(|m|, |M|) ≤ dx` for the driver's `dt`). An independent Python float implementation
  matches all printed digits for `200 200 0.15 --muscl` and `200 200 0.4 --muscl`.

## Findings (all remarks)

1. The sum and total-variation statements use the E0 diagnostics and rely on the E0 trusted statements for their
   meaning. Sound (same functions, instance and pinned files), but the meaning is in another file.
2. `dx ≠ 0` in the sum statement is not necessary over `ℝ`.
3. `musclSsprk2StepArray` and the Euler run have no trusted statement (consistent with the contract table).
4. The driver printed the same note inside and outside the proved range, and the word "need" read as a necessary
   condition. **Changed after the review:** the note now says "the bounds are proved for cfl <= ..." and whether the
   run is inside or outside that range.
5. The usage text said "second-order"; second-order accuracy is not proved. **Changed after the review.**
6. Information: with `Float` the kernel minmod is not symmetric for NaN and does not propagate it; a NaN cell still
   spreads through the face states and the driver's finiteness check reports it.

## Not checked by the reviewer

The refinement proofs, the bridge proofs, `lake comparator`, `scripts/verify.py`, a full build, CI and catalog changes.
