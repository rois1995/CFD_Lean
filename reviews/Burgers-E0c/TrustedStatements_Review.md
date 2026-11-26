# Burgers E0c: review of the trusted statements, the limiter kernel and the driver

Date: 2026-11-26. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed files and
did not check the refinement proofs. This is not a human review and not the independent implementation review.

Reviewed: `CFDLean/Verification/BurgersE0cChallenge.lean`
(sha256 `ef191f896ce59f9b26aa20ab06c3e12d791d8efd179cee4456cd40ce1193cdb4`), `CFDLean/Exec/LimiterKernel.lean`
(sha256 `ca3223409971be33a593ed31d8e28f64a55e74a083711393ed96db7c9bf32e50`), `CFDLean/Exec/RealScalarSign.lean`,
`Main.lean` (first version). Reference: `specifications/Burgers-E0c.md`; comparison with the E0b and B3b trusted files.

## Verdict

**Faithful, with remarks.** No blocker in the Lean files. One documentation item was marked "should fix"; it is fixed.

## Checks made by the reviewer

- By hand for real numbers: the kernel MC and superbee slopes equal the classical ones in every sign case;
  `maxmodSame` only receives two numbers of the same strict sign or two zeros; no division by zero in the van Leer and
  van Albada branches; the array kernels have the MUSCL form with periodic indices and the Shu-Osher steps.
- Exact test: with rational instances of `Scalar` and `ScalarSign`, the Euler, SSPRK2 and SSPRK3 kernels for all six
  choices on 61 arrays of size 0, 1, 2, 3, 6, 7, and 726 slope pairs, against an independent Python `Fraction`
  implementation in Sweby ratio form: 1824 of 1824 exact matches. Mutated versions are detected.
- `pp.explicit`: every trusted statement uses `instScalarReal` and `instScalarSignReal` (the only real instances);
  every operation in the trusted definitions is Mathlib's; `L ≠ Limiter.none` is the kernel constructor.
- `slopeOf` and `thetaOf` agree with the B3b trusted file; `musclEulerStep` is the E0b one with a slope function.
- Quantifiers and hypotheses as in the contract; for `none` only refinement and the sum are claimed; nothing vacuous.
- Program: all requested runs behave as documented (unlimited run leaves the initial bounds and its total variation
  grows; each limiter is named with the right proved range; "outside" is printed for `cfl = 0.3` with van Leer; bad
  limiter name exits 1; NaN exits 2). An independent Python float implementation matches all printed digits for the
  six choices at `N = 200`, 600 steps, `cfl = 0.12`.

## Findings

1. **Should fix (fixed):** `README.md` still showed `burgers1d 200 200 0.15 --muscl` as the E0b minmod example; that
   command now runs the unlimited scheme.
2. Remark (changed): the usage text did not say that `--muscl` meant minmod before.
3. Remark (partly changed): the "inside/outside" decision uses the given `cfl`, not the rounded `dt`; the note
   mentioned only bounds. The note now names bounds and total variation.
4. Remark: the van Albada slope is the clipped one (0 for `ab ≤ 0`), as in B3b.
5. Remark: the sum and total-variation statements get their meaning from the E0 trusted statements.
6. Remark: no trusted statement for the Euler and SSPRK2 runs or for "the minmod choice is the E0b kernel"
   (consistent with the contract table).
7. Information, `Float`: a NaN difference gives the slope 0 or a finite slope for the limiters (NaN for `none`), and
   still spreads through the fluxes; `ab` overflows above about `1e154` (van Leer gives inf, van Albada NaN) and
   underflows to 0 for tiny differences (slope 0).

## Changes after the review

`README.md` and `references/Burgers-E0b.md` use `--limiter minmod` in the E0b examples. `Main.lean`: usage text and
note lines reworded. `references/Burgers-E0c.md`: notes added. The trusted files did not change.

## Not checked by the reviewer

The refinement and bridge proofs, `lake comparator`, more than one SSPRK3 step in exact arithmetic.
