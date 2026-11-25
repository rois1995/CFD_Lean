# Burgers E0: review of the trusted statements, the kernel and the driver

Date: 2026-11-26. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed files and
did not check the refinement proofs. This is not a human review and not the independent implementation review.

Reviewed (first version): `CFDLean/Verification/BurgersE0Challenge.lean`, `CFDLean/Exec/Kernel.lean`,
`CFDLean/Exec/RealScalar.lean`, `Main.lean`. Reference: `specifications/Burgers-E0.md`.

## Verdict

**Faithful, with remarks.** No blocker in the Lean files. Three findings were marked "should fix". All three are
fixed in the committed version (see "Changes after the review"). The fixed files were not reviewed again.

## Findings

1. **Should fix (fixed): division on `ℝ` in the trusted file went through the instance under verification.**
   `class Scalar ... extends Div α` made `Scalar.toDiv` a global instance, and `ℝ` has no direct `Div` instance, so
   every `/` in the trusted definitions was `instScalarReal.toDiv`. It was definitionally the Mathlib division, so no
   statement was wrong, but the trusted mathematics was not independent of `RealScalar.lean` for division.
2. **Should fix (fixed): the driver printed NaN as `0.e0`.** With `cfl = 3` every cell is NaN and the program printed
   zeros and "sum drift = 0".
3. **Should fix (fixed): `sci` could be wrong by a factor 10** when the mantissa rounds up to 10.
4. Remark: the `Float` `max` is not symmetric for NaN. Apart from NaN, signed zero and rounding, each `Float` field
   matches the `ℝ` field; `third` and `twoThirds` are the correctly rounded doubles.
5. Remark: the kernel is what its docstrings say (elaborated terms inspected; empty array, size 1, size 2 and the
   `Fin` wrap-around for `n = 1, 2, 5` checked by evaluation).
6. Remark: `RealScalar.lean` is correct field by field; `#synth Scalar ℝ` gives `instScalarReal` and no other
   instance exists.
7. Remark: the nine trusted statements are correctly formed; the kernel calls use `instScalarReal`; `max |m| |M|` is
   the real maximum; the transfer statements include the empty array; none is vacuous. `dx ≠ 0` in the sum statement
   is not necessary.
8. Remark: the two diagnostic statements (`SumDiagnostic`, `TotalVariationDiagnostic`) are not in the contract table.
   They give the sum and total-variation transfer statements their meaning, so the trusted set is stronger than the
   table.
9. Remark: hashes matched the pins; the nine bridge theorems use only the three standard axioms.

Runs of the program: `200 200 0.4` and `50 400 0.5` conserve the sum to rounding, stay in the initial bounds and
decrease the total variation; `50 400 1.5` (outside the proved hypothesis) was still stable; `50 400 3` gives NaN.
An independent Python implementation matched every printed digit for `200 200 0.4` and `50 400 0.5`.

Scope notes of the reviewer: nothing is claimed about `Float`; the driver does not check the CFL hypothesis; in the
first version bad arguments were silently replaced by defaults.

## Changes after the review

- `Kernel.lean`: the parent projections of `Scalar` are instances of priority 10, so `ℝ` and `Float` keep their own
  arithmetic. In the trusted file `x / y` on `ℝ` is now `DivInvMonoid.toDiv` of Mathlib (checked with `pp.explicit`
  and `#synth Div ℝ`). The stale comment is corrected.
- Trusted file: new statement `RealScalarIsStandard`. It says that each field of the real instance is the Mathlib
  operation or literal. The bridge proves it by `rfl`.
- `Main.lean`: `sci` prints `NaN`, `inf`, `-inf` and corrects the decade of the mantissa; arguments are checked and a
  bad argument stops the program with exit code 1; a non-finite final state gives a message and exit code 2; one
  line of the output says that `Float` arithmetic is not verified and that the proved hypothesis is `cfl ≤ 0.5`.

## Not checked by the reviewer

The refinement proofs, a rebuild, `lake comparator`, `scripts/verify.py`, the CI wiring.
