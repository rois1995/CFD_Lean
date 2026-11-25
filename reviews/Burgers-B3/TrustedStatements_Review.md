# Burgers B3: review of the trusted statement file

Date: 2026-11-26. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed file and
did not check the implementation proofs. This is not a human review and not the independent implementation review.

Reviewed file: `CFDLean/Verification/BurgersB3Challenge.lean`
(sha256 `977a2e63064d9667d94b136cff163e201be25028d81449efc54c1c152abf4d8d`).
Reference: `specifications/Burgers-B3.md`; comparison with the B1 and B2 trusted files.

## Verdict

**Faithful, with remarks.** No blocker and no required change.

## Checks made by the reviewer (on a scratch copy of the file)

- `minmod` is the standard limiter (values checked in Lean, including ties, a zero argument and opposite signs).
- `musclEulerStep` equals the interface-indexed form of the contract (`simp`), and with zero slopes it equals the B2
  `eulerStep`. Two cells give zero slopes (first order); a fixed point of `next` gives the identity; several cycles
  split into independent periodic grids.
- `RusanovLipschitz`: the first part varies the left state, the second the right state. The constant `2A` is sharp:
  Lean proved that `(2 - 1/100) A` fails at `A = 1`, `a = 1`, `a' = 0.999`, `b = -0.998`.
- `MultiStepStable`: hypotheses and conclusion as in the contract; `(T next dx dt)^[n] u j` is `((T ...)^[n] u) j`;
  `ssprk2`, `ssprk3`, the flux and the total variation are the same text as in the B1 and B2 trusted files.
- Own derivation of the stability claim (ratios of reconstructed differences in `[1/2, 3/2]`, coefficients at most
  `3 A dt / dx ≤ 1/2`).
- Numerical tests. Exact rationals at the limit `6 · dt · A = dx`: about 1950 random cases, no violation.
  Floats, 3000 cases, 30 steps: no violation for `dt · A / dx ≤ 0.66`; violations from 0.68 (Euler) upward.

## Findings (all remarks)

1. `dx ≠ 0` in the conservation statements is not necessary (`x / 0 = 0`); it matches the contract.
2. The trusted file states the Burgers results for `minmod` only. The results for every limiter with `MinmodBounded`,
   the zero limiter, constant states, first-order recovery and the bounds of the reconstructed states have no trusted
   statement; the kernel audit and the result map check them. This matches the contract table.
3. `RusanovLipschitz` uses `|·| ≤ A`; the contract certificate uses states in `[m, M]` with `2 max(|m|, |M|)`. These
   are equivalent.
4. The CFL constant 1/6 is about four times smaller than the largest value without a violation in the tests
   (about 0.66, probably 2/3). The contract does not claim a sharp constant.

## Not checked by the reviewer

The implementation and bridge proofs, `lake comparator`. The CFL scan is random sampling, not a proof.
