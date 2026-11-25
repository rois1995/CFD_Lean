# Burgers B2: review of the trusted statement file

Date: 2026-11-25. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed file and
did not check the implementation proofs. This is not a human review and not the independent implementation review.

Reviewed file: `CFDLean/Verification/BurgersB2Challenge.lean`
(sha256 `445e3cf8c17a53ba5e9f55a911bf5070fff187144ad48c12126fe7186124af75`).
Reference: `specifications/Burgers-B2.md`; comparison with the B0 and B1 trusted files.

## Verdict

**Faithful, with remarks.** No blocker and no required change.

## Checks made by the reviewer (on a scratch copy of the file)

- `ssprk2` over `E v = v + dt • L v` is Heun's method. `ssprk3` is the classical SSPRK(3,3):
  `u + dt (k1/6 + k2/6 + 2 k3/3)` with `k1 = L u`, `k2 = L(u + dt k1)`, `k3 = L(u + dt/4 k1 + dt/4 k2)`.
- `eulerStep` is the B1 `rusanovStep` (`rfl` on a copy) and the B0 scheme.
- `T^[n] u j` parses as `(T^[n] u) j`; `max |m| |M|` is `max (|m|) (|M|)`; the scalar multiple on `I → ℝ` is pointwise.
- `m ≤ a, b ≤ M` gives `rusanovWaveSpeed a b ≤ max |m| |M|`, so the hypothesis gives both B1 CFL conditions at
  every interface, stage and step. The hypotheses hold for real data (`m = -1`, `M = 1`, `dx = 1`, `dt = 1/2`).
- Own derivation: bounded states are convex, the total variation is convex, every SSP stage is a convex combination of
  states in the invariant set. An exact-rational random test (300 cases, random permutations, `dt` at the limit) found
  no violation.

## Findings (all remarks)

1. `dx ≠ 0` in the conservation statements is not necessary (with `dx = 0` the step is the identity by `x / 0 = 0`).
   It matches the contract and only weakens the statement.
2. `SSPRK2Convex` and `SSPRK3Convex` take `ConvexOn ℝ S Φ` also for the membership part. Nothing is lost: `Φ = 0` gives
   the membership result for every convex `S`.
3. The trusted file states the seven statements of the contract table. Not stated against Mathlib-only definitions:
   B2-N, B2-L, the constant-state results, `ssprk2_forwardEuler`, the B2-B lemmas, and the `ZMod N` lemma. Those are
   checked by the kernel audit and the result map.
4. `MultiStepStable` is trivially true for `m > M` (then the grid is empty) and for `n = 0`. Real instances exist.
5. The contract says "frozen on 2026-11-26"; the freeze commit is of 2026-11-25. The contract is hash-pinned, so the
   date stays as written.

## Not checked by the reviewer

The implementation and bridge proofs, `lake comparator`, and an independent full proof of the multi-step statements.
