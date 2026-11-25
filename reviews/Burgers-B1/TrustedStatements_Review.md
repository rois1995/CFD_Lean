# Burgers B1: review of the trusted statement file

Date: 2026-11-25. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed file and
did not see the implementation proofs. This is not a human review and not the independent implementation review.

Reviewed file: `CFDLean/Verification/BurgersB1Challenge.lean`
(sha256 `c8f0c7e54f96b72dce34f5e7ccedeae7ba19028689a2b047bfba1ca87cf385bf`).
Reference: `specifications/Burgers-B1.md`; comparison with `CFDLean/Verification/BurgersB0Challenge.lean`.

## Verdict

**Faithful, with remarks.** No blocker and no required change. The five statements say what the contract promises,
and the reviewer derived by hand that all five are true.

## Findings (all remarks)

1. `rusanovStep` is the B0 scheme. B0 writes `u (next (next.symm i))` where B1 writes `u i`; the values are equal
   (`Equiv.apply_symm_apply`). The flux definitions are the same text as in B0. Checked values: `rusanov 1 0 = 3/4`,
   `rusanov (-2) 0 = -1`.
2. The incremental form and its indices match the contract: `C i` multiplies `u(next i) - u i`, `D (next.symm i)`
   multiplies `u i - u(next.symm i)`; the Harten condition pairs `C i + D i` at one interface; the bounds condition
   pairs `C i + D (prev i)` at one cell.
3. `next` may be any permutation. With several cycles the total variation is the sum over the cycles; with the
   identity it is 0. All statements stay true. An empty or one-element index type makes them trivially true.
4. `dx > 0` adds nothing once the CFL inequality holds on a nonempty grid, but it is the explicit hypothesis of frozen
   decision 5. `dt ≥ 0` is necessary.
5. The per-interface CFL hypothesis is equivalent to the global one `dt · max_j |u_j| ≤ dx`. The contract sentence
   "a global bound implies it" is true; there is no gain in generality.
6. CFL 1/2 is sufficient for the bounds and not sharp. At CFL 1 the sum `C_i + D_{i-1}` reaches 1.5
   (`0.3, -0.275, -0.3`), so the lemma needs a constant below 1; 2/3 is enough for the lemma. A numerical search found
   no violation of the bounds at CFL 1 (evidence only, not a proof).
7. `RusanovMonotone` has the right directions and is true without a CFL hypothesis.
8. No Lean pitfall: no natural subtraction, no auto-bound variable, no coercion; the only division is by `dx`.

## Not checked by the reviewer

The implementation, the bridge proofs and `lake comparator`.
