# Burgers B3b: review of the trusted statement file

Date: 2026-11-26. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed file and
did not check the implementation proofs. This is not a human review and not the independent implementation review.

Reviewed file: `CFDLean/Verification/BurgersB3bChallenge.lean`
(sha256 `05cb0c2a46cc79526cac38e70cb8e7e4803dff3634f2611eefc94fcf81f05b91`).
Reference: `specifications/Burgers-B3b.md`; comparison with the B3 trusted file.

## Verdict

**Faithful, with remarks.** No blocker and no required change.

## Checks made by the reviewer

- Lean, on a scratch copy: own full proof of `UnlimitedOvershoot`; parsing of `MultiStepStable`; for `θ < 0` no slope
  function is `θ`-bounded; `superbee(1, 2) = 4/3 · s(1, 2)`; `mc(1, 4)` and `superbee(1, 2)` equal `2|a|`.
- Each limiter compared with its Sweby function `φ(r)`, `r = a/b`: minmod `min(1, r)`, MC `min(2r, (1+r)/2, 2)`,
  superbee `max(min(2r, 1), min(r, 2))`, van Leer `2r/(1+r)`, van Albada `(r² + r)/(r² + 1)` (van Albada 1). Ties,
  zeros and opposite signs checked; no division by zero inside the `ab > 0` branches.
- `SlopeBounded θ` is the Sweby region in two-argument form; with `θ = 2` it is `0 ≤ φ ≤ min(2r, 2)`.
- Own derivation of the multi-step statement (reconstructed states between neighbours, ratios in
  `[1 - θ/2, 1 + θ/2]`, Rusanov Lipschitz constant `2A`, Harten, SSP as convex combinations).
- Exact-rational tests of each limiter at its CFL limit with Euler, SSPRK2, SSPRK3, random states and permutations:
  no violation. Float tests with 20 steps: no violation.

## Findings (all remarks)

1. The limiters are the standard ones. `vanAlbada` is clipped to 0 for `ab ≤ 0` (the contract says so). The
   implementation name `vanAlbadaFactor = 2ab/(a² + b²)` has the form of "van Albada 2" as a function of `r`; it is the
   factor on the central slope, not a different limited slope.
2. `LimiterFactorForms` is true with the constants `1, 1, 4/3, 1, 1`; `4/3` is sharp. The factor is an existential per
   pair `(a, b)`; the trusted file does not contain the implemented factor functions. The bridge supplies them.
3. `LimiterBounds`: all constants are true; sharp for minmod, MC, superbee, van Leer (supremum); `5/4` is not sharp
   for van Albada (sharp value `(1 + √2)/2`).
4. With `minmod` the general step is the B3 trusted step. The contract's name "Fromm's scheme" for the unlimited
   scheme is loose; the trusted file only says "unlimited".
5. `MultiStepStable`: hypotheses and quantifiers as in the contract. `θ ≤ 2` is necessary (violations with
   `3 · minmod` at every CFL tried). For `θ < 0` the statement is vacuous, harmless. Largest CFL without a violation
   in random float tests (information only): minmod 0.6, MC 0.5, superbee 0.5, van Leer 0.5, van Albada 0.6.
6. `UnlimitedOvershoot` is correct; the overshoot is `1 + 7 dt/16` for every `dt > 0`.
7. Not stated in the trusted file: the factor functions, `noLimiter`, symmetry, the per-limiter instances (they follow
   from `LimiterBounds` and the multi-step statements), conservation for a general slope function, accuracy.

## Changes after the review

A comment in `CFDLean/Discrete/Periodic/Limiters.lean` no longer uses the name "Fromm". Notes added to
`references/Burgers-B3b.md`.

## Not checked by the reviewer

The implementation proofs, the bridge, `lake comparator`. The exact-rational tests ran one or two steps only.
