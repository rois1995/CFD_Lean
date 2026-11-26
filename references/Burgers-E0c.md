# Burgers E0c implementation: source/result map

Status: **implementation candidate; independent acceptance pending**.

Frozen contract: `specifications/Burgers-E0c.md` (frozen by the agent, `specifications/Burgers-E0c-approval.md`; the
user asked for the formulation and the limiters). Result bindings checked by `scripts/verify.py`:
`specifications/Burgers-E0c-results.json`. Toolchain: Lean v4.36.0.

E0c adds new modules and changes the unverified driver `Main.lean`. The class `Scalar`, the E0 kernel, the E0b kernel
and every mathematical source are unchanged.

## Run it

```bash
lake exe burgers1d 200 600 0.12 --muscl                 # MUSCL, no limiter (unlimited central slope)
lake exe burgers1d 200 600 0.12 --limiter vanleer       # MUSCL with a limiter
lake exe burgers1d 200 200 0.4                          # first-order scheme
```

Limiter names: `none`, `minmod`, `mc`, `superbee`, `vanleer`, `vanalbada`. `--limiter NAME` implies MUSCL. `--muscl`
alone is the unlimited scheme (in E0b it was minmod; `--limiter minmod` gives the E0b result bit for bit). The first
output line names the scheme and the limiter. The note line gives the proved range for real arithmetic and says if the
run is inside it: `cfl <= 0.5` first order, `1/6` minmod, `2/13` van Albada, `1/8` MC, superbee, van Leer. For the
unlimited scheme it says that no bounds are proved. Exit codes: 0 normal, 1 bad arguments, 2 non-finite result.

Test runs, `N = 200`, `cfl = 0.12`, 600 steps (final time 0.24, after the shock forms at about 0.159); the initial
state has minimum -0.49988, maximum 1.49988, total variation 3.99951:

| Scheme | Final minimum | Final maximum | Final TV | In the initial bounds |
| --- | --- | --- | --- | --- |
| unlimited | -0.52492 | 1.65049 | 4.42173 | **no** (overshoot about 10%) |
| minmod | -0.49697 | 1.49337 | 3.98069 | yes |
| MC | -0.49911 | 1.49841 | 3.99505 | yes |
| superbee | -0.49961 | 1.49954 | 3.99830 | yes |
| van Leer | -0.49849 | 1.49709 | 3.99116 | yes |
| van Albada | -0.49781 | 1.49566 | 3.98693 | yes |

The sum is kept to rounding in every run. These are tests with `Float`, not proofs.

## Module map

| Module | Purpose |
| --- | --- |
| `CFDLean/Exec/LimiterKernel.lean` | Sign-test class `ScalarSign`, limiter type, kernel slopes, MUSCL array kernel with a limiter choice. Imports only the E0b kernel. |
| `CFDLean/Exec/RealScalarSign.lean` | The `ℝ` instance of the sign test |
| `CFDLean/Exec/LimiterRefinement.lean` | Kernel slopes are the B3b slope functions; refinement; transfer of the B3b results |
| `Main.lean` | Driver: `--muscl` (unlimited), `--limiter NAME` |
| `CFDLean/Verification/BurgersE0cChallenge.lean` | Trusted E0c statements; imports Mathlib and five trusted inputs |
| `CFDLean/Verification/BurgersE0cVerify.lean` | Bridge |
| `Challenges/BurgersE0c.lean` | `lake comparator` challenge |

## Frozen result IDs

### E0c-K — kernel

- Definitions: `CFDLean.Exec.ScalarSign` (class), `Limiter`, `Limiter.isLimited`, `Scalar.maxmodSame`, `limiterSlope`,
  `limSlopeAt`, `limFacePlus`, `limFaceMinus`, `limiterEulerStepArray`, `limiterSsprk2StepArray`, `instScalarSignReal`
- Results: `limiterEulerStepArray_size`, `limiterSsprk2StepArray_size`, `limiterSsprk3StepArray_size`

Kernel slopes: `none` is `(a + b)/2`; minmod is the comparison-free minmod of E0b; MC is
`minmod(minmod(2a, 2b), (a + b)/2)`; superbee is `maxmodSame(minmod(2a, b), minmod(a, 2b))`; van Leer is
`2ab/(a + b)` and van Albada is `ab(a + b)/(a² + b²)` when `isPos (ab)`, else 0. The branch keeps a flat state
exactly flat in `Float` (no `0/0`).

### E0c-L — the kernel slopes are the mathematical ones

- Definitions: `Limiter.slopeFn`, `Limiter.theta`
- Results: `isPos_eq`, `limiterSlope_eq`, `Limiter.slopeBounded`, `Limiter.theta_le_two`
- Supporting: `Limiter.isLimited_iff`, `minmod_of_pos`, `minmod_of_neg`, `minmod_of_not_mul_pos`, `maxmodSame_eq`,
  `maxmodSame_of_nonneg`, `maxmodSame_of_nonpos`

### E0c-S — refinement

- Results: `limiterEulerStepArray_refines`, `limiterSsprk2StepArray_refines`, `limiterSsprk3StepArray_refines` (every
  limiter, also `none`), and `limiterEulerStepArray_minmod`, `limiterSsprk2StepArray_minmod`,
  `limiterSsprk3StepArray_minmod` (the `minmod` choice is the E0b kernel, for every arithmetic)
- Supporting: `limSlopeAt_eq`, `limFacePlus_eq`, `limFaceMinus_eq`, the three `_refinedBy` forms

### E0c-T — transfer of the B3b theorems to arrays

- Results: `run_limiterEulerStepArray_sum`, `run_limiterSsprk3StepArray_sum` (every limiter, also `none`);
  `run_limiterEulerStepArray_bounds`, `run_limiterSsprk3StepArray_bounds`,
  `run_limiterEulerStepArray_totalVariation_le`, `run_limiterSsprk3StepArray_totalVariation_le` (every limiter except
  `none`, hypothesis `(4 + 2θ) · dt · max(|m|, |M|) ≤ dx`)

### E0c-X — executable

- Definitions run by the program: `limiterSsprk3StepArray`, `instScalarSignFloat`. Built and run in CI.

## Trusted boundary

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
| --- | --- | --- | --- |
| E0c-L | `RealSignIsStandard` | `real_sign_is_standard` | `isPos_eq` |
| E0c-L | `KernelSlopeIsLimiter` | `kernel_slope_is_limiter` | `limiterSlope_eq` |
| E0c-S | `LimiterEulerStepRefines`, `LimiterSSPRK3StepRefines`, `LimiterSSPRK3RunRefines` | `limiter_*_refines` | `limiterEulerStepArray_refines`, `limiterSsprk3StepArray_refines` |
| E0c-T | `LimiterSSPRK3RunSum`, `LimiterSSPRK3RunBounds`, `LimiterSSPRK3RunTotalVariation` | `limiter_ssprk3_run_*` | `run_limiterSsprk3StepArray_*` |

The trusted file restates the six slope functions in classical form (`slopeOf`), the constants (`thetaOf`), and the
MUSCL step on `Fin n` with a slope function; the bridge proves that they are the implemented ones. It imports Mathlib
and five trusted inputs, all hash-pinned in `scripts/verify.py`: the E0 kernel, the real instance, the E0b kernel, the
limiter kernel, the real sign test. The sum and total-variation statements use the E0 diagnostics (E0 trusted
statements `SumDiagnostic`, `TotalVariationDiagnostic`). The trusted statements were checked by a separate review
agent (`reviews/Burgers-E0c/TrustedStatements_Review.md`); no human reviewed them yet.

Checks: `scripts/verify.py`, `KernelAudit.lean`,
`lake comparator --paranoid --config Challenges/BurgersE0c.comparator.json`.

## Notes from the review

- The van Albada slope here is the clipped one: 0 for `ab ≤ 0`. The classical function `(r² + r)/(r² + 1)` is negative
  for `-1 < r < 0`. This is the B3b definition.
- The program decides "inside the proved range" from the given `cfl`. Exactly at the limit the rounded `dt` can be
  outside the hypothesis of the theorem by one rounding error.
- An exact rational instance of the kernel matched an independent rational implementation of the textbook scheme for
  all six choices on 61 arrays (reviewer's test).

## What is not verified

`Float` arithmetic, the driver, the compiler, performance. With `Float`, the sign test is false for NaN; minmod, MC and
superbee are not symmetric for a NaN argument; a NaN cell still spreads through the fluxes and the driver reports it.
For very large differences `ab` can overflow in van Leer and van Albada. The CFL constants are sufficient, not sharp.
