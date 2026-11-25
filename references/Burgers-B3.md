# Burgers B3 implementation: source/result map

Status: **implementation candidate; independent acceptance pending**.

Frozen contract: `specifications/Burgers-B3.md` (frozen by the agent, `specifications/Burgers-B3-approval.md`).
Result bindings checked by `scripts/verify.py`: `specifications/Burgers-B3-results.json`. Toolchain: Lean v4.36.0.

B3 adds new modules only. No B0, B1, B2, accepted Euler M1--M4 or M5 source is modified.

## Module map

| Module | Purpose |
| --- | --- |
| `CFDLean/Schemes/Scalar/Lipschitz.lean` | Lipschitz certificate `LipschitzOnBounds` of a two-point flux on bounded states |
| `CFDLean/Discrete/Periodic/Muscl.lean` | Limiter certificate, minmod, MUSCL reconstruction and right-hand side, incremental form, one-step theorems |
| `CFDLean/Schemes/Burgers/RusanovMuscl.lean` | Rusanov Lipschitz certificate; MUSCL-Rusanov with Euler, SSPRK2, SSPRK3 |
| `CFDLean/Schemes/Burgers/MusclControls.lean` | Exact small controls |
| `CFDLean/Verification/BurgersB3Challenge.lean` | Trusted B3 statements; imports only Mathlib |
| `CFDLean/Verification/BurgersB3Verify.lean` | Bridge |
| `Challenges/BurgersB3.lean` | `lake comparator` challenge |

## Frozen result IDs

### B3-L — limiter certificate

- Definitions: `CFDLean.Scalar.FiniteVolume.MinmodBounded`, `.minmod`
- Results: `.minmod_minmodBounded`, `.zero_minmodBounded`

### B3-R — reconstruction

- Definitions: `.slope`, `.leftState`, `.rightState`, `.musclFlux`, `.musclRhs`
- Results: `.musclRhs_zero` (zero limiter gives the B0 right-hand side), `.musclRhs_sum_zero` (any flux, any limiter),
  `.musclRhs_constant` (any flux, any limiter: every interface sees the same two states), `.leftState_mem`,
  `.rightState_mem`
- Supporting: `.half_slope_mem`

### B3-K — Lipschitz certificate

- Definition: `CFDLean.Scalar.LipschitzOnBounds`; supporting `.nonneg` (constants are nonnegative when `m < M`)
- Results: `CFDLean.Burgers.Rusanov.eval_lipschitz_left`, `.eval_lipschitz_right`, `.lipschitzOnBounds`

The constant `2A` is sharp: for `a > |b|` the left derivative of the flux is `3a/2 - b/2`, which tends to `2A`.

### B3-I — incremental form

- Result: `CFDLean.Scalar.FiniteVolume.muscl_incremental`
- Supporting: `.slope_combo`, `.rightState_sub`, `.leftState_sub` (the reconstructed-state differences are between
  `1/2` and `3/2` times the cell difference), `.sign_transfer`, `.flux_right_increment`, `.flux_left_increment`
  (monotonicity gives the sign, the Lipschitz certificate gives the size), `.exists_ratio` (a quotient without
  a division in the statement), `.muscl_incremental_false_without_nonneg` (the hypotheses `0 ≤ KL`, `0 ≤ KR` are
  necessary: counterexample on the interval `m = M = 0`)

The flux difference of cell `i` is split as `[F(L_i, R_i) - F(L_i, R_{i-1})] + [F(L_i, R_{i-1}) - F(L_{i-1}, R_{i-1})]`.
The first bracket is `-C_i Δ_i / λ`, the second is `D_{i-1} Δ_{i-1} / λ`.

### B3-T — generic one-step theorems

- Results: `.muscl_step_totalVariation_le`, `.muscl_step_mem`
- Supporting: `.muscl_step_eq_self_of_le` (degenerate interval), `.coeff_sum_le_one`

Compositions: B3-I, then B1-H (`incrementalUpdate_totalVariation_le`) or B1-X (`incrementalUpdate_bounds`).

### B3-S — MUSCL-Rusanov

- Definitions: `CFDLean.Burgers.Rusanov.musclEulerStep`, `.musclSsprk2Step`, `.musclSsprk3Step`
- Results: `.musclEulerStep_mem`, `.musclEulerStep_totalVariation_le`, `.musclEulerStep_iterate_stable`,
  `.musclSsprk2Step_iterate_stable`, `.musclSsprk3Step_iterate_stable`, the three `_sum` and the three `_constant`
  theorems
- Supporting: `.cfl_of_six`, the `minmod` instances

Compositions: B3-T with B1-M (`Rusanov.monotone`) and B3-K, then the B2 results `Time.SSP.ssprk*_mem`, `ssprk*_le`,
`iterate_*`, `ssprk*_linear`, `ssprk*_fixed`.

## Trusted boundary

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
| --- | --- | --- | --- |
| B3-L | `MinmodProperties` | `minmod_properties` | `FiniteVolume.minmod_minmodBounded` |
| B3-K | `RusanovLipschitz` | `rusanov_lipschitz` | `Rusanov.eval_lipschitz_left` (and `_right`) |
| B3-S | `MusclEulerMultiStep`, `MusclSSPRK2MultiStep`, `MusclSSPRK3MultiStep` | `muscl_*_multi_step` | `Rusanov.muscl*Step_iterate_stable` |
| B3-S | `MusclEulerConservation`, `MusclSSPRK2Conservation`, `MusclSSPRK3Conservation` | `muscl_*_conservation` | `Rusanov.muscl*Step_sum` |

The trusted file writes the scheme in the cell-based textbook form: face states `u_i ± σ_i / 2` and the step
`u_i - (dt/dx)(F(u_i⁺, u_{i+1}⁻) - F(u_{i-1}⁺, u_i⁻))`. The implementation is indexed by interfaces. The bridge lemma
`musclEulerStep_eq` proves that both are the same map. The generic theorems (any flux and limiter with certificates)
have no trusted statement; the kernel audit and the result map check them. The trusted statements were checked by a
separate review agent (`reviews/Burgers-B3/TrustedStatements_Review.md`); no human reviewed them yet.

Checks: `scripts/verify.py`, `KernelAudit.lean`,
`lake comparator --paranoid --config Challenges/BurgersB3.comparator.json`.

## Notes on the hypotheses

- CFL `6 · dt · max(|m|, |M|) ≤ dx` is sufficient, not sharp. It is `dt · (3/2)(KL + KR) ≤ dx` with the Lipschitz
  constants of the Rusanov flux. A flux with smaller constants gets a larger time step from the same theorem.
- One `dt` for all steps and stages, from the bounds of the initial state.
- The limiter class is the minmod region. A limiter with slopes up to twice the smaller difference is not covered.

## Exclusions

No B3 result implies second-order accuracy, an entropy inequality, convergence, floating-point correctness, or array
or parallel refinement.
