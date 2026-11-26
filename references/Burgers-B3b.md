# Burgers B3b implementation: source/result map

Status: **implementation candidate; independent acceptance pending**.

Frozen contract: `specifications/Burgers-B3b.md` (frozen by the agent, `specifications/Burgers-B3b-approval.md`; the
user asked for the formulation and the limiters). Result bindings checked by `scripts/verify.py`:
`specifications/Burgers-B3b-results.json`. Toolchain: Lean v4.36.0.

B3b adds new modules only. No B0--B4, E0, E0b, accepted Euler M1--M4 or M5 source is modified.

## The formulation

```text
slope of a cell  =  ψ(a, b) · (a + b)/2        a = u_i - u_{i-1},  b = u_{i+1} - u_i
                    ───────   ─────────
                    limiter   unlimited central slope (the default)
                    factor    
```

No limiter is the factor 1. The reconstruction, the flux difference, conservation and constant states are the B3 ones;
they hold for every slope function. Only the bounds and total-variation theorems need a limiter certificate.

| Limiter | `ψ` for `ab > 0` (0 otherwise) | Classical slope | Factor range | `θ` | CFL for Burgers-Rusanov |
| --- | --- | --- | --- | --- | --- |
| none | 1 (always) | `(a + b)/2` | 1 | none | no stability theorem; overshoot example |
| minmod | `2 min(\|a\|,\|b\|)/(\|a\|+\|b\|)` | `sgn(a) min(\|a\|,\|b\|)` | `[0, 1]` | 1 | 1/6 |
| MC | `min(1, 4 min(\|a\|,\|b\|)/(\|a\|+\|b\|))` | `sgn(a) min(\|a+b\|/2, 2\|a\|, 2\|b\|)` | `[0, 1]` | 2 | 1/8 |
| superbee | `2 max(min(2\|a\|,\|b\|), min(\|a\|,2\|b\|))/(\|a\|+\|b\|)` | `sgn(a) max(min(2\|a\|,\|b\|), min(\|a\|,2\|b\|))` | `[0, 4/3]` | 2 | 1/8 |
| van Leer | `4ab/(a+b)²` | `2ab/(a+b)` | `[0, 1]` | 2 | 1/8 |
| van Albada | `2ab/(a²+b²)` | `ab(a+b)/(a²+b²)` | `[0, 1]` | 5/4 | 2/13 |

The CFL column is `dt · max(|m|, |M|)/dx ≤ 1/(4 + 2θ)`. It is sufficient, not sharp. The constants `θ` are sharp for
minmod, MC, superbee and van Leer; for van Albada the sharp value is `(1 + √2)/2 ≈ 1.207`.

## Module map

| Module | Purpose |
| --- | --- |
| `CFDLean/Discrete/Periodic/Limiters.lean` | Central slope, limiter factors, certificate `SlopeBounded θ`, classical forms, ranges, generalized incremental form and one-step theorems |
| `CFDLean/Schemes/Burgers/RusanovLimiters.lean` | MUSCL-Rusanov with a `θ`-bounded slope: one-step and multi-step results, limiter instances, the overshoot example |
| `CFDLean/Schemes/Burgers/LimiterControls.lean` | Exact small controls |
| `CFDLean/Verification/BurgersB3bChallenge.lean` | Trusted B3b statements; imports only Mathlib |
| `CFDLean/Verification/BurgersB3bVerify.lean` | Bridge |
| `Challenges/BurgersB3b.lean` | `lake comparator` challenge |

## Frozen result IDs

### B3b-U — unlimited slope and limiter factor

- Definitions: `CFDLean.Scalar.FiniteVolume.centralSlope`, `.limitedSlope`, `.noLimiter`
- Result: `.limitedSlope_noLimiter`

Use: `musclRhs g dx nf centralSlope` is the unlimited scheme; `musclRhs g dx nf (limitedSlope ψ)` is the limited one.
The Burgers maps are `Rusanov.musclEulerStep g dx dt φ`, `musclSsprk2Step`, `musclSsprk3Step` of B3 with
`φ = centralSlope` or `φ = limitedSlope ψ`.

### B3b-C — certificate

- Definition: `.SlopeBounded`
- Results: `.minmodBounded_iff_slopeBounded_one`, `.SlopeBounded.mono`, `.SlopeBounded.nonneg`,
  `.not_slopeBounded_centralSlope`

### B3b-L — limiters

- Definitions: `.minmodFactor`, `.mcFactor`, `.superbeeFactor`, `.vanLeerFactor`, `.vanAlbadaFactor`
- Results: `.limitedSlope_minmodFactor` (equals the B3 `minmod`), `.limitedSlope_mcFactor`,
  `.limitedSlope_superbeeFactor`, `.limitedSlope_vanLeerFactor`, `.limitedSlope_vanAlbadaFactor`; the five `_mem`
  (factor range), the five `_comm` (symmetry) and the five `slopeBounded_*Factor` theorems
- Supporting: sign lemmas for `ab > 0`, `limitedSlope_eq_sign_mul`, `*_mul`, and `slopeBounded_limitedSlope` (a general
  criterion: a symmetric factor that is 0 unless `ab > 0`, with `0 ≤ ψ` and `ψ (|a|+|b|)/2 ≤ θ|a|`)

### B3b-I — incremental form

- Result: `.muscl_incremental_bounded`
- Supporting: `.half_slope_mem_two`, `.leftState_mem_bounded`, `.rightState_mem_bounded`, `.slope_combo_bounded`,
  `.rightState_sub_bounded`, `.leftState_sub_bounded`, `.flux_right_increment_bounded`, `.flux_left_increment_bounded`

The proof is the B3 proof with the constant `1 + θ/2` in place of `3/2`. `θ ≤ 2` is used twice: the reconstructed
states stay between the two neighbour values, and the ratio `1 - θ/2` is nonnegative. `sign_transfer` and
`exists_ratio` of B3 are reused.

### B3b-T — generic one-step theorems

- Results: `.muscl_step_totalVariation_le_bounded`, `.muscl_step_mem_bounded`; supporting `.coeff_sum_le_one_bounded`

### B3b-S — MUSCL-Rusanov

- Results: `CFDLean.Burgers.Rusanov.musclEulerStep_mem_bounded`, `.musclEulerStep_totalVariation_le_bounded`,
  `.musclEulerStep_iterate_stable_bounded`, `.musclSsprk2Step_iterate_stable_bounded`,
  `.musclSsprk3Step_iterate_stable_bounded`, and the SSPRK3 instances `.musclSsprk3Step_minmodFactor_iterate_stable`,
  `.musclSsprk3Step_mc_iterate_stable`, `.musclSsprk3Step_superbee_iterate_stable`,
  `.musclSsprk3Step_vanLeer_iterate_stable`, `.musclSsprk3Step_vanAlbada_iterate_stable`
- Supporting: `.cfl_of_bounded`

### B3b-N — the unlimited scheme is not bound preserving

- Definition: `CFDLean.Burgers.Rusanov.stepData` (`(0, 0, 1, 1)` on `ZMod 4`)
- Results: `.stepData_mem`, `.unlimited_step_leaves_bounds` (cell 3 becomes `167/160` with `dx = 1`, `dt = 1/10`)

Hand check: `L_3 = 3/4`, `R_3 = 1/4`, `F_3 = 11/32`; `L_2 = R_2 = 5/4`, `F_2 = 25/32`; cell 3 is
`1 + (1/10)(14/32) = 167/160`. `LimiterControls.lean` shows that the same step with the van Leer limiter stays in
`[0, 1]`.

## Trusted boundary

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
| --- | --- | --- | --- |
| B3b-L | `LimiterFactorForms` | `limiter_factor_forms` | the five `_mem` theorems and classical forms |
| B3b-L | `LimiterBounds` | `limiter_bounds` | the five `slopeBounded_*Factor` theorems |
| B3b-S | `MusclEulerBoundedMultiStep`, `MusclSSPRK2BoundedMultiStep`, `MusclSSPRK3BoundedMultiStep` | `muscl_*_bounded_multi_step` | `Rusanov.muscl*Step_iterate_stable_bounded` |
| B3b-N | `UnlimitedOvershoot` | `unlimited_overshoot` | `Rusanov.unlimited_step_leaves_bounds` |

The trusted file defines the limiters in their classical slope form and does not contain the factor definitions of the
implementation. `LimiterFactorForms` says that each classical slope is some factor in the stated range times the
central slope; the bridge supplies the implemented factor. The multi-step statements quantify over every `θ ≤ 2` and
every `θ`-bounded slope function, so they cover all five limiters through `LimiterBounds`. The trusted statements were
checked by a separate review agent (`reviews/Burgers-B3b/TrustedStatements_Review.md`); no human reviewed them yet.

Checks: `scripts/verify.py`, `KernelAudit.lean`,
`lake comparator --paranoid --config Challenges/BurgersB3b.comparator.json`.

## Notes from the review

- The contract calls the unlimited scheme "Fromm's scheme". This is loose: Fromm's scheme is a fully discrete scheme.
  Here the unlimited scheme is the central-slope MUSCL discretization in space with the chosen time integrator.
- The overshoot of the unlimited step is `1 + 7 dt/16` in the example for every `dt > 0`; it is not an effect of a
  large time step.
- `vanAlbadaFactor = 2ab/(a² + b²)` has the form of the function often called "van Albada 2", `2r/(1 + r²)`. Here it is
  the factor on the central slope; the limited slope is the classical van Albada 1 slope `ab(a + b)/(a² + b²)`,
  clipped to 0 for `ab ≤ 0`.
- Random tests of the reviewer found no violation of bounds or total variation up to CFL 0.5 (MC, superbee, van Leer)
  and 0.6 (minmod, van Albada). The proved constants are about four times smaller. `θ ≤ 2` is necessary: with
  `3 · minmod` violations appear at every CFL tried.

## Exclusions

No accuracy statement. No sharp CFL constant. The executable `burgers1d --muscl` still uses minmod; a limiter choice
in the kernel is a later milestone (E0c). No entropy result for MUSCL.
