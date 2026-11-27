# Burgers B1 implementation: source/result map

Status: **accepted** at `4c77f6e` ([acceptance](../reviews/Burgers-B1/Acceptance.md)). Human review of the trusted statements pending.

Frozen contract: `specifications/Burgers-B1.md`. Approval record: `specifications/Burgers-B1-approval.md`.
Result bindings checked by `scripts/verify.py`: `specifications/Burgers-B1-results.json`. Toolchain: Lean v4.36.0.

B1 adds new modules only. No B0 source, no accepted Euler M1--M4 source and no M5 source is modified.

## Module map

| Module | Purpose |
| --- | --- |
| `CFDLean/Discrete/Periodic/TotalVariation.lean` | Periodic total variation, incremental-form update, the two generic lemmas |
| `CFDLean/Schemes/Scalar/Monotone.lean` | Monotone two-point-flux certificate `MonotoneFlux` |
| `CFDLean/Schemes/Burgers/RusanovStability.lean` | Rusanov monotonicity, incremental form, TVD and bounds under CFL |
| `CFDLean/Schemes/Burgers/StabilityControls.lean` | Exact small controls, including a CFL-violation example |
| `CFDLean/Verification/BurgersB1Challenge.lean` | Trusted B1 statements; imports only Mathlib |
| `CFDLean/Verification/BurgersB1Verify.lean` | Bridge: the implementation proves the trusted statements |
| `Challenges/BurgersB1.lean` | `lake comparator` challenge: the bridge theorem statements with `sorry` holes |

## Frozen result IDs

### B1-V — total variation and incremental form (definitions)

- `CFDLean.Scalar.FiniteVolume.totalVariation`
- `CFDLean.Scalar.FiniteVolume.incrementalUpdate`

### B1-H — generic Harten lemma

- `CFDLean.Scalar.FiniteVolume.incrementalUpdate_totalVariation_le`

The proof writes the difference of two updated neighbours as a combination of three old differences with the
coefficients `1 - C_i - D_i`, `C_{i+1}`, `D_{i-1}`, takes absolute values, and reindexes the periodic sums
(`Grid.sum_next`, `Grid.sum_prev` of B0). No flux appears.

### B1-X — generic local bounds

- `CFDLean.Scalar.FiniteVolume.incrementalUpdate_bounds`

The updated value is the convex combination `(1 - C_i - D_{i-1}) u_i + C_i u_{i+1} + D_{i-1} u_{i-1}`.

### B1-M — monotone flux certificate

- Definition: `CFDLean.Scalar.MonotoneFlux`
- Supporting: `CFDLean.Burgers.Rusanov.eval_mono_left`, `.eval_anti_right`
- Result: `CFDLean.Burgers.Rusanov.monotone`

The proof is a case analysis on the signs of the states and on which state has the larger absolute value. No
derivative is used. No B1 theorem consumes this certificate; later milestones do.

### B1-I — Rusanov step in incremental form

- Definitions: `CFDLean.Burgers.Rusanov.incrementC`, `.incrementD`
- Supporting: `.incrementC_nonneg`, `.incrementD_nonneg`, `.incrementC_add_incrementD`
- Results: `CFDLean.Burgers.Rusanov.abs_mean_le_waveSpeed`, `.step_eq_incrementalUpdate`

`step_eq_incrementalUpdate` has no hypothesis on `dx` or `dt` (with `dx = 0` both sides are `u i`, by Lean's
`x / 0 = 0`). The sign lemmas need `0 < dx` and `0 ≤ dt`.

### B1-S — TVD and bounds of the Rusanov Forward-Euler step

- Any periodic grid: `CFDLean.Burgers.Rusanov.step_totalVariation_le`, `.step_bounds`
- `ZMod N`: `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_totalVariation_le`, `.step_bounds`

Both are compositions: B1-I rewrites the step, then B1-H or B1-X applies with the sign lemmas and the CFL hypothesis.
The `ZMod N` theorems are instances of the general-grid theorems.

## Trusted boundary

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
| --- | --- | --- | --- |
| B1-M | `RusanovMonotone` | `rusanov_monotone` | `CFDLean.Burgers.Rusanov.monotone` |
| B1-H | `HartenTotalVariation` | `harten_total_variation` | `...FiniteVolume.incrementalUpdate_totalVariation_le` |
| B1-X | `IncrementalBounds` | `incremental_bounds` | `...FiniteVolume.incrementalUpdate_bounds` |
| B1-S | `RusanovTotalVariation` | `rusanov_total_variation` | `CFDLean.Burgers.Rusanov.step_totalVariation_le` |
| B1-S | `RusanovBounds` | `rusanov_bounds` | `CFDLean.Burgers.Rusanov.step_bounds` |

The trusted file writes the step in the direct form `u_i - (dt/dx)(F(u_i, u_{i+1}) - F(u_{i-1}, u_i))`. The bridge
lemma `rusanovStep_eq` proves that it is the implemented step. The trusted statements were checked against the
contract by a separate review agent (`reviews/Burgers-B1/TrustedStatements_Review.md`); no human reviewed them yet.

Checks: `scripts/verify.py` (bindings, modules, standard axioms, pinned hash and Mathlib-only imports of the trusted
file, bridge types), `KernelAudit.lean`, and
`lake comparator --paranoid --config Challenges/BurgersB1.comparator.json`.

## Notes on the hypotheses

- The CFL inequality is a hypothesis on the old state. B1 does not prove that it holds again after the step.
- `next` may be any permutation of the cells. For one cycle this is the usual periodic grid.
- The per-interface CFL hypothesis is equivalent to `dt · max_j |u_j| ≤ dx`, because every cell is the left state of
  one interface.
- CFL 1/2 is sufficient for the bounds, not sharp. The Lean proof bounds `C_i <= dt*a_i/dx` and `D_(i-1) <= dt*a_(i-1)/dx`, so it needs 1/2; the coefficient lemma alone holds up to 2/3. No sharper constant is claimed.
- `StabilityControls.lean` shows that total variation grows (2 to 6) and the bounds fail at `dt · a = 2 dx`.

## Exclusions

No B1 result implies multi-step stability, a CFL estimator, an entropy inequality, convergence, order of accuracy,
floating-point correctness, or array or parallel refinement.
