# Burgers B2 implementation: source/result map

Status: **implementation candidate; independent acceptance pending**.

Frozen contract: `specifications/Burgers-B2.md` (frozen by the agent, `specifications/Burgers-B2-approval.md`).
Result bindings checked by `scripts/verify.py`: `specifications/Burgers-B2-results.json`. Toolchain: Lean v4.36.0.

B2 adds new modules only. No B0, B1, accepted Euler M1--M4 or M5 source is modified.

## Module map

| Module | Purpose |
| --- | --- |
| `CFDLean/Time/SSP.lean` | SSPRK2, SSPRK3 over a one-step map; generic composition, iteration, fixed points, linear invariants |
| `CFDLean/Discrete/Periodic/Convexity.lean` | Bounded states are convex; total variation is convex; total sum as a linear functional |
| `CFDLean/Schemes/Burgers/RusanovSSP.lean` | Rusanov Euler map on bounded states; multi-step results for Euler, SSPRK2, SSPRK3 |
| `CFDLean/Schemes/Burgers/SSPControls.lean` | Exact small controls |
| `CFDLean/Verification/BurgersB2Challenge.lean` | Trusted B2 statements; imports only Mathlib |
| `CFDLean/Verification/BurgersB2Verify.lean` | Bridge |
| `Challenges/BurgersB2.lean` | `lake comparator` challenge |

## Frozen result IDs

### B2-R — SSP Runge-Kutta steps

- Definitions: `CFDLean.Time.SSP.ssprk2`, `.ssprk3` (Shu-Osher form over a map `E : V → V`, `V` a real vector space)
- Result: `CFDLean.Time.SSP.ssprk2_forwardEuler` (SSPRK2 of Forward Euler is Heun's method)

### B2-C — generic SSP composition

- `CFDLean.Time.SSP.ssprk2_mem`, `.ssprk3_mem` (Mathlib `Convex`)
- `CFDLean.Time.SSP.ssprk2_le`, `.ssprk3_le` (Mathlib `ConvexOn`)

Each proof applies the convexity inequality once per convex combination of the Shu-Osher form.

### B2-N — generic iteration

- `CFDLean.Time.SSP.iterate_mem`, `.iterate_le` (induction on the number of steps; no structure on `V`)

### B2-L — fixed points and linear invariants

- `CFDLean.Time.SSP.ssprk2_fixed`, `.ssprk3_fixed`, `.ssprk2_linear`, `.ssprk3_linear`

### B2-B — building blocks for Burgers

- Definitions: `CFDLean.Scalar.FiniteVolume.boundedStates`, `.totalSum`, `CFDLean.Burgers.Rusanov.eulerStep`
- Supporting: `.totalSum_apply`, `Rusanov.eulerStep_sum`, `Rusanov.eulerStep_constant` (B0 results for the Euler map),
  `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_eq_eulerStep` (the `ZMod N` step of B0 is the Euler map on `grid`)
- Results: `FiniteVolume.boundedStates_convex`, `FiniteVolume.totalVariation_convexOn`,
  `Rusanov.waveSpeed_le_of_bounds`, `Rusanov.eulerStep_mem`, `Rusanov.eulerStep_totalVariation_le`

`eulerStep_mem` and `eulerStep_totalVariation_le` are the B1 theorems `step_bounds` and `step_totalVariation_le`: the
bounds `m ≤ u ≤ M` give `a_i ≤ max(|m|, |M|)`, so `2 · dt · max(|m|, |M|) ≤ dx` gives both B1 CFL hypotheses.

### B2-S — multi-step stability, conservation, constants

- Definitions: `CFDLean.Burgers.Rusanov.ssprk2Step`, `.ssprk3Step`
- Results: `Rusanov.eulerStep_iterate_stable`, `.ssprk2Step_iterate_stable`, `.ssprk3Step_iterate_stable`,
  `.ssprk2Step_sum`, `.ssprk3Step_sum`, `.ssprk2Step_constant`, `.ssprk3Step_constant`

All are compositions: B2-B gives the invariant set and the non-increasing functional for the Euler map, B2-C lifts them
to the SSP steps, B2-N iterates. Conservation is B2-L with the linear functional `totalSum`; constant states are B2-L
with the B0 fixed point.

## Trusted boundary

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
| --- | --- | --- | --- |
| B2-C | `SSPRK2Convex`, `SSPRK3Convex` | `ssprk2_convex`, `ssprk3_convex` | `Time.SSP.ssprk2_le`, `.ssprk3_le` (with `_mem`) |
| B2-S | `EulerMultiStep` | `euler_multi_step` | `Rusanov.eulerStep_iterate_stable` |
| B2-S | `SSPRK2MultiStep`, `SSPRK3MultiStep` | `ssprk2_multi_step`, `ssprk3_multi_step` | `Rusanov.ssprk2Step_iterate_stable`, `.ssprk3Step_iterate_stable` |
| B2-S | `SSPRK2Conservation`, `SSPRK3Conservation` | `ssprk2_conservation`, `ssprk3_conservation` | `Rusanov.ssprk2Step_sum`, `.ssprk3Step_sum` |

The trusted file restates the Rusanov flux, the Euler step in direct form, the total variation and the two SSP
steps. The bridge lemma `eulerStep_eq` proves that the trusted Euler step is the implemented one. The trusted
statements were checked by a separate review agent (`reviews/Burgers-B2/TrustedStatements_Review.md`); no human
reviewed them yet.

Checks: `scripts/verify.py`, `KernelAudit.lean`,
`lake comparator --paranoid --config Challenges/BurgersB2.comparator.json`.

## Notes on the hypotheses

- One `dt` for all steps and stages. The hypothesis `2 · dt · max(|m|, |M|) ≤ dx` uses bounds of the initial state.
- CFL 1/2 comes from the B1 bounds theorem. A sharper B1 constant would carry over without a change of B2 proofs.
- The SSP coefficient of SSPRK2 and SSPRK3 is 1: the SSP step is stable under the same `dt` as Forward Euler.

## Exclusions

No B2 result implies an order of accuracy of the Runge-Kutta methods, variable time steps, an entropy inequality,
convergence, floating-point correctness, or array or parallel refinement.
