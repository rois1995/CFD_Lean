# Burgers B4 implementation: source/result map

Status: **accepted** at `4c77f6e` ([acceptance](../reviews/Burgers-B4/Acceptance.md)). Human review of the trusted statements pending.

Frozen contract: `specifications/Burgers-B4.md` (frozen by the agent, `specifications/Burgers-B4-approval.md`).
Result bindings checked by `scripts/verify.py`: `specifications/Burgers-B4-results.json`. Toolchain: Lean v4.36.0.

B4 adds new modules only. No B0--B3, accepted Euler M1--M4 or M5 source is modified.

## Module map

| Module | Purpose |
| --- | --- |
| `CFDLean/Entropy/Scalar/Certificates.lean` | Entropy-stability and entropy-conservation certificates of a two-point flux |
| `CFDLean/Entropy/Scalar/Periodic.lean` | Numerical entropy flux, cell entropy identity, inequality and equality, total entropy production |
| `CFDLean/Entropy/Scalar/Burgers.lean` | Square entropy of Burgers, entropy-conservative flux, Rusanov is entropy stable |
| `CFDLean/Entropy/Scalar/Controls.lean` | Exact small controls (the central flux is not entropy stable) |
| `CFDLean/Verification/BurgersB4Challenge.lean` | Trusted B4 statements; imports only Mathlib |
| `CFDLean/Verification/BurgersB4Verify.lean` | Bridge |
| `Challenges/BurgersB4.lean` | `lake comparator` challenge |

## Frozen result IDs

### B4-C — certificates

- Definitions: `CFDLean.Scalar.EntropyStable`, `CFDLean.Scalar.EntropyConservative`
- Result: `CFDLean.Scalar.EntropyConservative.entropyStable`

### B4-Q — numerical entropy flux

- Definition: `CFDLean.Scalar.FiniteVolume.entropyFlux`
- Result: `.entropyFlux_constant` (`Q = v f - ψ` on equal states for a consistent flux)

### B4-I — cell entropy relations

- Results: `.cell_entropy_identity` (no hypothesis; with `dx = 0` both sides are 0), `.cell_entropy_inequality`
  (`EntropyStable`, `dx > 0`), `.cell_entropy_equality` (`EntropyConservative`)

### B4-G — total entropy production

- Results: `.entropy_production_nonpos`, `.entropy_production_zero` (sum of B4-I and the periodic reindexing lemma
  `Grid.sum_prev` of B0)

### B4-B — Burgers, square entropy

- Definitions: `CFDLean.Burgers.entropyVariable` (`u`), `.entropyFluxFunction` (`u³/3`), `.entropyPotential` (`u³/6`),
  `CFDLean.Burgers.EntropyConservativeFlux.eval`, `.numericalFlux`
- Results: `CFDLean.Burgers.entropyPotential_eq`, `EntropyConservativeFlux.consistent`, `.entropyConservative`,
  `CFDLean.Burgers.Rusanov.eval_eq_entropyConservative_sub`, `Rusanov.entropyStable`

### B4-S — Rusanov operator

- Results: `CFDLean.Burgers.Rusanov.cell_entropy_inequality`, `.energy_production_nonpos` (instances of B4-I, B4-G)

## Trusted boundary

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
| --- | --- | --- | --- |
| B4-B | `EntropyConservativeFluxProperties` | `entropy_conservative_flux_properties` | `EntropyConservativeFlux.entropyConservative` (and `.consistent`) |
| B4-B | `RusanovEntropyStable` | `rusanov_entropy_stable` | `Rusanov.entropyStable` |
| B4-I | `CellEntropyInequality` | `cell_entropy_inequality` | `FiniteVolume.cell_entropy_inequality` |
| B4-G | `EntropyProductionNonpos` | `entropy_production_nonpos` | `FiniteVolume.entropy_production_nonpos` |
| B4-S | `RusanovEnergyProduction` | `rusanov_energy_production` | `Rusanov.energy_production_nonpos` |

The trusted file takes the flux as a plain function and the flux inequality as a hypothesis. It has no entropy `η` and
no entropy flux `q`: the potential `u³/6` is a literal. The equality versions, `entropyFlux_constant`,
`entropyPotential_eq` and the Rusanov decomposition have no trusted statement; the kernel audit and the result map
check them. The trusted statements were checked by a separate review agent
(`reviews/Burgers-B4/TrustedStatements_Review.md`); no human reviewed them yet.

Checks: `scripts/verify.py`, `KernelAudit.lean`,
`lake comparator --paranoid --config Challenges/BurgersB4.comparator.json`.

## What the results mean and do not mean

- `v_i L_i` is the time derivative of `η(u_i)` along `u' = L(u)` by the chain rule. That step is not in Lean. The
  theorems are algebraic inequalities for the operator `L`.
- `v` and `ψ` are arbitrary functions in the generic theorems. Convexity of `η` is not used and not required.
- For Burgers only the square entropy is treated.
- Nothing is proved for Forward Euler or SSP steps (a fully discrete entropy inequality needs more than these
  certificates), and nothing for MUSCL.
- `CFDLean.Num.antisymmetric_pairFlux` of the MC-N core is the same mechanism on general node sets. No adapter yet.
