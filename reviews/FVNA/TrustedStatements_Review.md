# FVNA: review of the trusted statement file

Date: 2026-11-27. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed file and
did not read the implementation proofs or the implementer's notes. This is not a human review and not the independent
implementation review.

Reviewed file: `CFDLean/Verification/FV1DNonuniformArrayChallenge.lean` at commit `60e7112`
(sha256 `309726e83eafae4da3d60603009cd7cbfd1b1fcd6908e340e6a6e83388be7181`), with its hash-pinned kernel inputs.
Reference: `specifications/FV1D-nonuniform-array.md`, `specifications/FV1D-nonuniform-array-approval.md` and, for the
underlying meanings, `specifications/FV1D-nonuniform.md`; wording compared with the accepted E0c and FVN trusted files.

## Verdict

**No mandatory findings.** All 13 statements say what the frozen contract requires. None is weaker or vacuous; every
strengthening is true and harmless.

| Statement | Contract | Result |
|---|---|---|
| `MusclEulerStepRefines`, `MusclSSPRK2StepRefines`, `MusclSSPRK3StepRefines` | FVNA-M | Faithful, every limiter including `none`. |
| `FirstOrderWeightedSum`, `MusclEulerWeightedSum`, `MusclSSPRK2WeightedSum`, `MusclSSPRK3WeightedSum` | FVNA-T (a), Burgers | Faithful. |
| `EulerFirstOrderWeightedSum` | FVNA-T (a), Euler | Faithful; components 0, 1, 2 are density, x-momentum, total energy. |
| `FirstOrderBounds`, `FirstOrderTotalVariation` | FVNA-T (b) | Faithful; the FVN-B cell and face conditions. |
| `MusclEulerRunStable`, `MusclSSPRK2RunStable`, `MusclSSPRK3RunStable` | FVNA-T (c) | Faithful. |

The reviewer checked the restated FVN step, the periodic cells and seam, the kernel rescaling over ℝ, the limiter and
`theta` definitions (identical to E0c), the SSP coefficients, the Burgers and Euler real models, the diagnostics
`sumArray` and `totalVariationArray` (already pinned by the accepted E0 statements), the weighted sum and the mesh
ratio, and found every hypothesis set satisfiable.

## Deliberate choices evaluated

1. FVNA-M and FVNA-T (a) have no `0 ≤ dt`: acceptable; both are algebraic identities true for every real `dt`.
2. Euler FVNA-T (a) for every `γ` without admissibility: acceptable; the contract asks none, and conservation needs only
   positive widths and equal sizes.
3. FVNA-T (c) for every number of steps `k`: acceptable; it is the contract's "`n` steps" (the letter `n` also names
   the cell count) and is true because the hypotheses are invariant.
4. FVNA-M gives positive `w` stored by `widths`; FVNA-T uses `widths[i]`: equivalent and faithful.

## Non-blocking remarks

1. Name the E0 statements `SumDiagnostic` and `TotalVariationDiagnostic` where the file justifies `sumArray` and
   `totalVariationArray`.
2. `weightedSum` uses `Array.zipWith`, which truncates to the shorter array; harmless because every use assumes equal
   sizes. A docstring note would help later reuse.
3. Record in the result map that FVNA-T (c) "`n` steps" means any number of steps.
4. No array-level `run` refinement is stated; the contract does not ask for one.

The remarks that would change the trusted file are not applied, so the reviewed hash stays valid.
