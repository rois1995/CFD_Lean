# Burgers E0b implementation: source/result map

Status: **accepted** at `4c77f6e` ([acceptance](../reviews/Burgers-E0b/Acceptance.md)). Human review of the trusted statements pending.

Frozen contract: `specifications/Burgers-E0b.md` (frozen by the agent, `specifications/Burgers-E0b-approval.md`; the
user chose the milestone). Result bindings checked by `scripts/verify.py`: `specifications/Burgers-E0b-results.json`.
Toolchain: Lean v4.36.0.

E0b adds new modules and changes the unverified driver `Main.lean`. The E0 kernel, the class `Scalar`, the real
instance and every B0--B4, E0, Euler M1--M5 source are unchanged.

## Run it

```bash
lake exe burgers1d 200 200 0.15 --limiter minmod     # MUSCL-minmod with SSPRK3
lake exe burgers1d 200 200 0.4              # first order, as in E0
```

Since E0c the limiter is chosen with `--limiter NAME`, and `--muscl` alone is the unlimited scheme; at the time of E0b
`--muscl` meant minmod. The output below is the E0b format; the numbers are the same with `--limiter minmod`.
The first output line names the scheme. The note line gives the proved hypothesis for real arithmetic: `cfl <= 0.5`
for the first-order scheme, `cfl <= 1/6` for MUSCL. Exit codes: 0 normal, 1 bad arguments, 2 non-finite result.

## Module map

| Module | Purpose |
| --- | --- |
| `CFDLean/Exec/MusclKernel.lean` | Comparison-free `min` and `minmod`, the MUSCL array kernel. Imports only the E0 kernel. |
| `CFDLean/Exec/MusclRefinement.lean` | The kernel limiter is minmod; refinement theorems; transfer of the B3 results |
| `Main.lean` | Driver: flag `--muscl` |
| `CFDLean/Verification/BurgersE0bChallenge.lean` | Trusted E0b statements; imports Mathlib, the two kernels and the `ℝ` instance |
| `CFDLean/Verification/BurgersE0bVerify.lean` | Bridge |
| `Challenges/BurgersE0b.lean` | `lake comparator` challenge |

## Frozen result IDs

### E0b-K — MUSCL kernel

- Definitions: `CFDLean.Exec.Scalar.min`, `Scalar.minmod`, `nextIdx`, `prevIdx`, `slopeAt`, `facePlus`, `faceMinus`,
  `musclEulerStepArray`, `musclSsprk2StepArray`
- Results: `musclEulerStepArray_size`, `musclSsprk2StepArray_size`, `musclSsprk3StepArray_size`

`minmod a b = max 0 (min a b) + min 0 (max a b)` with `min a b = -max (-a) (-b)`: the class `Scalar` has no order
relation. The kernel evaluates a slope each time a face state needs it (up to three times per cell and stage).

### E0b-L — the kernel limiter is minmod

- Results: `min_eq`, `minmod_eq` (real arithmetic; `minmod_eq` is a case split on the signs)

### E0b-S — refinement

- Results: `musclEulerStepArray_refines`, `musclSsprk2StepArray_refines`, `musclSsprk3StepArray_refines`
- Supporting: `nextIdx_cast`, `prevIdx_cast`, `Represents.get`, `slopeAt_eq`, `facePlus_eq`, `faceMinus_eq`,
  `musclEulerStepArray_refinedBy`, `musclSsprk3StepArray_refinedBy`

`faceMinus_eq` is stated at the previous cell: the mathematical `rightState i` of B3 is the left face of cell
`next i`. The SSP refinements compose the Euler refinement with `axpby_refines` of E0. Refinement of `k` steps is
`run_refines` of E0.

### E0b-T — transfer of the B3 theorems to arrays

- Results: `run_musclEulerStepArray_bounds`, `run_musclSsprk3StepArray_bounds`, `run_musclEulerStepArray_sum`,
  `run_musclSsprk3StepArray_sum`, `run_musclEulerStepArray_totalVariation_le`,
  `run_musclSsprk3StepArray_totalVariation_le`

They use the generic transfer lemmas of E0 and the B3 theorems `musclEulerStep_iterate_stable`,
`musclSsprk3Step_iterate_stable`, `musclEulerStep_sum`, `musclSsprk3Step_sum` with `minmod_minmodBounded`. Hypothesis
for bounds and total variation: `6 · dt · max(|m|, |M|) ≤ dx`.

### E0b-X — executable

- Definition run by the flag: `musclSsprk3StepArray`. Built and run in CI. Reference output for
  `burgers1d 200 200 0.15 --muscl` (E0b; now `--limiter minmod`):

```text
N = 200  steps = 200  cfl = 0.150000  dx = 5.000000000000e-3  dt = 5.000411258885e-4  scheme = MUSCL-minmod
note: Float arithmetic is not verified. With real arithmetic the bounds are proved for cfl <= 1/6; this run is inside that range.
initial: sum*dx = 5.000000000000e-1  min = -4.998766324817e-1  max = 1.499876632482e0  TV = 3.999506529927e0
final  : sum*dx = 5.000000000000e-1  min = -4.984049443367e-1  max = 1.496448265916e0  TV = 3.989706420506e0
sum drift (final - initial) * dx = -5.186961971049e-15
```

  An independent Python script (textbook minmod) gave the same 200 final values bit for bit (prototype check). The
  first-order scheme at the same time gives max 1.48565 and TV 3.96160: MUSCL is less diffusive. Tests, not proofs.

## Trusted boundary

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
| --- | --- | --- | --- |
| E0b-L | `KernelMinmodIsMinmod` | `kernel_minmod_is_minmod` | `minmod_eq` |
| E0b-S | `MusclEulerStepRefines`, `MusclSSPRK3StepRefines`, `MusclSSPRK3RunRefines` | `muscl_euler_step_refines`, `muscl_ssprk3_step_refines`, `muscl_ssprk3_run_refines` | `musclEulerStepArray_refines`, `musclSsprk3StepArray_refines` |
| E0b-T | `MusclSSPRK3RunBounds`, `MusclSSPRK3RunSum`, `MusclSSPRK3RunTotalVariation` | `muscl_ssprk3_run_*` | `run_musclSsprk3StepArray_*` |

The trusted file restates minmod and the MUSCL step on `Fin n` in the cell-based form with cyclic indices; the bridge
proves that they are the implemented ones. `scripts/verify.py` pins the three trusted inputs (E0 kernel, real
instance, MUSCL kernel). The sum and total-variation statements use the E0 diagnostics; the E0 trusted statements
`SumDiagnostic` and `TotalVariationDiagnostic` say what these compute. The trusted statements were checked by a
separate review agent (`reviews/Burgers-E0b/TrustedStatements_Review.md`); no human reviewed them yet.

Checks: `scripts/verify.py`, `KernelAudit.lean`,
`lake comparator --paranoid --config Challenges/BurgersE0b.comparator.json`.

## What is not verified

`Float` arithmetic (with `Float` the kernel `minmod` returns 0 or its first argument when an argument is NaN; a NaN
cell still spreads through the face states, and the driver reports it), the driver, the compiler, performance. The CFL
hypothesis 1/6 is sufficient, not sharp; a run at `cfl = 0.4` stayed in bounds in a test, without a proof.
