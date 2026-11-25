# Burgers E0 implementation: source/result map

Status: **implementation candidate; independent acceptance pending**.

Frozen contract: `specifications/Burgers-E0.md` (frozen by the agent, `specifications/Burgers-E0-approval.md`).
Result bindings checked by `scripts/verify.py`: `specifications/Burgers-E0-results.json`. Toolchain: Lean v4.36.0.

E0 adds new modules only. No B0--B4, accepted Euler M1--M4 or M5 source is modified.

## Run it

```bash
lake exe burgers1d                 # N = 200, steps = 200, cfl = 0.4
lake exe burgers1d 400 1000 0.5    # N, steps, cfl
lake exe burgers1d 50 100 0.4 --dump
```

The program prints `N`, `steps`, `dt`, and for the initial and final state `sum · dx`, minimum, maximum and total
variation. It runs the kernel with `Float`. The theorems are about the same kernel with real numbers.

## Module map

| Module | Purpose |
| --- | --- |
| `CFDLean/Exec/Kernel.lean` | Arithmetic class `Scalar`, the array kernel, the `Float` instance. No imports. |
| `CFDLean/Exec/RealScalar.lean` | The `ℝ` instance of the kernel arithmetic |
| `CFDLean/Exec/Refinement.lean` | Representation relation, refinement theorems, diagnostics, transfer of the B2 results |
| `Main.lean` | Driver of the executable `burgers1d`; imports only the kernel |
| `CFDLean/Verification/BurgersE0Challenge.lean` | Trusted E0 statements; imports Mathlib, the kernel and the `ℝ` instance |
| `CFDLean/Verification/BurgersE0Verify.lean` | Bridge |
| `Challenges/BurgersE0.lean` | `lake comparator` challenge |

The dependency direction is: the mathematical modules do not import `CFDLean/Exec`; `Kernel.lean` imports nothing;
`Refinement.lean` imports the kernel and `CFDLean.Schemes.Burgers.RusanovSSP`.

## Frozen result IDs

### E0-K — kernel

- Definitions: `CFDLean.Exec.Scalar` (class), `Scalar.burgersFlux`, `Scalar.rusanov`, `eulerStepArray`, `axpby`,
  `ssprk2StepArray`, `ssprk3StepArray`, `run`, `sumArray`, `maxArray`, `minArray`, `totalVariationArray`,
  `instScalarReal`
- Results: `eulerStepArray_size`, `axpby_size`, `ssprk3StepArray_size`, `run_size`
- Supporting: `succ_mod_lt`, `pred_mod_lt` (the periodic indices are in bounds; no default value is used)

The kernel builds new arrays with `Array.ofFn` and `Array.zipWith`. `axpby` on arrays of different sizes returns the
smaller size. `run step (k+1) u = run step k (step u)`.

### E0-R — representation

- Definitions: `CFDLean.Exec.finGrid` (the periodic grid on `Fin n`, successor `i + 1`), `Represents`
- Results: `rusanov_eq`, `represents_iff_eq_ofFn`
- Supporting: `finGrid_next_val`, `finGrid_prev_val`, `represents_ofFn`, `represents_self`, `Represents.getElem_eq`

### E0-S — one-step refinement

- Results: `eulerStepArray_refines`, `axpby_refines`, `ssprk2StepArray_refines`, `ssprk3StepArray_refines`

The SSP refinements are one term each: the Euler refinement and the linear-combination refinement, composed in the
order of the Shu-Osher form. The `ℝ` instance gives the coefficients as the literals of `CFDLean.Time.SSP`.

### E0-N — many steps

- Result: `run_refines`

### E0-D — diagnostics

- Results: `sumArray_eq`, `totalVariationArray_eq`

### E0-T — transfer of the B2 theorems to arrays

- Definitions: `EntriesBetween`, `RefinedBy`
- Results: `run_eulerStepArray_bounds`, `run_ssprk3StepArray_bounds`, `run_eulerStepArray_sum`,
  `run_ssprk3StepArray_sum`, `run_eulerStepArray_totalVariation_le`, `run_ssprk3StepArray_totalVariation_le`
- Supporting: `self_mem_boundedStates`, `run_entriesBetween`, `run_sumArray`, `run_totalVariationArray_le`,
  `eulerStepArray_refinedBy`, `ssprk3StepArray_refinedBy`

These hold for every array, also the empty one. Each is: the array represents its own cell function, the kernel run
represents the iterated scheme (E0-N), the B2 theorem (`eulerStep_iterate_stable`, `ssprk3Step_iterate_stable`,
`eulerStep_sum`, `ssprk3Step_sum`) holds for the scheme, the diagnostic is the mathematical quantity (E0-D).

### E0-X — executable

- `[[lean_exe]] burgers1d` in `lakefile.toml`, root `Main.lean`, with the instance `CFDLean.Exec.instScalarFloat`.
- Built and run in CI. Reference output for `burgers1d 200 200 0.4`:

```text
N = 200  steps = 200  cfl = 0.400000  dx = 5.000000000000e-3  dt = 1.333443002369e-3
initial: sum*dx = 5.000000000000e-1  min = -4.998766324817e-1  max = 1.499876632482e0  TV = 3.999506529927e0
final  : sum*dx = 5.000000000000e-1  min = -4.783885174983e-1  max = 1.457006232256e0  TV = 3.870789499509e0
sum drift (final - initial) * dx = -4.831690603169e-15
```

  An independent Python script gave the same numbers to 13 digits (prototype check). This is a test, not a proof.

## Trusted boundary

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
| --- | --- | --- | --- |
| E0-R | `KernelFluxIsRusanov` | `kernel_flux_is_rusanov` | `rusanov_eq` |
| E0-S | `EulerStepRefines`, `SSPRK3StepRefines` | `euler_step_refines`, `ssprk3_step_refines` | `eulerStepArray_refines`, `ssprk3StepArray_refines` |
| E0-N | `SSPRK3RunRefines` | `ssprk3_run_refines` | `run_refines` |
| E0-D | `SumDiagnostic`, `TotalVariationDiagnostic` | `sum_diagnostic`, `total_variation_diagnostic` | `sumArray_eq`, `totalVariationArray_eq` |
| E0-T | `SSPRK3RunBounds`, `SSPRK3RunSum`, `SSPRK3RunTotalVariation` | `ssprk3_run_*` | `run_ssprk3StepArray_*` |

The trusted file has two statements more than the contract table (the two E0-D statements). The total-variation
transfer is stated with the kernel diagnostic, and `TotalVariationDiagnostic` says what that diagnostic is.

The trusted file restates the scheme on `Fin n` with the cyclic indices `i + 1`, `i - 1` and its own representation
relation; the bridge proves that these are the implemented ones (`eulerStep_eq`, `represents_iff`). The kernel and the
`ℝ` instance are imported by the trusted file because the statements are about them. `scripts/verify.py` pins the
hashes of both (`trusted_inputs`) and checks that they import only Mathlib or each other. The trusted statements were
checked by a separate review agent (`reviews/Burgers-E0/TrustedStatements_Review.md`); no human reviewed them yet.

Checks: `scripts/verify.py`, `KernelAudit.lean` (the kernel and its `Float` instance are in the audited closure: no
axiom outside the three standard ones, no unsafe declaration),
`lake comparator --paranoid --config Challenges/BurgersE0.comparator.json`.

## What is not verified

- `Float` arithmetic: no rounding bound, and no statement that a `Float` run keeps bounds, sum or total variation.
- The driver `Main.lean`: argument parsing, initial data, the choice of `dt`, printing.
- The Lean compiler, the runtime, the C toolchain.
- Performance. The kernel allocates new arrays in every stage.

## Design notes for E1--E4

- E1 (floating point): the `Scalar` class is the place to attach an error model. A statement of the form "the `Float`
  run stays within a bound of the real run" needs a formal model of IEEE arithmetic, which Lean core does not provide
  for `Float` (its operations are opaque).
- E2--E4 (parallel, GPU, MPI): the refinement is stated through `Represents` and `RefinedBy`, which do not depend on
  how an array is computed. A partitioned kernel with halo cells can be proved to refine the same `eulerStepArray`
  (local stencil correctness under valid halos), without a change of the mathematical layer.
