# Burgers B0 implementation: source/result map

Status: **implementation candidate; independent acceptance pending**.

Frozen contract: `specifications/Burgers-B0.md`.

Approval record: `specifications/Burgers-B0-approval.md`.

The declarations keep the namespace `CFDLean.Burgers` and their names and types. Since the move to the layered folders
of `main` (`specifications/Burgers-B0-layout.md`) each module sits in the folder of its catalog layer. The accepted
Euler M1--M4 mathematical source files and the M5 sources are not modified. Toolchain: Lean v4.36.0.

Result bindings checked by `scripts/verify.py`: `specifications/Burgers-B0-results.json`.

## Module map

| Module | Purpose |
| --- | --- |
| `CFDLean/Physics/Scalar/ConservationLaw.lean` | Generic exact-real scalar conservation-law object |
| `CFDLean/Physics/Burgers/Flux.lean` | Burgers physical flux and conservation law |
| `CFDLean/Discrete/Periodic/Grid.lean` | Generic periodic equivalence and `ZMod` periodic-grid instance |
| `CFDLean/Discrete/Periodic/FiniteVolume.lean` | Generic first-order periodic flux-difference semidiscretization |
| `CFDLean/Discrete/Periodic/Conservation.lean` | Generic finite-sum telescoping and semidiscrete conservation |
| `CFDLean/Schemes/Scalar/NumericalFlux.lean` | Generic two-point numerical flux and separate consistency certificate |
| `CFDLean/Schemes/Burgers/Rusanov.lean` | Local Lax--Friedrichs/Rusanov flux for Burgers and its consistency |
| `CFDLean/Schemes/Burgers/RusanovForwardEuler.lean` | Assembled Burgers/Rusanov/Forward-Euler scheme certificates |
| `CFDLean/Schemes/Burgers/Controls.lean` | Exact small controls |
| `CFDLean/Time/ForwardEuler.lean` | Generic Forward-Euler composition results |
| `CFDLean/Verification/BurgersB0Challenge.lean` | Trusted B0 statements; imports only Mathlib |
| `CFDLean/Verification/BurgersB0Verify.lean` | Bridge: the implementation proves the trusted statements |
| `Challenges/BurgersB0.lean` | `lake comparator` challenge: the bridge theorem statements with `sorry` holes |

## Frozen result IDs

### B0-P — Burgers physical flux and equation convention

Definitions:

- `CFDLean.Burgers.physicalFlux`
- `CFDLean.Burgers.law`

The selected flux is exactly (f(u)=u^2/2). No viscous/source term or multidimensional system is represented by B0.

### B0-F — Rusanov definition and consistency

Definitions:

- `CFDLean.Burgers.Rusanov.waveSpeed`
- `CFDLean.Burgers.Rusanov.eval`
- `CFDLean.Burgers.Rusanov.numericalFlux`

Result:

- `CFDLean.Burgers.Rusanov.consistent`

The evaluator is the frozen local Lax--Friedrichs/Rusanov expression with (a=max(|u_L|,|u_R|)). The theorem proves equal-state consistency only; it does not claim monotonicity, entropy stability or a CFL condition.

### B0-C — generic periodic conservation

Definitions:

- `CFDLean.Burgers.Core.PeriodicGrid`
- `CFDLean.Burgers.Core.PeriodicGrid.prev`
- `CFDLean.Burgers.Core.zmodGrid`
- `CFDLean.Burgers.FiniteVolume.interfaceFlux`
- `CFDLean.Burgers.FiniteVolume.rhs`

Supporting reindexing results:

- `CFDLean.Burgers.Core.PeriodicGrid.sum_prev`
- `CFDLean.Burgers.Core.PeriodicGrid.sum_next`

Results:

- `CFDLean.Burgers.FiniteVolume.fluxDifference_sum_zero`
- `CFDLean.Burgers.FiniteVolume.rhs_sum_zero`

The cancellation theorem is numerical-flux generic and uses only finite cyclic reindexing. Consistency is not an assumption.

### B0-K — constant-state semidiscrete preservation

Result:

- `CFDLean.Burgers.FiniteVolume.rhs_constant`

The public theorem consumes the separate `Core.Consistent` certificate and proves zero semidiscrete RHS for a constant state.

### B0-T — generic Forward Euler composition

Definition:

- `CFDLean.Burgers.Time.step`

Results:

- `CFDLean.Burgers.Time.step_zero_rhs`
- `CFDLean.Burgers.Time.step_constant`
- `CFDLean.Burgers.Time.step_sum`

These are exact algebraic one-step statements. No temporal order or stability theorem is claimed.

### B0-S — assembled Burgers/Rusanov/Forward-Euler certificates

Definitions:

- `CFDLean.Burgers.Schemes.RusanovForwardEuler.grid`
- `CFDLean.Burgers.Schemes.RusanovForwardEuler.semidiscrete`
- `CFDLean.Burgers.Schemes.RusanovForwardEuler.step`

Results:

- `CFDLean.Burgers.Schemes.RusanovForwardEuler.semidiscrete_constant`
- `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_preserves_constant`
- `CFDLean.Burgers.Schemes.RusanovForwardEuler.semidiscrete_sum_zero`
- `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_preserves_sum`
- `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_preserves_integral`

The assembled proofs compose the generic finite-volume/time results with the Rusanov consistency certificate. They do not re-prove conservation or constant-state preservation from Burgers-specific algebra.

## Trusted boundary and exclusions

Project proof terms are intended to be checked by the pinned Lean kernel and Mathlib dependency.

The B0 agent/workflow is not trusted as a source of mathematical truth; it only proposes proof terms and build results.

Trusted statements and their bridge theorems (`CFDLean.Verification.BurgersB0Challenge` / `.BurgersB0Verify`):

| ID | Trusted statement | Bridge theorem | Implementation theorem used |
| --- | --- | --- | --- |
| B0-F | `RusanovConsistency` | `rusanov_consistency` | `CFDLean.Burgers.Rusanov.consistent` |
| B0-C | `PeriodicConservation` | `periodic_conservation` | `CFDLean.Burgers.FiniteVolume.rhs_sum_zero` |
| B0-K | `ConstantRhs` | `constant_rhs` | `CFDLean.Burgers.FiniteVolume.rhs_constant` |
| B0-T | `ForwardEulerSum` | `forward_euler_sum` | `CFDLean.Burgers.Time.step_sum` |

The trusted statement file does not state B0-P (definitions only), the constant-state part of B0-T, or the assembled
`ZMod N` scheme B0-S. Those results are checked by the kernel audit and the result map, not by a separate statement.

Checks:

- `scripts/verify.py`: result bindings, modules, standard axioms, hash of the trusted statement file, its
  Mathlib-only imports, bridge theorem types;
- `KernelAudit.lean`: no project axiom, only `propext`, `Classical.choice`, `Quot.sound`, no unsafe dependency;
- `lake comparator --paranoid --config Challenges/BurgersB0.comparator.json`: each bridge theorem has the statement
  of the challenge and is accepted by Lean's kernel and five external checkers in a `bwrap` sandbox.

No B0 result implies:

- CFL stability;
- TVD or monotonicity;
- entropy stability or entropy-solution convergence;
- positivity;
- temporal or spatial order;
- floating-point correctness;
- array or generated-code refinement.

Those require later frozen contracts.
