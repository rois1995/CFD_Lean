# Burgers E0b: executable MUSCL array kernel and its refinement

Status: **frozen for implementation on 2026-11-26 by the agent** (`specifications/Burgers-E0b-approval.md`). The user
chose this milestone; no human approved the statements of this contract.

Base: Burgers B0--B4 and E0 on `main`. Toolchain: Lean v4.36.0. No new dependency.

## Purpose

E0 gave an executable array kernel for the first-order scheme and proved that, with real arithmetic, it computes the
mathematical scheme. E0b does the same for the second-order MUSCL scheme with the minmod limiter of B3, so that the
B3 theorems (bounds, total variation, conservation) hold for the arrays, and `burgers1d --muscl` runs it.

## Frozen decisions

1. **The E0 kernel and the class `Scalar` do not change.** The MUSCL kernel is a new module that imports only the E0
   kernel. `CFDLean/Exec/Kernel.lean` and `CFDLean/Exec/RealScalar.lean` keep their pinned hashes.
2. **Minmod without a comparison.** `Scalar` has `max`, negation, zero and addition, and no order relation. The kernel
   uses `min a b = -max (-a) (-b)` and `minmod a b = max 0 (min a b) + min 0 (max a b)`. With real arithmetic this is
   the minmod of B3 (proved).
3. **Scheme.** MUSCL reconstruction with minmod and the Rusanov flux, in the cell-based form of the B3 trusted file:
   face states `u_i ± σ_i / 2`, step `u_i - (dt/dx)(F(u_i⁺, u_{i+1}⁻) - F(u_{i-1}⁺, u_i⁻))`; Forward Euler, SSPRK2,
   SSPRK3 in Shu-Osher form with the E0 linear combination `axpby`.
4. **Same representation and grid as E0**: `Represents`, `finGrid`, `run`, `RefinedBy`, and the E0 diagnostics.
5. **What is trusted and not proved** is the same as in E0: `Float`, the driver, the compiler.

## Frozen Lean statements

Kernel (`CFDLean/Exec/MusclKernel.lean`, namespace `CFDLean.Exec`, `α` with `[Scalar α]`):

```lean
def Scalar.min (a b : α) : α := -Scalar.max (-a) (-b)
def Scalar.minmod (a b : α) : α := Scalar.max 0 (Scalar.min a b) + Scalar.min 0 (Scalar.max a b)
def nextIdx {n : Nat} (i : Fin n) : Fin n := ⟨(i.val + 1) % n, succ_mod_lt i⟩
def prevIdx {n : Nat} (i : Fin n) : Fin n := ⟨(i.val + n - 1) % n, pred_mod_lt i⟩
def slopeAt (u : Array α) (i : Fin u.size) : α :=
  Scalar.minmod (u[i] - u[prevIdx i]) (u[nextIdx i] - u[i])
def facePlus (u : Array α) (i : Fin u.size) : α := u[i] + slopeAt u i / two
def faceMinus (u : Array α) (i : Fin u.size) : α := u[i] - slopeAt u i / two
def musclEulerStepArray (dx dt : α) (u : Array α) : Array α :=
  Array.ofFn fun i : Fin u.size =>
    u[i] + dt * (-(rusanov (facePlus u i) (faceMinus u (nextIdx i)) -
      rusanov (facePlus u (prevIdx i)) (faceMinus u i)) / dx)
def musclSsprk2StepArray (dx dt : α) (u : Array α) : Array α :=
  axpby half u half (musclEulerStepArray dx dt (musclEulerStepArray dx dt u))
def musclSsprk3StepArray (dx dt : α) (u : Array α) : Array α :=
  axpby third u twoThirds (musclEulerStepArray dx dt
    (axpby threeQuarters u quarter (musclEulerStepArray dx dt (musclEulerStepArray dx dt u))))
```

Refinement (`CFDLean/Exec/MusclRefinement.lean`, namespace `CFDLean.Exec`, real arithmetic):

```lean
-- E0b-L
theorem min_eq (a b : ℝ) : Scalar.min a b = min a b
theorem minmod_eq (a b : ℝ) : Scalar.minmod a b = CFDLean.Scalar.FiniteVolume.minmod a b

-- E0b-S
theorem musclEulerStepArray_refines {n : ℕ} [NeZero n] (dx dt : ℝ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) :
    Represents (musclEulerStepArray dx dt a)
      (Burgers.Rusanov.musclEulerStep (finGrid n) dx dt CFDLean.Scalar.FiniteVolume.minmod u)
theorem musclSsprk2StepArray_refines   -- against Burgers.Rusanov.musclSsprk2Step (finGrid n) dx dt minmod
theorem musclSsprk3StepArray_refines   -- against Burgers.Rusanov.musclSsprk3Step (finGrid n) dx dt minmod

-- E0b-T   (for step in {musclEulerStepArray, musclSsprk3StepArray})
theorem run_step_bounds (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    EntriesBetween m M (run (step dx dt) k a)
theorem run_step_sum (dx dt : ℝ) (hdx : dx ≠ 0) (a : Array ℝ) (k : ℕ) :
    sumArray (run (step dx dt) k a) = sumArray a
theorem run_step_totalVariation_le (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    totalVariationArray (run (step dx dt) k a) ≤ totalVariationArray a
```

Size lemmas and the `RefinedBy` forms are supporting results with any name.

## Executable (E0b-X)

`burgers1d` gets the flag `--muscl`. With it the program runs `musclSsprk3StepArray`, without it the E0 kernel as
before. The first output line names the scheme. The note line gives the proved hypothesis for the scheme in use:
`cfl ≤ 0.5` (first order) or `cfl ≤ 1/6` (MUSCL), both for real arithmetic. Built and run in CI. Not a theorem.

## Frozen module layout

```text
CFDLean/Exec/MusclKernel.lean                      E0b-K: comparison-free minmod, MUSCL array kernel (imports the E0 kernel only)
CFDLean/Exec/MusclRefinement.lean                  E0b-L, E0b-S, E0b-T
Main.lean                                          E0b-X: `--muscl`
CFDLean/Verification/BurgersE0bChallenge.lean      trusted statements
CFDLean/Verification/BurgersE0bVerify.lean         bridge
Challenges/BurgersE0b.lean                         `lake comparator` challenge
```

## Trusted statements

The trusted statement file imports Mathlib and the three hash-pinned trusted inputs: the E0 kernel, the real instance
and the MUSCL kernel. It restates the minmod function, the MUSCL step on `Fin n` in cell-based form with cyclic
indices, the SSPRK3 step and the representation relation, and states:

| Trusted statement | Content | Result ID |
| --- | --- | --- |
| `KernelMinmodIsMinmod` | with real arithmetic the kernel `minmod` is the minmod function | E0b-L |
| `MusclEulerStepRefines` | the kernel MUSCL Euler step computes the mathematical one | E0b-S |
| `MusclSSPRK3StepRefines` | the same for the SSPRK3 kernel step | E0b-S |
| `MusclSSPRK3RunRefines` | `k` kernel steps compute `k` mathematical steps | E0b-S |
| `MusclSSPRK3RunBounds` | with `dx > 0`, `dt ≥ 0`, entries in `[m, M]`, `6 · dt · max(|m|, |M|) ≤ dx`: entries stay in `[m, M]` after `k` kernel SSPRK3 steps | E0b-T |
| `MusclSSPRK3RunSum` | with `dx ≠ 0` the kernel sum diagnostic is unchanged after `k` steps | E0b-T |
| `MusclSSPRK3RunTotalVariation` | under the hypotheses of the bounds statement the kernel total-variation diagnostic does not increase | E0b-T |

The two diagnostics are the E0 ones; the E0 trusted statements `SumDiagnostic` and `TotalVariationDiagnostic` say what
they compute.

## Explicitly excluded from E0b

- anything about `Float`; correctness of the driver and of the compiler;
- other limiters, other fluxes, non-periodic boundaries;
- performance (the kernel computes each slope up to three times), in-place updates, parallel execution;
- second-order accuracy.

## Frozen E0b result IDs

| ID | Required result |
| --- | --- |
| E0b-K | MUSCL array kernel over the E0 `Scalar` class, with a comparison-free minmod; size lemmas |
| E0b-L | With real arithmetic the kernel `min` and `minmod` are the mathematical ones |
| E0b-S | One-step and `k`-step refinement of the MUSCL kernel: Euler, SSPRK2, SSPRK3 |
| E0b-T | Transfer of the B3 results to arrays: bounds, sum, total variation after `k` steps |
| E0b-X | `burgers1d --muscl` |

Independent implementation review remains separate from implementation authorization.
