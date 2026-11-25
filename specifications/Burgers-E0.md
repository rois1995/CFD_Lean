# Burgers E0: executable array kernel and its refinement to the mathematical scheme

Status: **frozen for implementation on 2026-11-26 by the agent under the standing authorization**
(`specifications/Burgers-E0-approval.md`). No human approved the statements of this contract.

Base: Burgers B0--B4. Toolchain: Lean v4.36.0. No new dependency.

## Purpose

B0--B4 define the schemes as functions on index types and prove their properties in exact real arithmetic. They cannot
run. E0 adds the first executable implementation and the first refinement proof:

```text
mathematical scheme (functions Fin n → ℝ, B0--B2 theorems)
          ↑ refinement, proved in Lean
array kernel, generic in its arithmetic (Array α)
          ↓ instance α = Float
native executable  lake exe burgers1d
```

The kernel is one piece of code. With the real-number instance it is proved to compute the mathematical scheme, so the
B2 theorems hold for the arrays. With the `Float` instance the same code is compiled and run. E0 proves nothing about
floating-point rounding; that is E1.

## Frozen decisions

1. **One generic kernel.** The kernel is written once over a class `CFDLean.Exec.Scalar α` that lists the arithmetic
   it uses (`+ - * /`, negation, zero, `abs`, `max`, and the constants 2, 1/2, 1/3, 2/3, 1/4, 3/4). Instances: `Float`
   and `ℝ`.
2. **Execution is separate from the mathematics.** The kernel module imports nothing (no Mathlib) and mentions no real
   number. The mathematical modules do not import it. Only the refinement module imports both.
3. **Scheme.** First-order periodic finite volume with the Rusanov flux; Forward Euler, SSPRK2, SSPRK3 in the
   Shu-Osher form of B2. MUSCL is not in the E0 kernel.
4. **State and grid.** The array of size `n` stores the cell values of `u : Fin n → ℝ`. The periodic grid is
   `Fin n` with successor `i + 1`. An array `a` represents `u` when `a.size = n` and `a[i] = u i` for every `i`.
5. **What is proved.** One-step refinement for the Euler, SSPRK2 and SSPRK3 kernels; refinement of `k` steps; the
   kernel diagnostics (sum, total variation) are the mathematical ones; transfer of the B2 results to arrays (bounds,
   sum, total variation after `k` steps). All for the `ℝ` instance.
6. **What is trusted and not proved.** The Lean compiler and runtime, the `Float` operations, the executable driver
   `Main.lean` (argument parsing, initial condition, printing).

## Frozen Lean statements

Kernel (`CFDLean/Exec/Kernel.lean`, namespace `CFDLean.Exec`, `α` with `[Scalar α]`):

```lean
class Scalar (α : Type) extends Add α, Sub α, Mul α, Div α, Neg α, Zero α where
  abs : α → α
  max : α → α → α
  two : α
  half : α
  third : α
  twoThirds : α
  quarter : α
  threeQuarters : α

def Scalar.burgersFlux (u : α) : α := u * u / two
def Scalar.rusanov (uL uR : α) : α :=
  (burgersFlux uL + burgersFlux uR) / two - Scalar.max (abs uL) (abs uR) / two * (uR - uL)

def eulerStepArray (dx dt : α) (u : Array α) : Array α :=
  Array.ofFn fun i : Fin u.size =>
    u[i] + dt * (-(rusanov u[i] (u[(i.val + 1) % u.size]'(succ_mod_lt i)) -
      rusanov (u[(i.val + u.size - 1) % u.size]'(pred_mod_lt i)) u[i]) / dx)
def axpby (a : α) (x : Array α) (b : α) (y : Array α) : Array α :=
  Array.zipWith (fun p q => a * p + b * q) x y
def ssprk2StepArray (dx dt : α) (u : Array α) : Array α :=
  axpby half u half (eulerStepArray dx dt (eulerStepArray dx dt u))
def ssprk3StepArray (dx dt : α) (u : Array α) : Array α :=
  axpby third u twoThirds
    (eulerStepArray dx dt (axpby threeQuarters u quarter (eulerStepArray dx dt (eulerStepArray dx dt u))))
def run {β : Type} (step : β → β) : Nat → β → β      -- run step (k+1) u = run step k (step u)
def sumArray (u : Array α) : α := u.sum
def totalVariationArray (u : Array α) : α             -- Σ |u[(i+1) % n] - u[i]|
instance : Scalar Float
```

Specification arithmetic (`CFDLean/Exec/RealScalar.lean`): `instance instScalarReal : Scalar ℝ` with the real
operations, `abs x := |x|`, `max := max`, `two := 2`, `half := 1 / 2`, `third := 1 / 3`, `twoThirds := 2 / 3`,
`quarter := 1 / 4`, `threeQuarters := 3 / 4`.

Refinement (`CFDLean/Exec/Refinement.lean`, namespace `CFDLean.Exec`):

```lean
-- E0-R
def finGrid (n : ℕ) [NeZero n] : Periodic.Grid (Fin n) := ⟨Equiv.addRight 1⟩
def Represents {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) : Prop :=
  ∃ h : a.size = n, ∀ i : Fin n, a[i.val]'(h ▸ i.isLt) = u i
theorem rusanov_eq (uL uR : ℝ) : Scalar.rusanov uL uR = Burgers.Rusanov.eval uL uR
theorem represents_iff_eq_ofFn {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) : Represents a u ↔ a = Array.ofFn u

-- E0-S
theorem eulerStepArray_refines {n : ℕ} [NeZero n] (dx dt : ℝ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) : Represents (eulerStepArray dx dt a) (Burgers.Rusanov.eulerStep (finGrid n) dx dt u)
theorem axpby_refines {n : ℕ} (a b : ℝ) {x y : Array ℝ} {u v : Fin n → ℝ} (hx : Represents x u)
    (hy : Represents y v) : Represents (axpby a x b y) (a • u + b • v)
theorem ssprk2StepArray_refines   -- against Burgers.Rusanov.ssprk2Step (finGrid n) dx dt
theorem ssprk3StepArray_refines   -- against Burgers.Rusanov.ssprk3Step (finGrid n) dx dt

-- E0-N
theorem run_refines {n : ℕ} {step : Array ℝ → Array ℝ} {T : (Fin n → ℝ) → Fin n → ℝ}
    (hT : ∀ a u, Represents a u → Represents (step a) (T u)) (k : ℕ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) : Represents (run step k a) (T^[k] u)

-- E0-D
theorem sumArray_eq {n : ℕ} {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u) : sumArray a = ∑ i, u i
theorem totalVariationArray_eq {n : ℕ} [NeZero n] {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u) :
    totalVariationArray a = Scalar.FiniteVolume.totalVariation (finGrid n) u

-- E0-T   (for step in {eulerStepArray, ssprk3StepArray}; EntriesBetween m M a := ∀ i (hi : i < a.size), m ≤ a[i] ∧ a[i] ≤ M)
theorem run_step_bounds (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    EntriesBetween m M (run (step dx dt) k a)
theorem run_step_sum (dx dt : ℝ) (hdx : dx ≠ 0) (a : Array ℝ) (k : ℕ) :
    sumArray (run (step dx dt) k a) = sumArray a
theorem run_step_totalVariation_le (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    totalVariationArray (run (step dx dt) k a) ≤ totalVariationArray a
```

Supporting lemmas (sizes, index lemmas of `finGrid`) may be added with any name.

## Executable (E0-X)

`lake exe burgers1d [N] [steps] [cfl] [--dump]`, defaults `N = 200`, `steps = 200`, `cfl = 0.4`. Domain `[0, 1)`,
`dx = 1/N`, initial cell values `0.5 + sin(2π (i + 1/2) dx)`, `dt = cfl · dx / max|u⁰|`, `steps` SSPRK3 steps of the
kernel with the `Float` instance. It prints `N`, `steps`, `dt`, and for the initial and final state: `sum · dx`,
minimum, maximum, total variation. `--dump` prints the final cell values. The driver is `Main.lean`; it imports only
the kernel. E0-X is a build-and-run requirement, checked in CI; it is not a theorem.

## Frozen module layout

```text
CFDLean/Exec/Kernel.lean                          E0-K: Scalar class, kernel, Float instance (no imports)
CFDLean/Exec/RealScalar.lean                      the ℝ instance of the kernel arithmetic
CFDLean/Exec/Refinement.lean                      E0-R, E0-S, E0-N, E0-D, E0-T
Main.lean                                         E0-X driver of `burgers1d`
CFDLean/Verification/BurgersE0Challenge.lean      trusted statements
CFDLean/Verification/BurgersE0Verify.lean         bridge
Challenges/BurgersE0.lean                         `lake comparator` challenge
```

## Trusted statements

The trusted statement file imports Mathlib and the two modules that define the object under verification: the kernel
and the `ℝ` instance. Both are hash-pinned as trusted inputs in `scripts/verify.py`. It imports no mathematical
implementation module and no proof. It restates the mathematical scheme on `Fin n` with cyclic indices `i + 1`,
`i - 1`, the SSPRK3 step and the representation relation, and states:

| Trusted statement | Content | Result ID |
| --- | --- | --- |
| `KernelFluxIsRusanov` | the kernel flux with real arithmetic is the Rusanov flux | E0-R |
| `EulerStepRefines` | if `a` represents `u`, the kernel Euler step of `a` represents the Euler step of `u` | E0-S |
| `SSPRK3StepRefines` | the same for the SSPRK3 kernel step | E0-S |
| `SSPRK3RunRefines` | `k` kernel SSPRK3 steps represent `k` mathematical SSPRK3 steps | E0-N |
| `SSPRK3RunBounds` | with `dx > 0`, `dt ≥ 0`, entries in `[m, M]`, `2 · dt · max(|m|, |M|) ≤ dx`: after `k` kernel SSPRK3 steps every entry is in `[m, M]` | E0-T |
| `SSPRK3RunSum` | with `dx ≠ 0`: `k` kernel SSPRK3 steps keep the sum of the entries | E0-T |
| `SSPRK3RunTotalVariation` | under the hypotheses of the bounds statement the periodic total variation of the entries does not increase | E0-T |

## Explicitly excluded from E0

E0 does **not** claim or implement:

- anything about `Float`: no rounding-error bound, no statement that the `Float` run keeps bounds, sum or total
  variation (E1);
- correctness of the driver `Main.lean`, of the Lean compiler, of the C toolchain;
- a MUSCL kernel, other fluxes, non-periodic boundaries;
- performance, in-place updates, parallel execution, GPU, MPI (E2--E4);
- domain decomposition, halo cells.

## Frozen E0 result IDs

| ID | Required result |
| --- | --- |
| E0-K | Generic array kernel over the `Scalar` class; `Float` and `ℝ` instances; size lemmas |
| E0-R | Representation of a cell function by an array; periodic grid on `Fin n`; the kernel flux is the Rusanov flux |
| E0-S | One-step refinement: Euler, linear combination, SSPRK2, SSPRK3 |
| E0-N | Refinement of `k` steps |
| E0-D | The kernel diagnostics (sum, total variation) are the mathematical ones |
| E0-T | Transfer of the B2 results to arrays: bounds, sum, total variation after `k` steps |
| E0-X | Native executable `burgers1d` that runs the kernel with `Float` |

Independent implementation review remains separate from implementation authorization.
