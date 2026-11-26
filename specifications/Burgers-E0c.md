# Burgers E0c: limiter choice in the executable MUSCL kernel

Status: **frozen for implementation on 2026-11-26 by the agent** (`specifications/Burgers-E0c-approval.md`). The user
asked for the unlimited-by-default formulation and the limiters; no human approved the statements of this contract.

Base: Burgers B0--B4, B3b, E0, E0b. Toolchain: Lean v4.36.0. No new dependency.

## Purpose

B3b made the MUSCL reconstruction unlimited by default with a limiter on top, in the mathematics. E0b has an array
kernel that is fixed to minmod. E0c adds an array kernel with a limiter choice, proves that with real arithmetic it
computes the B3b scheme for every limiter, transfers the B3b results to the arrays, and gives the program the same
choice: `--muscl` is unlimited, `--limiter NAME` adds a limiter.

## Frozen decisions

1. **New modules; nothing existing changes.** The class `Scalar`, the E0 kernel and the E0b kernel keep their pinned
   hashes. The driver `Main.lean` changes (it is not verified).
2. **Limiters of the kernel:** `none` (unlimited central slope), `minmod`, `mc`, `superbee`, `vanLeer`, `vanAlbada`.
3. **Slope forms in the kernel.** The kernel computes the limited slope directly (no factor, no extra division):
   minmod, MC and superbee with `max` only; van Leer and van Albada with one branch on the sign of `ab`, so that a flat
   state gives the slope 0 and not `0/0` in `Float`. With real arithmetic each kernel slope is the B3b slope function
   `limitedSlope ψ` of that limiter (and `centralSlope` for `none`).
4. **Sign test.** A new class `ScalarSign` with one operation `isPos` (true exactly for strictly positive arguments),
   with a `Float` instance in the kernel and a real instance in its own small module.
5. **Program default.** `burgers1d --muscl` runs the unlimited scheme. `--limiter NAME` runs MUSCL with that limiter.
   Without both, the first-order kernel of E0 runs. This changes the meaning of `--muscl` (E0b: minmod).
6. **What is proved for `none`:** refinement and conservation of the sum. No bounds and no total-variation result:
   B3b has an exact overshoot example.
7. **What is trusted and not proved** is the same as in E0: `Float`, the driver, the compiler.

## Frozen Lean statements

Kernel (`CFDLean/Exec/LimiterKernel.lean`, namespace `CFDLean.Exec`; imports only `CFDLean.Exec.MusclKernel`):

```lean
class ScalarSign (α : Type) [Scalar α] where
  isPos : α → Bool
instance : ScalarSign Float            -- isPos x := decide (0 < x)

inductive Limiter where
  | none | minmod | mc | superbee | vanLeer | vanAlbada
def Limiter.isLimited : Limiter → Bool

def Scalar.maxmodSame (x y : α) : α := Scalar.max 0 (Scalar.max x y) + Scalar.min 0 (Scalar.min x y)
def limiterSlope (L : Limiter) (a b : α) : α :=
  match L with
  | .none => (a + b) / two
  | .minmod => Scalar.minmod a b
  | .mc => Scalar.minmod (Scalar.minmod (two * a) (two * b)) ((a + b) / two)
  | .superbee => Scalar.maxmodSame (Scalar.minmod (two * a) b) (Scalar.minmod a (two * b))
  | .vanLeer => if ScalarSign.isPos (a * b) then two * (a * b) / (a + b) else 0
  | .vanAlbada => if ScalarSign.isPos (a * b) then a * b * (a + b) / (a * a + b * b) else 0
def limSlopeAt (L : Limiter) (u : Array α) (i : Fin u.size) : α :=
  limiterSlope L (u[i] - u[prevIdx i]) (u[nextIdx i] - u[i])
def limFacePlus (L : Limiter) (u : Array α) (i : Fin u.size) : α := u[i] + limSlopeAt L u i / two
def limFaceMinus (L : Limiter) (u : Array α) (i : Fin u.size) : α := u[i] - limSlopeAt L u i / two
def limiterEulerStepArray (L : Limiter) (dx dt : α) (u : Array α) : Array α :=
  Array.ofFn fun i : Fin u.size =>
    u[i] + dt * (-(rusanov (limFacePlus L u i) (limFaceMinus L u (nextIdx i)) -
      rusanov (limFacePlus L u (prevIdx i)) (limFaceMinus L u i)) / dx)
def limiterSsprk2StepArray (L : Limiter) (dx dt : α) (u : Array α) : Array α   -- Shu-Osher with `axpby`
def limiterSsprk3StepArray (L : Limiter) (dx dt : α) (u : Array α) : Array α
```

Real sign test (`CFDLean/Exec/RealScalarSign.lean`): `instance instScalarSignReal : ScalarSign ℝ` with
`isPos x := decide (0 < x)`.

Refinement (`CFDLean/Exec/LimiterRefinement.lean`, namespace `CFDLean.Exec`, real arithmetic):

```lean
-- E0c-L
def Limiter.slopeFn : Limiter → ℝ → ℝ → ℝ      -- none: centralSlope; else limitedSlope of the B3b factor
def Limiter.theta : Limiter → ℝ                -- none 0, minmod 1, mc 2, superbee 2, vanLeer 2, vanAlbada 5/4
theorem isPos_eq (x : ℝ) : ScalarSign.isPos x = decide (0 < x)
theorem limiterSlope_eq (L : Limiter) (a b : ℝ) : limiterSlope L a b = L.slopeFn a b
theorem Limiter.slopeBounded (L : Limiter) (hL : L ≠ .none) :
    CFDLean.Scalar.FiniteVolume.SlopeBounded L.theta L.slopeFn
theorem Limiter.theta_le_two (L : Limiter) : L.theta ≤ 2

-- E0c-S
theorem limiterEulerStepArray_refines {n : ℕ} [NeZero n] (L : Limiter) (dx dt : ℝ) {a : Array ℝ}
    {u : Fin n → ℝ} (h : Represents a u) :
    Represents (limiterEulerStepArray L dx dt a) (Burgers.Rusanov.musclEulerStep (finGrid n) dx dt L.slopeFn u)
theorem limiterSsprk2StepArray_refines   -- against Burgers.Rusanov.musclSsprk2Step (finGrid n) dx dt L.slopeFn
theorem limiterSsprk3StepArray_refines   -- against Burgers.Rusanov.musclSsprk3Step (finGrid n) dx dt L.slopeFn
theorem limiterEulerStepArray_minmod (dx dt : α) (u : Array α) :
    limiterEulerStepArray .minmod dx dt u = musclEulerStepArray dx dt u      -- every arithmetic; also SSPRK2, SSPRK3

-- E0c-T   (for step in {limiterEulerStepArray, limiterSsprk3StepArray})
theorem run_step_sum (L : Limiter) (dx dt : ℝ) (hdx : dx ≠ 0) (a : Array ℝ) (k : ℕ) :
    sumArray (run (step L dx dt) k a) = sumArray a
theorem run_step_bounds (L : Limiter) (hL : L ≠ .none) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : (4 + 2 * L.theta) * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    EntriesBetween m M (run (step L dx dt) k a)
theorem run_step_totalVariation_le   -- same hypotheses: totalVariationArray (run ...) ≤ totalVariationArray a
```

The order of the arguments of the transfer theorems may differ. Supporting lemmas may be added with any name.

## Executable (E0c-X)

`burgers1d [N] [steps] [cfl] [--muscl] [--limiter NAME] [--dump]`, `NAME` in `none`, `minmod`, `mc`, `superbee`,
`vanleer`, `vanalbada`. The first output line names the scheme and the limiter. The note line gives the proved range
for real arithmetic: `cfl ≤ 0.5` (first order), `1/6` (minmod), `2/13` (van Albada), `1/8` (MC, superbee, van Leer),
and says whether the run is inside it; for the unlimited scheme it says that no bounds are proved and that it can
overshoot. An unknown limiter name is a bad argument (exit 1). Built and run in CI. Not a theorem.

## Frozen module layout

```text
CFDLean/Exec/LimiterKernel.lean                    E0c-K
CFDLean/Exec/RealScalarSign.lean                   the ℝ instance of the sign test
CFDLean/Exec/LimiterRefinement.lean                E0c-L, E0c-S, E0c-T
Main.lean                                          E0c-X
CFDLean/Verification/BurgersE0cChallenge.lean      trusted statements
CFDLean/Verification/BurgersE0cVerify.lean         bridge
Challenges/BurgersE0c.lean                         `lake comparator` challenge
```

## Trusted statements

The trusted statement file imports Mathlib and five hash-pinned trusted inputs: the E0 kernel, the real instance, the
MUSCL kernel (for the indices and the comparison-free minmod), the limiter kernel and the real sign test. It restates
the six slope functions in classical form, the MUSCL step with a slope function on `Fin n`, the SSPRK3 step and the
representation relation, and states:

| Trusted statement | Content | Result ID |
| --- | --- | --- |
| `RealSignIsStandard` | with real arithmetic `isPos x` is true exactly when `0 < x` | E0c-L |
| `KernelSlopeIsLimiter` | for every limiter the kernel slope is the classical slope function | E0c-L |
| `LimiterEulerStepRefines`, `LimiterSSPRK3StepRefines`, `LimiterSSPRK3RunRefines` | for every limiter, also `none`: the kernel computes the mathematical MUSCL scheme with that slope function, for one step and for `k` steps | E0c-S |
| `LimiterSSPRK3RunSum` | for every limiter, `dx ≠ 0`: the sum diagnostic is unchanged after `k` steps | E0c-T |
| `LimiterSSPRK3RunBounds`, `LimiterSSPRK3RunTotalVariation` | for every limiter except `none`, with `dx > 0`, `dt ≥ 0`, entries in `[m, M]`, `(4 + 2θ) · dt · max(\|m\|, \|M\|) ≤ dx`: bounds and total-variation diagnostic after `k` steps | E0c-T |

## Explicitly excluded from E0c

- anything about `Float`; correctness of the driver and of the compiler;
- bounds or total variation for the unlimited scheme;
- other limiters, other fluxes, non-periodic boundaries, non-uniform grids;
- performance; snapshot output during a run.

## Frozen E0c result IDs

| ID | Required result |
| --- | --- |
| E0c-K | Sign-test class, limiter type, kernel slope and MUSCL array kernel with a limiter choice; size lemmas |
| E0c-L | With real arithmetic the kernel slope of each limiter is its B3b slope function; bound constants |
| E0c-S | One-step refinement for every limiter (Euler, SSPRK2, SSPRK3); the `minmod` choice is the E0b kernel |
| E0c-T | Transfer to arrays: sum for every limiter; bounds and total variation for every limiter except `none` |
| E0c-X | `burgers1d --muscl` (unlimited) and `--limiter NAME` |

Independent implementation review remains separate from implementation authorization.
