# Burgers B1: total-variation and maximum-principle stability of the first-order scheme

Status: **approved and frozen for implementation on 2026-11-25** (`specifications/Burgers-B1-approval.md`).

Base: Burgers B0 (`specifications/Burgers-B0.md`, merged to `main` at e0e70cc). Toolchain: Lean v4.36.0. Exact real
arithmetic. No new dependency. Proposal: `specifications/Burgers-B1-proposal.md`.

## Purpose

B0 proves algebra only: consistency, conservation, constant states. B1 adds the first stability results for

```text
Burgers physical flux + Rusanov flux + periodic first-order finite volume + Forward Euler
```

under an explicit CFL hypothesis. Generic theorems consume certificates; the assembled Burgers theorems are
compositions.

## Frozen decisions

1. **CFL hypothesis per interface.** The hypothesis is an inequality at every interface `i`, with the Rusanov wave
   speed `a_i = max(|u_i|, |u_{i+1}|)` of the old state. A global bound `dt · sup|u| ≤ dx` implies it.
2. **CFL 1/2 for the bounds.** The total-variation result uses `dt · a_i ≤ dx`. The bounds result uses
   `2 · dt · a_i ≤ dx`. No sharper constant is claimed.
3. **The monotone-flux certificate is part of B1.** It is a separate certificate, as the consistency certificate of B0.
   Its name is `MonotoneFlux`, not `Monotone`, so that it does not shadow Mathlib's `Monotone`.
4. **B0 sources do not change.** B1 adds new modules only.
5. **`dx > 0` and `dt ≥ 0` are explicit hypotheses** of every stability theorem.

## Mathematical route

Write `λ = dt/dx`, `a_i = max(|u_i|, |u_{i+1}|)`, `ū_i = (u_i + u_{i+1})/2`.

**Incremental form (Harten).** A one-step update is in incremental form with interface coefficients `C_i`, `D_i` when

```text
v_i = u_i + C_i (u_{i+1} - u_i) - D_{i-1} (u_i - u_{i-1}).
```

**Generic lemma H (total variation).** If `0 ≤ C_i`, `0 ≤ D_i` and `C_i + D_i ≤ 1` for every `i`, then
`TV(v) ≤ TV(u)` with `TV(u) = Σ_i |u_{i+1} - u_i|` on the periodic grid.

**Generic lemma X (bounds).** If `0 ≤ C_i`, `0 ≤ D_{i-1}` and `C_i + D_{i-1} ≤ 1`, then `v_i` is a convex combination
of `u_{i-1}`, `u_i`, `u_{i+1}`. So `m ≤ u ≤ M` gives `m ≤ v_i ≤ M`.

**Burgers Rusanov coefficients.** The B0 step is exactly in incremental form with

```text
C_i = (λ/2) (a_i - ū_i),      D_i = (λ/2) (a_i + ū_i).
```

Because `|ū_i| ≤ a_i`: with `dx > 0`, `dt ≥ 0` both coefficients are nonnegative, and `C_i + D_i = λ a_i`.

## Frozen Lean statements

`g : CFDLean.Periodic.Grid I`, `u : I → ℝ`. Names are final.

```lean
-- B1-V  (namespace CFDLean.Scalar.FiniteVolume)
def totalVariation [Fintype I] (g : Grid I) (u : I → ℝ) : ℝ :=
  ∑ i, |u (g.next i) - u i|

def incrementalUpdate (g : Grid I) (C D : I → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  u i + C i * (u (g.next i) - u i) - D (g.prev i) * (u i - u (g.prev i))

-- B1-H
theorem incrementalUpdate_totalVariation_le [Fintype I] (g : Grid I) (C D u : I → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hD : ∀ i, 0 ≤ D i) (hCD : ∀ i, C i + D i ≤ 1) :
    totalVariation g (incrementalUpdate g C D u) ≤ totalVariation g u

-- B1-X
theorem incrementalUpdate_bounds (g : Grid I) (C D u : I → ℝ) (m M : ℝ) (i : I)
    (hC : 0 ≤ C i) (hD : 0 ≤ D (g.prev i)) (hCD : C i + D (g.prev i) ≤ 1)
    (hm : ∀ j, m ≤ u j) (hM : ∀ j, u j ≤ M) :
    m ≤ incrementalUpdate g C D u i ∧ incrementalUpdate g C D u i ≤ M

-- B1-M  (namespace CFDLean.Scalar, then CFDLean.Burgers.Rusanov)
def MonotoneFlux (numFlux : NumericalFlux) : Prop :=
  (∀ a a' b, a ≤ a' → numFlux.eval a b ≤ numFlux.eval a' b) ∧
  (∀ a b b', b ≤ b' → numFlux.eval a b' ≤ numFlux.eval a b)

theorem monotone : MonotoneFlux numericalFlux

-- B1-I  (namespace CFDLean.Burgers.Rusanov)
def incrementC (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) : ℝ :=
  dt / dx * ((waveSpeed (u i) (u (g.next i)) - (u i + u (g.next i)) / 2) / 2)

def incrementD (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) : ℝ :=
  dt / dx * ((waveSpeed (u i) (u (g.next i)) + (u i + u (g.next i)) / 2) / 2)

theorem abs_mean_le_waveSpeed (a b : ℝ) : |(a + b) / 2| ≤ waveSpeed a b

theorem step_eq_incrementalUpdate (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) :
    Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u i =
      FiniteVolume.incrementalUpdate g (incrementC g dx dt u) (incrementD g dx dt u) u i

-- B1-S, any periodic grid  (namespace CFDLean.Burgers.Rusanov)
theorem step_totalVariation_le [Fintype I] (g : Grid I) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : I → ℝ)
    (hcfl : ∀ i, dt * waveSpeed (u i) (u (g.next i)) ≤ dx) :
    FiniteVolume.totalVariation g (Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u) ≤
      FiniteVolume.totalVariation g u

theorem step_bounds (g : Grid I) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : I → ℝ) (m M : ℝ)
    (hcfl : ∀ i, 2 * (dt * waveSpeed (u i) (u (g.next i))) ≤ dx)
    (hm : ∀ j, m ≤ u j) (hM : ∀ j, u j ≤ M) (i : I) :
    m ≤ Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u i ∧
      Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u i ≤ M

-- B1-S, assembled scheme on ZMod N  (namespace CFDLean.Burgers.Schemes.RusanovForwardEuler)
theorem step_totalVariation_le (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : ZMod N → ℝ)
    (hcfl : ∀ i, dt * Rusanov.waveSpeed (u i) (u (grid.next i)) ≤ dx) :
    totalVariation grid (step dx dt u) ≤ totalVariation grid u

theorem step_bounds (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : ZMod N → ℝ) (m M : ℝ)
    (hcfl : ∀ i, 2 * (dt * Rusanov.waveSpeed (u i) (u (grid.next i))) ≤ dx)
    (hm : ∀ j, m ≤ u j) (hM : ∀ j, u j ≤ M) (i : ZMod N) :
    m ≤ step dx dt u i ∧ step dx dt u i ≤ M
```

Supporting lemmas (coefficient signs, coefficient sum) may be added with any name.

## Frozen module layout

```text
CFDLean/Discrete/Periodic/TotalVariation.lean     B1-V, B1-H, B1-X
CFDLean/Schemes/Scalar/Monotone.lean              B1-M certificate `MonotoneFlux`
CFDLean/Schemes/Burgers/RusanovStability.lean     B1-M proof, B1-I, B1-S
CFDLean/Schemes/Burgers/StabilityControls.lean    exact small controls
CFDLean/Verification/BurgersB1Challenge.lean      trusted statements, Mathlib only
CFDLean/Verification/BurgersB1Verify.lean         bridge
Challenges/BurgersB1.lean                         `lake comparator` challenge
```

## Trusted statements

`CFDLean/Verification/BurgersB1Challenge.lean` imports only Mathlib and restates its own definitions (Burgers flux,
Rusanov flux, periodic flux-difference step on an equivalence `next : I ≃ I`, total variation, incremental update). It
states:

| Trusted statement | Content | Result ID |
| --- | --- | --- |
| `HartenTotalVariation I` | lemma H for every `next`, `C`, `D`, `u` | B1-H |
| `IncrementalBounds I` | lemma X for every `next`, `C`, `D`, `u`, `m`, `M`, `i` | B1-X |
| `RusanovMonotone` | the Rusanov flux is nondecreasing in the left state and nonincreasing in the right state | B1-M |
| `RusanovTotalVariation I` | TVD of the Rusanov Forward-Euler step under `0 < dx`, `0 ≤ dt`, `dt · a_i ≤ dx` | B1-S |
| `RusanovBounds I` | bounds of the step under `0 < dx`, `0 ≤ dt`, `2 · dt · a_i ≤ dx` | B1-S |

The bridge proves each statement from the implementation theorem of its result ID.

## Explicitly excluded from B1

B1 does **not** claim or implement:

- a CFL estimator or a time-step selection rule (the CFL inequality is a hypothesis on the old state);
- multi-step statements such as `TV(u^n) ≤ TV(u^0)`;
- that the CFL hypothesis holds again after the step;
- entropy inequalities, convergence, order of accuracy;
- other fluxes (Godunov, Engquist--Osher, HLL), reconstruction and limiters, other time integrators;
- floating-point, arrays, parallel execution.

## Frozen B1 result IDs

| ID | Required result |
| --- | --- |
| B1-V | Periodic total variation and the incremental-form update (definitions) |
| B1-H | Generic Harten lemma: incremental form with `C, D ≥ 0`, `C + D ≤ 1` does not increase total variation |
| B1-X | Generic local bounds of an incremental-form update |
| B1-M | Monotone two-point-flux certificate and its proof for the Burgers Rusanov flux |
| B1-I | Burgers Rusanov Forward-Euler step in incremental form; `|ū| ≤ a` |
| B1-S | TVD (CFL 1) and bounds (CFL 1/2) of the Rusanov Forward-Euler step, on any periodic grid and on `ZMod N` |

Independent implementation review remains separate from implementation authorization.
