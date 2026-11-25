# Burgers B1 proposal: total-variation and maximum-principle stability of the first-order scheme

Status: **proposal; superseded by the frozen contract `specifications/Burgers-B1.md` (approved 2026-11-25)**.

Base: Burgers B0 (`specifications/Burgers-B0.md`, implementation on branch `burgers-b0-implementation`, PR 2).
Toolchain: Lean v4.36.0. Exact real arithmetic. No new dependency.

## Purpose

B0 proves algebra only: consistency, conservation, constant states. B1 adds the first stability results for

```text
Burgers physical flux + Rusanov flux + periodic first-order finite volume + Forward Euler
```

under an explicit CFL hypothesis. B1 keeps the B0 rule: generic theorems consume certificates; the assembled Burgers
theorems are compositions.

## Mathematical route

Write `λ = dt/dx`, `Δ_i = u_{i+1} - u_i`, `a_i = max(|u_i|, |u_{i+1}|)`, `ū_i = (u_i + u_{i+1})/2`.

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

- TVD follows from lemma H under the CFL hypothesis `dt · a_i ≤ dx` for every interface `i`.
- The bounds follow from lemma X under the stronger hypothesis `2 · dt · a_i ≤ dx` for every interface `i`
  (because `C_i ≤ λ a_i` and `D_{i-1} ≤ λ a_{i-1}`). CFL number 1 is not sufficient for lemma X: the state
  `(M, M-ε, -M)` gives `C_i + D_{i-1} ≈ 1.5 λ M`.

This route needs no derivative and no flux monotonicity. Monotonicity of the Rusanov flux is a separate certificate
(B1-M) for later use (monotone-scheme and entropy results).

## Proposed Lean statements

Names follow the B0 namespaces after the rename (`specifications/Burgers-B0-layout.md` on the B0 branch): generic
declarations in `CFDLean.Scalar` and `CFDLean.Periodic`, Burgers ones in `CFDLean.Burgers`. `g : Periodic.Grid I`,
`u : I → ℝ`.

```lean
-- B1-V  (CFDLean.Scalar.FiniteVolume)
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

-- B1-M  (CFDLean.Scalar, CFDLean.Burgers.Rusanov)
def Monotone (numFlux : NumericalFlux) : Prop :=
  (∀ a a' b, a ≤ a' → numFlux.eval a b ≤ numFlux.eval a' b) ∧
  (∀ a b b', b ≤ b' → numFlux.eval a b' ≤ numFlux.eval a b)

theorem Rusanov.monotone : Monotone Rusanov.numericalFlux

-- B1-I  (CFDLean.Burgers.Rusanov)
def incrementC (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) : ℝ :=
  dt / dx * ((waveSpeed (u i) (u (g.next i)) - (u i + u (g.next i)) / 2) / 2)

def incrementD (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) : ℝ :=
  dt / dx * ((waveSpeed (u i) (u (g.next i)) + (u i + u (g.next i)) / 2) / 2)

theorem abs_mean_le_waveSpeed (a b : ℝ) : |(a + b) / 2| ≤ waveSpeed a b

theorem step_eq_incrementalUpdate (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) :
    Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u i =
      FiniteVolume.incrementalUpdate g (incrementC g dx dt u) (incrementD g dx dt u) u i

-- B1-S  (CFDLean.Burgers.Schemes.RusanovForwardEuler, cells ZMod N)
theorem step_totalVariation_le (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : ZMod N → ℝ)
    (hcfl : ∀ i, dt * Rusanov.waveSpeed (u i) (u (grid.next i)) ≤ dx) :
    totalVariation grid (step dx dt u) ≤ totalVariation grid u

theorem step_bounds (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : ZMod N → ℝ) (m M : ℝ)
    (hcfl : ∀ i, 2 * (dt * Rusanov.waveSpeed (u i) (u (grid.next i))) ≤ dx)
    (hm : ∀ j, m ≤ u j) (hM : ∀ j, u j ≤ M) (i : ZMod N) :
    m ≤ step dx dt u i ∧ step dx dt u i ≤ M
```

Feasibility: all statements above were proved in a scratch file against the B0 branch before this proposal
(Lean v4.36.0, standard axioms only). The scratch file is not part of the repository.

## Proposed result IDs

| ID | Required result |
| --- | --- |
| B1-V | Periodic total variation and the incremental-form update (definitions) |
| B1-H | Generic Harten lemma: incremental form with `C, D ≥ 0`, `C + D ≤ 1` does not increase total variation |
| B1-X | Generic local bounds of an incremental-form update |
| B1-M | Monotone two-point-flux certificate and its proof for the Burgers Rusanov flux |
| B1-I | Burgers Rusanov Forward-Euler step in incremental form; coefficient sign from `|ū| ≤ a` |
| B1-S | Assembled TVD (CFL 1) and bounds (CFL 1/2) theorems for the `ZMod N` scheme, by composition |

## Proposed module layout (layered folders)

```text
CFDLean/Discrete/Periodic/TotalVariation.lean     B1-V, B1-H, B1-X
CFDLean/Schemes/Scalar/NumericalFlux.lean         B1-M certificate `Monotone` (added definition)
CFDLean/Schemes/Burgers/RusanovStability.lean     B1-M proof, B1-I
CFDLean/Schemes/Burgers/RusanovForwardEuler.lean  B1-S (added theorems)
CFDLean/Verification/BurgersB1Challenge.lean      trusted statements, Mathlib only
CFDLean/Verification/BurgersB1Verify.lean         bridge
Challenges/BurgersB1.lean                         `lake comparator` challenge
```

## Trusted statements

The B1 challenge file restates, with Mathlib only: the total variation, the Rusanov step on a periodic equivalence,
the TVD statement and the bounds statement with their CFL hypotheses, and flux monotonicity. Unlike B0, it states the
assembled scheme results (B1-S), because these are the claims a user reads.

## Explicitly excluded from B1

- a CFL estimator or a time-step selection rule (the CFL inequality is a hypothesis on the old state);
- multi-step statements (`TV(u^n) ≤ TV(u^0)`): they need the bounds to propagate the CFL hypothesis (B1-X gives the
  ingredient; the induction is B2 material together with SSP time stepping);
- entropy inequalities, convergence, order of accuracy;
- other fluxes (Godunov, Engquist--Osher, HLL), reconstruction and limiters;
- floating-point, arrays, parallel execution.

## Review questions

1. Is the per-interface CFL hypothesis (`dt · a_i ≤ dx` for every `i`) the form you want, or a global bound
   `dt · sup|u| ≤ dx`? The per-interface form is the weaker hypothesis; the global form implies it.
2. Is CFL 1/2 acceptable for the bounds theorem? A sharper constant needs a longer case proof.
3. Should `Monotone` (B1-M) be part of B1, or wait for the milestone that first consumes it?
