# Burgers B3: second-order MUSCL reconstruction with a limiter in the minmod region

Status: **frozen for implementation on 2026-11-25 by the agent under the standing authorization**
(`specifications/Burgers-B3-approval.md`). No human approved the statements of this contract.

Base: Burgers B0, B1, B2 on `main` at 16a77e0. Toolchain: Lean v4.36.0. Exact real arithmetic. No new dependency.

## Purpose

B0--B2 are about the first-order scheme (piecewise-constant states at the interfaces). B3 adds a second-order
reconstruction: a limited slope in every cell, two reconstructed states at every interface, the same two-point flux.
B3 proves that the Forward-Euler step of this scheme is again in Harten's incremental form with bounded nonnegative
coefficients. Then the generic lemmas of B1 (total variation, bounds) and the SSP machinery of B2 apply without a new
stability proof.

## Mathematics

`Δ_i = u_{i+1} - u_i`. A limiter is a function `φ : ℝ → ℝ → ℝ`. Cell slope: `σ_i = φ(Δ_{i-1}, Δ_i)`.
Interface `i + 1/2` (indexed by its left cell `i`): left state `L_i = u_i + σ_i / 2`, right state
`R_i = u_{i+1} - σ_{i+1} / 2`. Right-hand side: `-(F(L_i, R_i) - F(L_{i-1}, R_{i-1})) / dx`.

**Limiter certificate (minmod region).** `σ = φ(a, b)` has the sign of `a` and of `b` and `|σ| ≤ |a|`, `|σ| ≤ |b|`,
written without division: `0 ≤ σ a`, `0 ≤ σ b`, `|σ| ≤ |a|`, `|σ| ≤ |b|`. The minmod limiter and the zero limiter
(first order) have it. Limiters that allow `|σ|` up to `2 min(|a|, |b|)` (MC, superbee) do not; they are not in B3.

**Flux certificates.** `MonotoneFlux` (B1) and a Lipschitz certificate on states between `m` and `M` with one constant
per argument, `KL` and `KR`.

**Key result.** For a limiter in the minmod region, a monotone flux with the Lipschitz certificate, `dx > 0`,
`dt ≥ 0` and `m ≤ u ≤ M`: there are interface coefficients with `0 ≤ C_i ≤ (dt/dx)(3/2) KR` and
`0 ≤ D_i ≤ (dt/dx)(3/2) KL` such that the MUSCL Forward-Euler step is the incremental update with `C`, `D`.
The factor `3/2` bounds `(R_i - R_{i-1}) / Δ_i` and `(L_i - L_{i-1}) / Δ_{i-1}`.

**Consequence.** Under `dt · (3/2)(KL + KR) ≤ dx` one step keeps the bounds and does not increase the total variation.
For Burgers with Rusanov, `KL = KR = 2 max(|m|, |M|)` (this constant is sharp for the Lipschitz certificate), so the
hypothesis is `6 · dt · max(|m|, |M|) ≤ dx`. No claim that this CFL constant is sharp for stability.

## Frozen decisions

1. Certificates stay separate: `MinmodBounded φ` for the limiter, `MonotoneFlux nf` and `LipschitzOnBounds nf m M KL KR`
   for the flux. The generic theorems take them as hypotheses.
2. The generic MUSCL theorems hold for every two-point flux and every limiter with the certificates, on every periodic
   grid. The Burgers theorems are instances with the Rusanov flux; they are stated for every limiter with
   `MinmodBounded` and for `minmod`.
3. Time stepping: Forward Euler, SSPRK2 and SSPRK3 through the B2 composition, one `dt` for all steps.
4. B0, B1, B2 sources do not change.

## Frozen Lean statements

```lean
-- B3-L  (namespace CFDLean.Scalar.FiniteVolume)
def MinmodBounded (φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b, 0 ≤ φ a b * a ∧ 0 ≤ φ a b * b ∧ |φ a b| ≤ |a| ∧ |φ a b| ≤ |b|
def minmod (a b : ℝ) : ℝ :=
  if 0 < a ∧ 0 < b then min a b else if a < 0 ∧ b < 0 then max a b else 0
theorem minmod_minmodBounded : MinmodBounded minmod
theorem zero_minmodBounded : MinmodBounded (fun _ _ => 0)

-- B3-R
def slope (g : Grid I) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  φ (u i - u (g.prev i)) (u (g.next i) - u i)
def leftState (g : Grid I) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ := u i + slope g φ u i / 2
def rightState (g : Grid I) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  u (g.next i) - slope g φ u (g.next i) / 2
def musclFlux (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  nf.eval (leftState g φ u i) (rightState g φ u i)
def musclRhs (g : Grid I) (dx : ℝ) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  -(musclFlux g nf φ u i - musclFlux g nf φ u (g.prev i)) / dx
theorem musclRhs_zero (g : Grid I) (dx : ℝ) (nf : NumericalFlux) (u : I → ℝ) (i : I) :
    musclRhs g dx nf (fun _ _ => 0) u i = rhs g dx nf u i
theorem musclRhs_sum_zero [Fintype I] (g : Grid I) (dx : ℝ) (_hdx : dx ≠ 0) (nf : NumericalFlux)
    (φ : ℝ → ℝ → ℝ) (u : I → ℝ) : ∑ i, musclRhs g dx nf φ u i = 0
theorem musclRhs_constant (g : Grid I) (dx : ℝ) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (c : ℝ) (i : I) :
    musclRhs g dx nf φ (fun _ => c) i = 0
theorem leftState_mem (g : Grid I) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ) (m M : ℝ) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) (i : I) : m ≤ leftState g φ u i ∧ leftState g φ u i ≤ M
theorem rightState_mem  -- the same for rightState

-- B3-K  (namespace CFDLean.Scalar, then CFDLean.Burgers.Rusanov)
def LipschitzOnBounds (nf : NumericalFlux) (m M KL KR : ℝ) : Prop :=
  (∀ a a' b, m ≤ a → a ≤ M → m ≤ a' → a' ≤ M → m ≤ b → b ≤ M →
    |nf.eval a b - nf.eval a' b| ≤ KL * |a - a'|) ∧
  (∀ a b b', m ≤ a → a ≤ M → m ≤ b → b ≤ M → m ≤ b' → b' ≤ M →
    |nf.eval a b - nf.eval a b'| ≤ KR * |b - b'|)
theorem eval_lipschitz_left (A a a' b : ℝ) (ha : |a| ≤ A) (ha' : |a'| ≤ A) (hb : |b| ≤ A) :
    |eval a b - eval a' b| ≤ 2 * A * |a - a'|
theorem eval_lipschitz_right (A a b b' : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ A) (hb' : |b'| ≤ A) :
    |eval a b - eval a b'| ≤ 2 * A * |b - b'|
theorem lipschitzOnBounds (m M : ℝ) :
    LipschitzOnBounds numericalFlux m M (2 * max |m| |M|) (2 * max |m| |M|)

-- B3-I  (namespace CFDLean.Scalar.FiniteVolume)
theorem muscl_incremental (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ)
    (hmono : MonotoneFlux nf) (m M KL KR : ℝ) (hlip : LipschitzOnBounds nf m M KL KR) (hKL : 0 ≤ KL)
    (hKR : 0 ≤ KR) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    ∃ C D : I → ℝ,
      (∀ i, 0 ≤ C i ∧ C i ≤ dt / dx * (3 / 2 * KR)) ∧
      (∀ i, 0 ≤ D i ∧ D i ≤ dt / dx * (3 / 2 * KL)) ∧
      Time.ForwardEuler.step dt (musclRhs g dx nf φ) u = incrementalUpdate g C D u

-- B3-T
theorem muscl_step_totalVariation_le [Fintype I] (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ)
    (hφ : MinmodBounded φ) (hmono : MonotoneFlux nf) (m M KL KR : ℝ) (hlip : LipschitzOnBounds nf m M KL KR)
    (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : dt * (3 / 2 * (KL + KR)) ≤ dx) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) :
    totalVariation g (Time.ForwardEuler.step dt (musclRhs g dx nf φ) u) ≤ totalVariation g u
theorem muscl_step_mem  -- same hypotheses: Time.ForwardEuler.step dt (musclRhs g dx nf φ) u ∈ boundedStates m M

-- B3-S  (namespace CFDLean.Burgers.Rusanov)
def musclEulerStep (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) : (I → ℝ) → I → ℝ :=
  Time.ForwardEuler.step dt (musclRhs g dx numericalFlux φ)
def musclSsprk2Step (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) : (I → ℝ) → I → ℝ :=
  Time.SSP.ssprk2 (musclEulerStep g dx dt φ)
def musclSsprk3Step (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) : (I → ℝ) → I → ℝ :=
  Time.SSP.ssprk3 (musclEulerStep g dx dt φ)

-- one theorem for each T in {musclEulerStep, musclSsprk2Step, musclSsprk3Step}:
theorem T_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : MinmodBounded φ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) (n : ℕ) :
    (T g dx dt φ)^[n] u ∈ boundedStates m M ∧
      totalVariation g ((T g dx dt φ)^[n] u) ≤ totalVariation g u
theorem T_sum [Fintype I] (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) (hdx : dx ≠ 0) (u : I → ℝ) :
    ∑ i, T g dx dt φ u i = ∑ i, u i
theorem T_constant (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) (c : ℝ) :
    T g dx dt φ (fun _ => c) = fun _ => c
```

The one-step theorems `musclEulerStep_mem` and `musclEulerStep_totalVariation_le` and the `minmod` instances are
supporting or additional results. Supporting lemmas may be added with any name. `0 ≤ KL`, `0 ≤ KR` are necessary in
B3-I (a counterexample on the degenerate interval `m = M` is part of the implementation); B3-T does not need them.

## Frozen module layout

```text
CFDLean/Schemes/Scalar/Lipschitz.lean              B3-K certificate
CFDLean/Discrete/Periodic/Muscl.lean               B3-L, B3-R, B3-I, B3-T
CFDLean/Schemes/Burgers/RusanovMuscl.lean          B3-K for Rusanov, B3-S
CFDLean/Schemes/Burgers/MusclControls.lean         exact small controls
CFDLean/Verification/BurgersB3Challenge.lean       trusted statements, Mathlib only
CFDLean/Verification/BurgersB3Verify.lean          bridge
Challenges/BurgersB3.lean                          `lake comparator` challenge
```

## Trusted statements

`CFDLean/Verification/BurgersB3Challenge.lean` imports only Mathlib and restates its own definitions (Rusanov flux,
minmod, the MUSCL Euler step with minmod on `next : I ≃ I`, total variation, `ssprk2`, `ssprk3`). It states:

| Trusted statement | Content | Result ID |
| --- | --- | --- |
| `MinmodProperties` | the four inequalities of the limiter certificate for `minmod` | B3-L |
| `RusanovLipschitz` | `|F(a,b) - F(a',b)| ≤ 2A|a - a'|` and the same in the right state, for `|a|, |a'|, |b| ≤ A` | B3-K |
| `MusclEulerMultiStep I`, `MusclSSPRK2MultiStep I`, `MusclSSPRK3MultiStep I` | bounds and total variation after `n` steps of the MUSCL-minmod-Rusanov scheme under `dx > 0`, `dt ≥ 0`, `m ≤ u ≤ M`, `6 · dt · max(|m|, |M|) ≤ dx` | B3-S |
| `MusclEulerConservation I`, `MusclSSPRK2Conservation I`, `MusclSSPRK3Conservation I` | one step keeps the total sum when `dx ≠ 0` | B3-S |

## Explicitly excluded from B3

B3 does **not** claim or implement:

- second-order accuracy of the reconstruction or of the scheme (no truncation-error statement);
- limiters outside the minmod region (MC, superbee, van Leer), other reconstructions (PPM, ENO, WENO);
- a sharp CFL constant; a CFL estimator; variable time steps;
- entropy inequalities, convergence;
- floating-point, arrays, parallel execution.

## Frozen B3 result IDs

| ID | Required result |
| --- | --- |
| B3-L | Limiter certificate `MinmodBounded`; `minmod` and the zero limiter have it |
| B3-R | MUSCL reconstruction and right-hand side; first-order recovery; conservation; constant states; reconstructed states keep the bounds |
| B3-K | Lipschitz certificate of a two-point flux on bounded states; the Burgers Rusanov flux has it with `2 max(|m|, |M|)` |
| B3-I | The MUSCL Forward-Euler step is in incremental form with bounded nonnegative coefficients |
| B3-T | Generic one-step total-variation and bounds theorems of the MUSCL step |
| B3-S | MUSCL-Rusanov: multi-step bounds and TVD for Euler, SSPRK2, SSPRK3; conservation; constant states |

Independent implementation review remains separate from implementation authorization.
