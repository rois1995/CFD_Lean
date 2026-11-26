# Burgers B3b: unlimited MUSCL reconstruction with limiters on top

Status: **frozen for implementation on 2026-11-26 by the agent** (`specifications/Burgers-B3b-approval.md`). The user
asked for this formulation and for the limiters; no human approved the statements of this contract.

Base: Burgers B0--B4, E0, E0b on `main`. Toolchain: Lean v4.36.0. Exact real arithmetic. No new dependency.

## Purpose

B3 has the MUSCL reconstruction for any slope function and one stability class, the minmod region. B3b changes the
formulation to the one of production codes:

```text
reconstruction = unlimited slope (central difference)        the default
               × limiter factor ψ(a, b)                      optional, on top;  no limiter: ψ = 1
```

and it adds the widely used limiters with a wider certificate.

## Mathematics

`a = u_i - u_{i-1}` (backward difference), `b = u_{i+1} - u_i` (forward difference).

- Unlimited slope: `s(a, b) = (a + b)/2` (central difference; with it MUSCL is Fromm's scheme).
- Limited slope: `σ = ψ(a, b) · s(a, b)` for a limiter factor `ψ`.
- The reconstruction of B3 is unchanged: `σ_i = φ(a_i, b_i)`, `L_i = u_i + σ_i/2`, `R_i = u_{i+1} - σ_{i+1}/2`, with
  `φ = s` (unlimited) or `φ = ψ · s` (limited).

**Limiter factors.** All are 0 unless `a` and `b` have the same strict sign (`ab > 0`). For `ab > 0`:

| Limiter | Factor `ψ(a, b)` | Limited slope `ψ · s` (classical form) | `θ` |
| --- | --- | --- | --- |
| minmod | `2 min(\|a\|,\|b\|) / (\|a\|+\|b\|)` | `sgn(a) min(\|a\|, \|b\|)` | 1 |
| MC (monotonized central) | `min(1, 4 min(\|a\|,\|b\|) / (\|a\|+\|b\|))` | `sgn(a) min(\|a+b\|/2, 2\|a\|, 2\|b\|)` | 2 |
| superbee | `2 max(min(2\|a\|,\|b\|), min(\|a\|,2\|b\|)) / (\|a\|+\|b\|)` | `sgn(a) max(min(2\|a\|,\|b\|), min(\|a\|,2\|b\|))` | 2 |
| van Leer | `4ab / (a+b)²` | `2ab / (a+b)` | 2 |
| van Albada | `2ab / (a²+b²)` | `ab(a+b) / (a²+b²)` | 5/4 |

The factors of minmod, MC, van Leer and van Albada are in `[0, 1]`; the superbee factor is in `[0, 4/3]`.

**Certificate (Sweby region) with a constant `θ`.** A slope function `φ` is `θ`-bounded when `σ = φ(a, b)` has the
sign of `a` and of `b` and `|σ| ≤ θ|a|`, `|σ| ≤ θ|b|` (written without division). `θ = 1` is the minmod region of B3.
The unlimited slope has no such bound for any `θ`.

**Stability.** For a `θ`-bounded slope with `θ ≤ 2`, a monotone flux with the Lipschitz certificate of B3, `dx > 0`,
`dt ≥ 0`, `m ≤ u ≤ M`: the Forward-Euler MUSCL step is an incremental update with
`0 ≤ C_i ≤ (dt/dx)(1 + θ/2) KR`, `0 ≤ D_i ≤ (dt/dx)(1 + θ/2) KL`. The ratios `(R_i - R_{i-1})/Δ_i` and
`(L_i - L_{i-1})/Δ_{i-1}` are in `[1 - θ/2, 1 + θ/2]`; `θ ≤ 2` keeps them nonnegative and keeps the reconstructed
states in `[m, M]`. So under `dt (1 + θ/2)(KL + KR) ≤ dx` one step keeps the bounds and does not increase the total
variation. For Burgers with Rusanov (`KL = KR = 2 max(|m|, |M|)`): `(4 + 2θ) · dt · max(|m|, |M|) ≤ dx`, that is
CFL 1/6 for minmod, 2/13 for van Albada, 1/8 for MC, superbee and van Leer. These constants are sufficient, not sharp.

**The unlimited scheme is not bound preserving.** Four cells, state `(0, 0, 1, 1)`, `dx = 1`, `dt = 1/10` (inside the
CFL 1/8 range): one unlimited MUSCL-Rusanov Forward-Euler step gives `167/160 > 1` in the last cell.

## Frozen decisions

1. The default reconstruction is unlimited (`centralSlope`). A limiter is a factor on top (`limitedSlope ψ`).
   `noLimiter` is the factor 1.
2. The B3 definitions and theorems do not change; `MinmodBounded φ` is `SlopeBounded 1 φ` (proved). B0--B4, E0, E0b
   sources do not change.
3. Conservation and constant states need no limiter (B3: `musclRhs_sum_zero`, `musclRhs_constant` hold for every
   slope function). Bounds and total variation need the certificate.
4. The constant for van Albada is `5/4` (the sharp value is `(1 + √2)/2`).
5. Time stepping: Forward Euler, SSPRK2, SSPRK3 through the B2 composition, one `dt` for all steps.

## Frozen Lean statements

```lean
-- B3b-U  (namespace CFDLean.Scalar.FiniteVolume)
def centralSlope (a b : ℝ) : ℝ := (a + b) / 2
def limitedSlope (ψ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ := ψ a b * centralSlope a b
def noLimiter : ℝ → ℝ → ℝ := fun _ _ => 1
theorem limitedSlope_noLimiter : limitedSlope noLimiter = centralSlope

-- B3b-C
def SlopeBounded (θ : ℝ) (φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b, 0 ≤ φ a b * a ∧ 0 ≤ φ a b * b ∧ |φ a b| ≤ θ * |a| ∧ |φ a b| ≤ θ * |b|
theorem minmodBounded_iff_slopeBounded_one (φ : ℝ → ℝ → ℝ) : MinmodBounded φ ↔ SlopeBounded 1 φ
theorem SlopeBounded.mono : SlopeBounded θ φ → θ ≤ θ' → SlopeBounded θ' φ
theorem SlopeBounded.nonneg : SlopeBounded θ φ → 0 ≤ θ
theorem not_slopeBounded_centralSlope (θ : ℝ) : ¬ SlopeBounded θ centralSlope

-- B3b-L
def minmodFactor (a b : ℝ) : ℝ := if 0 < a * b then 2 * min |a| |b| / (|a| + |b|) else 0
def mcFactor (a b : ℝ) : ℝ := if 0 < a * b then min 1 (4 * min |a| |b| / (|a| + |b|)) else 0
def superbeeFactor (a b : ℝ) : ℝ :=
  if 0 < a * b then 2 * max (min (2 * |a|) |b|) (min |a| (2 * |b|)) / (|a| + |b|) else 0
def vanLeerFactor (a b : ℝ) : ℝ := if 0 < a * b then 4 * (a * b) / (a + b) ^ 2 else 0
def vanAlbadaFactor (a b : ℝ) : ℝ := if 0 < a * b then 2 * (a * b) / (a ^ 2 + b ^ 2) else 0

theorem limitedSlope_minmodFactor : limitedSlope minmodFactor = minmod
theorem limitedSlope_mcFactor (a b : ℝ) : limitedSlope mcFactor a b =
    if 0 < a * b then (if 0 < a then 1 else -1) * min (|a + b| / 2) (min (2 * |a|) (2 * |b|)) else 0
theorem limitedSlope_superbeeFactor (a b : ℝ) : limitedSlope superbeeFactor a b =
    if 0 < a * b then (if 0 < a then 1 else -1) * max (min (2 * |a|) |b|) (min |a| (2 * |b|)) else 0
theorem limitedSlope_vanLeerFactor (a b : ℝ) : limitedSlope vanLeerFactor a b =
    if 0 < a * b then 2 * (a * b) / (a + b) else 0
theorem limitedSlope_vanAlbadaFactor (a b : ℝ) : limitedSlope vanAlbadaFactor a b =
    if 0 < a * b then a * b * (a + b) / (a ^ 2 + b ^ 2) else 0

-- factor ranges `0 ≤ ψ a b ∧ ψ a b ≤ c` (c = 1; superbee: c = 4/3) and symmetry `ψ a b = ψ b a`:
theorem minmodFactor_mem, mcFactor_mem, vanLeerFactor_mem, vanAlbadaFactor_mem, superbeeFactor_mem
theorem minmodFactor_comm, mcFactor_comm, superbeeFactor_comm, vanLeerFactor_comm, vanAlbadaFactor_comm

theorem slopeBounded_minmodFactor : SlopeBounded 1 (limitedSlope minmodFactor)
theorem slopeBounded_mcFactor : SlopeBounded 2 (limitedSlope mcFactor)
theorem slopeBounded_superbeeFactor : SlopeBounded 2 (limitedSlope superbeeFactor)
theorem slopeBounded_vanLeerFactor : SlopeBounded 2 (limitedSlope vanLeerFactor)
theorem slopeBounded_vanAlbadaFactor : SlopeBounded (5 / 4) (limitedSlope vanAlbadaFactor)

-- B3b-I
theorem muscl_incremental_bounded (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (hmono : MonotoneFlux nf) (m M KL KR : ℝ)
    (hlip : LipschitzOnBounds nf m M KL KR) (hKL : 0 ≤ KL) (hKR : 0 ≤ KR) (dx dt : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    ∃ C D : I → ℝ,
      (∀ i, 0 ≤ C i ∧ C i ≤ dt / dx * ((1 + θ / 2) * KR)) ∧
      (∀ i, 0 ≤ D i ∧ D i ≤ dt / dx * ((1 + θ / 2) * KL)) ∧
      Time.ForwardEuler.step dt (musclRhs g dx nf φ) u = incrementalUpdate g C D u

-- B3b-T   hypotheses: SlopeBounded θ φ, θ ≤ 2, MonotoneFlux nf, LipschitzOnBounds nf m M KL KR, 0 < dx, 0 ≤ dt,
--         dt * ((1 + θ / 2) * (KL + KR)) ≤ dx, u ∈ boundedStates m M
theorem muscl_step_totalVariation_le_bounded   -- totalVariation g (step) ≤ totalVariation g u
theorem muscl_step_mem_bounded                 -- step ∈ boundedStates m M

-- B3b-S  (namespace CFDLean.Burgers.Rusanov; φ with SlopeBounded θ φ, θ ≤ 2, 0 < dx, 0 ≤ dt,
--         hcfl : (4 + 2 * θ) * (dt * max |m| |M|) ≤ dx, u ∈ boundedStates m M)
theorem musclEulerStep_mem_bounded, musclEulerStep_totalVariation_le_bounded
theorem musclEulerStep_iterate_stable_bounded, musclSsprk2Step_iterate_stable_bounded,
        musclSsprk3Step_iterate_stable_bounded          -- shape of B3 `musclSsprk3Step_iterate_stable`
-- SSPRK3 instances with the numeric constant 6, 8, 8, 8, 13/2:
theorem musclSsprk3Step_minmodFactor_iterate_stable, musclSsprk3Step_mc_iterate_stable,
        musclSsprk3Step_superbee_iterate_stable, musclSsprk3Step_vanLeer_iterate_stable,
        musclSsprk3Step_vanAlbada_iterate_stable

-- B3b-N
def stepData : ZMod 4 → ℝ := fun i => if i = 2 ∨ i = 3 then 1 else 0
theorem stepData_mem : stepData ∈ boundedStates 0 1
theorem unlimited_step_leaves_bounds :
    8 * (1 / 10 * max |(0 : ℝ)| |1|) ≤ (1 : ℝ) ∧
      musclEulerStep grid 1 (1 / 10) centralSlope stepData 3 = 167 / 160
```

Supporting lemmas may be added with any name.

## Frozen module layout

```text
CFDLean/Discrete/Periodic/Limiters.lean            B3b-U, B3b-C, B3b-L, B3b-I, B3b-T
CFDLean/Schemes/Burgers/RusanovLimiters.lean       B3b-S, B3b-N
CFDLean/Schemes/Burgers/LimiterControls.lean       exact small controls
CFDLean/Verification/BurgersB3bChallenge.lean      trusted statements, Mathlib only
CFDLean/Verification/BurgersB3bVerify.lean         bridge
Challenges/BurgersB3b.lean                         `lake comparator` challenge
```

## Trusted statements

`CFDLean/Verification/BurgersB3bChallenge.lean` imports only Mathlib. It restates the five limiters in their classical
slope form, the central slope, the Rusanov flux, the MUSCL step with a general slope function on `next : I ≃ I`, the
total variation and the SSP steps. It states:

| Trusted statement | Content | Result ID |
| --- | --- | --- |
| `LimiterFactorForms` | each classical limited slope is a factor times the central slope, with the factor in `[0, 1]` (superbee: `[0, 4/3]`) | B3b-L |
| `LimiterBounds` | each classical limited slope is `θ`-bounded with `θ = 1, 2, 2, 2, 5/4` | B3b-L |
| `MusclEulerBoundedMultiStep I`, `MusclSSPRK2BoundedMultiStep I`, `MusclSSPRK3BoundedMultiStep I` | for every `θ ≤ 2` and every `θ`-bounded slope function: bounds and total variation after `n` steps under `dx > 0`, `dt ≥ 0`, `m ≤ u ≤ M`, `(4 + 2θ) · dt · max(\|m\|, \|M\|) ≤ dx` | B3b-S |
| `UnlimitedOvershoot` | the four-cell example: one unlimited step gives `167/160` in a cell of a state in `[0, 1]` | B3b-N |

## Explicitly excluded from B3b

- other limiters (Koren, ospre, UMIST, Venkatakrishnan, Barth--Jespersen), other unlimited slopes (one-sided, κ-family);
- sharp CFL constants; the sharp van Albada constant;
- accuracy statements (second order away from extrema, loss of order at extrema);
- limiters in the executable kernel (a later milestone, E0c);
- entropy inequalities for MUSCL.

## Frozen B3b result IDs

| ID | Required result |
| --- | --- |
| B3b-U | Unlimited central slope; limiter factor on top; no limiter is the factor 1 |
| B3b-C | Certificate `SlopeBounded θ`; `θ = 1` is the minmod region of B3; the unlimited slope has no certificate |
| B3b-L | Limiter factors minmod, MC, superbee, van Leer, van Albada: classical forms, ranges, symmetry, certificates |
| B3b-I | Incremental form of the MUSCL Forward-Euler step for a `θ`-bounded slope, `θ ≤ 2` |
| B3b-T | Generic one-step total-variation and bounds theorems with the constant `1 + θ/2` |
| B3b-S | MUSCL-Rusanov with a `θ`-bounded slope: one-step and multi-step results for Euler, SSPRK2, SSPRK3; instances for the five limiters |
| B3b-N | The unlimited scheme is not bound preserving (exact example) |

Independent implementation review remains separate from implementation authorization.
