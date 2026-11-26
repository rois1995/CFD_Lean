import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.ZMod.Basic

/-! Trusted Burgers B3b statements (`specifications/Burgers-B3b.md`). This file imports only Mathlib and restates every
definition it uses. `a` is the backward difference `u_i - u_{i-1}`, `b` the forward difference `u_{i+1} - u_i`.
`next : I ≃ I` is the periodic successor of the cells; `next.symm` is the predecessor. `T^[n]` is `n` applications of
`T`. Sums and scalar multiples of cell functions are pointwise. -/
noncomputable section
namespace CFDLean.Verification.BurgersB3bChallenge

open scoped BigOperators

/-- Burgers physical flux `f(u) = u² / 2`. -/
def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

/-- Rusanov wave speed `a(uL, uR) = max(|uL|, |uR|)`. -/
def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

/-- Rusanov (local Lax-Friedrichs) flux for Burgers. -/
def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

/-- The unlimited slope: the central difference `(a + b) / 2`. -/
def centralSlope (a b : ℝ) : ℝ := (a + b) / 2

/-- Sign of `a`, used only for `a ≠ 0`. -/
def sgn (a : ℝ) : ℝ := if 0 < a then 1 else -1

/-- Minmod: the argument of smaller absolute value when both have the same strict sign, else zero. -/
def minmod (a b : ℝ) : ℝ :=
  if 0 < a ∧ 0 < b then min a b else if a < 0 ∧ b < 0 then max a b else 0

/-- Monotonized central (MC): `sgn(a) min(|a + b|/2, 2|a|, 2|b|)` when `ab > 0`, else zero. -/
def mc (a b : ℝ) : ℝ :=
  if 0 < a * b then sgn a * min (|a + b| / 2) (min (2 * |a|) (2 * |b|)) else 0

/-- Superbee: `sgn(a) max(min(2|a|, |b|), min(|a|, 2|b|))` when `ab > 0`, else zero. -/
def superbee (a b : ℝ) : ℝ :=
  if 0 < a * b then sgn a * max (min (2 * |a|) |b|) (min |a| (2 * |b|)) else 0

/-- Van Leer (harmonic mean): `2ab / (a + b)` when `ab > 0`, else zero. -/
def vanLeer (a b : ℝ) : ℝ :=
  if 0 < a * b then 2 * (a * b) / (a + b) else 0

/-- Van Albada: `ab(a + b) / (a² + b²)` when `ab > 0`, else zero. -/
def vanAlbada (a b : ℝ) : ℝ :=
  if 0 < a * b then a * b * (a + b) / (a ^ 2 + b ^ 2) else 0

/-- The limited slope `L` is a factor between `0` and `c` times the unlimited slope. -/
def IsFactorOnCentral (L : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ a b : ℝ, ∃ ψ : ℝ, 0 ≤ ψ ∧ ψ ≤ c ∧ L a b = ψ * centralSlope a b

/-- B3b-L: every limiter is a factor on top of the unlimited slope; the factor is at most 1, for superbee 4/3. -/
def LimiterFactorForms : Prop :=
  IsFactorOnCentral minmod 1 ∧ IsFactorOnCentral mc 1 ∧ IsFactorOnCentral superbee (4 / 3) ∧
    IsFactorOnCentral vanLeer 1 ∧ IsFactorOnCentral vanAlbada 1

/-- The slope `σ = φ(a, b)` has the sign of `a` and of `b`, and `|σ| ≤ θ|a|`, `|σ| ≤ θ|b|`. -/
def SlopeBounded (θ : ℝ) (φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ φ a b * a ∧ 0 ≤ φ a b * b ∧ |φ a b| ≤ θ * |a| ∧ |φ a b| ≤ θ * |b|

/-- B3b-L: the bound constant of each limiter. -/
def LimiterBounds : Prop :=
  SlopeBounded 1 minmod ∧ SlopeBounded 2 mc ∧ SlopeBounded 2 superbee ∧ SlopeBounded 2 vanLeer ∧
    SlopeBounded (5 / 4) vanAlbada

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Two-stage SSP Runge-Kutta step over a one-step map `E`: `½ u + ½ E(E u)`. -/
def ssprk2 (E : V → V) (u : V) : V := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • E (E u)

/-- Three-stage SSP Runge-Kutta step over a one-step map `E`: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

end Generic

variable {I : Type*}

/-- Total variation on the periodic grid: `Σ_i |u_{i+1} - u_i|`. -/
def totalVariation [Fintype I] (next : I ≃ I) (u : I → ℝ) : ℝ :=
  ∑ i, |u (next i) - u i|

/-- Slope of cell `i` for the slope function `φ`: `σ_i = φ(u_i - u_{i-1}, u_{i+1} - u_i)`. -/
def slope (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (u : I → ℝ) (i : I) : ℝ :=
  φ (u i - u (next.symm i)) (u (next i) - u i)

/-- Reconstructed state at the right face of cell `i`: `u_i + σ_i / 2`. -/
def facePlus (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (u : I → ℝ) (i : I) : ℝ := u i + slope φ next u i / 2

/-- Reconstructed state at the left face of cell `i`: `u_i - σ_i / 2`. -/
def faceMinus (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (u : I → ℝ) (i : I) : ℝ := u i - slope φ next u i / 2

/-- One Forward-Euler step of the MUSCL scheme with the slope function `φ` and the Rusanov flux:
`v_i = u_i - (dt/dx) (F(u_i⁺, u_{i+1}⁻) - F(u_{i-1}⁺, u_i⁻))`. With `φ = centralSlope` the scheme is unlimited. -/
def musclEulerStep (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ) : I → ℝ :=
  fun i => u i + dt *
    (-(rusanov (facePlus φ next u i) (faceMinus φ next u (next i)) -
        rusanov (facePlus φ next u (next.symm i)) (faceMinus φ next u i)) / dx)

/-- A time-stepping map `T` (given the slope function, the grid, `dx` and `dt`) is multi-step stable when: for every
`θ ≤ 2` and every `θ`-bounded slope function, `dx > 0`, `dt ≥ 0`, bounds `m ≤ u_j ≤ M` of the initial state and
`(4 + 2θ) · dt · max(|m|, |M|) ≤ dx`, the state after `n` steps has the same bounds and no larger total variation,
for every `n`. -/
def MultiStepStable (I : Type*) [Fintype I]
    (T : (ℝ → ℝ → ℝ) → (I ≃ I) → ℝ → ℝ → (I → ℝ) → I → ℝ) : Prop :=
  ∀ (θ : ℝ) (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ) (m M : ℝ) (n : ℕ),
    θ ≤ 2 → SlopeBounded θ φ → 0 < dx → 0 ≤ dt → (4 + 2 * θ) * (dt * max |m| |M|) ≤ dx →
    (∀ j, m ≤ u j ∧ u j ≤ M) →
    (∀ j, m ≤ (T φ next dx dt)^[n] u j ∧ (T φ next dx dt)^[n] u j ≤ M) ∧
      totalVariation next ((T φ next dx dt)^[n] u) ≤ totalVariation next u

/-- B3b-S: MUSCL-Rusanov with a bounded slope and Forward Euler. -/
def MusclEulerBoundedMultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I musclEulerStep

/-- B3b-S: MUSCL-Rusanov with a bounded slope and SSPRK2. -/
def MusclSSPRK2BoundedMultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I (fun φ next dx dt => ssprk2 (musclEulerStep φ next dx dt))

/-- B3b-S: MUSCL-Rusanov with a bounded slope and SSPRK3. -/
def MusclSSPRK3BoundedMultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I (fun φ next dx dt => ssprk3 (musclEulerStep φ next dx dt))

/-- The state `(0, 0, 1, 1)` on four periodic cells. -/
def stepData : ZMod 4 → ℝ := fun i => if i = 2 ∨ i = 3 then 1 else 0

/-- B3b-N: the unlimited scheme is not bound preserving. The state `(0, 0, 1, 1)` is in `[0, 1]`, the time step
`dt = 1/10` with `dx = 1` satisfies `8 · dt · max(|0|, |1|) ≤ dx`, and one unlimited step gives `167/160 > 1` in
cell 3. -/
def UnlimitedOvershoot : Prop :=
  (∀ j, 0 ≤ stepData j ∧ stepData j ≤ 1) ∧ 8 * (1 / 10 * max |(0 : ℝ)| |1|) ≤ (1 : ℝ) ∧
    musclEulerStep centralSlope (Equiv.addRight (1 : ZMod 4)) 1 (1 / 10) stepData 3 = 167 / 160

end CFDLean.Verification.BurgersB3bChallenge
