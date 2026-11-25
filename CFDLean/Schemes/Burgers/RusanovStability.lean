import CFDLean.Schemes.Burgers.RusanovForwardEuler
import CFDLean.Schemes.Scalar.Monotone
import CFDLean.Discrete.Periodic.TotalVariation
import Mathlib.Tactic

/-! Burgers B1-M, B1-I, B1-S: the Burgers Rusanov flux is monotone; the Rusanov Forward-Euler step is in incremental
form with nonnegative coefficients; under a per-interface CFL hypothesis the step does not increase the total variation
(CFL 1) and keeps the bounds of the old state (CFL 1/2). The stability theorems are compositions of the generic lemmas
of `CFDLean.Discrete.Periodic.TotalVariation`. -/
noncomputable section
namespace CFDLean.Burgers

open Scalar Periodic

namespace Rusanov

variable {I : Type*}

/-- B1-M, left state. -/
theorem eval_mono_left (a a' b : ℝ) (h : a ≤ a') : eval a b ≤ eval a' b := by
  simp only [eval, waveSpeed, physicalFlux]
  rcases le_total |a| |b| with h1 | h1 <;> rcases le_total |a'| |b| with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;>
    rcases abs_cases a with ⟨ea, _⟩ | ⟨ea, _⟩ <;> rcases abs_cases a' with ⟨ea', _⟩ | ⟨ea', _⟩ <;>
    rcases abs_cases b with ⟨eb, _⟩ | ⟨eb, _⟩ <;> rw [ea, eb] at h1 <;> rw [ea', eb] at h2 <;>
    simp only [ea, ea', eb] <;> nlinarith

/-- B1-M, right state. -/
theorem eval_anti_right (a b b' : ℝ) (h : b ≤ b') : eval a b' ≤ eval a b := by
  simp only [eval, waveSpeed, physicalFlux]
  rcases le_total |a| |b| with h1 | h1 <;> rcases le_total |a| |b'| with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;>
    rcases abs_cases a with ⟨ea, _⟩ | ⟨ea, _⟩ <;> rcases abs_cases b with ⟨eb, _⟩ | ⟨eb, _⟩ <;>
    rcases abs_cases b' with ⟨eb', _⟩ | ⟨eb', _⟩ <;> rw [ea, eb] at h1 <;> rw [ea, eb'] at h2 <;>
    simp only [ea, eb, eb'] <;> nlinarith

/-- B1-M: the Burgers Rusanov flux is a monotone two-point flux. -/
theorem monotone : MonotoneFlux numericalFlux :=
  ⟨eval_mono_left, eval_anti_right⟩

/-- Coefficient of `u_{i+1} - u_i` in the incremental form of the Rusanov Forward-Euler step. -/
def incrementC (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) : ℝ :=
  dt / dx * ((waveSpeed (u i) (u (g.next i)) - (u i + u (g.next i)) / 2) / 2)

/-- Coefficient of `u_{i+1} - u_i` seen from cell `i + 1` in the incremental form. -/
def incrementD (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) : ℝ :=
  dt / dx * ((waveSpeed (u i) (u (g.next i)) + (u i + u (g.next i)) / 2) / 2)

/-- B1-I: the mean of two states is bounded by the Rusanov wave speed. -/
theorem abs_mean_le_waveSpeed (a b : ℝ) : |(a + b) / 2| ≤ waveSpeed a b := by
  unfold waveSpeed
  have h1 := le_max_left |a| |b|
  have h2 := le_max_right |a| |b|
  rw [abs_le]
  constructor <;> linarith [neg_abs_le a, neg_abs_le b, le_abs_self a, le_abs_self b]

/-- B1-I: the Rusanov Forward-Euler step is in incremental form. No hypothesis on `dx` or `dt`. -/
theorem step_eq_incrementalUpdate (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) :
    Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u i =
      FiniteVolume.incrementalUpdate g (incrementC g dx dt u) (incrementD g dx dt u) u i := by
  simp only [Time.ForwardEuler.step, FiniteVolume.rhs, FiniteVolume.interfaceFlux, numericalFlux, eval,
    physicalFlux, FiniteVolume.incrementalUpdate, incrementC, incrementD, g.next_prev]
  ring

theorem incrementC_nonneg (g : Grid I) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : I → ℝ) (i : I) :
    0 ≤ incrementC g dx dt u i := by
  have h := abs_le.mp (abs_mean_le_waveSpeed (u i) (u (g.next i)))
  exact mul_nonneg (div_nonneg hdt hdx.le) (by linarith)

theorem incrementD_nonneg (g : Grid I) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : I → ℝ) (i : I) :
    0 ≤ incrementD g dx dt u i := by
  have h := abs_le.mp (abs_mean_le_waveSpeed (u i) (u (g.next i)))
  exact mul_nonneg (div_nonneg hdt hdx.le) (by linarith)

theorem incrementC_add_incrementD (g : Grid I) (dx dt : ℝ) (u : I → ℝ) (i : I) :
    incrementC g dx dt u i + incrementD g dx dt u i = dt * waveSpeed (u i) (u (g.next i)) / dx := by
  simp only [incrementC, incrementD]
  ring

/-- B1-S: under `dt · a_i ≤ dx` at every interface the Rusanov Forward-Euler step does not increase the total
variation. Composition of B1-I and the generic lemma B1-H. -/
theorem step_totalVariation_le [Fintype I] (g : Grid I) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : I → ℝ)
    (hcfl : ∀ i, dt * waveSpeed (u i) (u (g.next i)) ≤ dx) :
    FiniteVolume.totalVariation g (Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u) ≤
      FiniteVolume.totalVariation g u := by
  have e : Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u =
      FiniteVolume.incrementalUpdate g (incrementC g dx dt u) (incrementD g dx dt u) u :=
    funext (step_eq_incrementalUpdate g dx dt u)
  rw [e]
  refine FiniteVolume.incrementalUpdate_totalVariation_le g _ _ u
    (incrementC_nonneg g dx dt hdx hdt u) (incrementD_nonneg g dx dt hdx hdt u) (fun i => ?_)
  rw [incrementC_add_incrementD, div_le_one hdx]
  exact hcfl i

/-- B1-S: under `2 · dt · a_i ≤ dx` at every interface the Rusanov Forward-Euler step keeps every lower and upper
bound of the old state. Composition of B1-I and the generic lemma B1-X. -/
theorem step_bounds (g : Grid I) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : I → ℝ) (m M : ℝ)
    (hcfl : ∀ i, 2 * (dt * waveSpeed (u i) (u (g.next i))) ≤ dx)
    (hm : ∀ j, m ≤ u j) (hM : ∀ j, u j ≤ M) (i : I) :
    m ≤ Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u i ∧
      Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux) u i ≤ M := by
  rw [step_eq_incrementalUpdate]
  have hr : 0 ≤ dt / dx := div_nonneg hdt hdx.le
  have hw : ∀ j, dt / dx * waveSpeed (u j) (u (g.next j)) ≤ 1 / 2 := by
    intro j
    rw [div_mul_eq_mul_div, div_le_iff₀ hdx]
    linarith [hcfl j]
  have b1 := abs_le.mp (abs_mean_le_waveSpeed (u i) (u (g.next i)))
  have b2 := abs_le.mp (abs_mean_le_waveSpeed (u (g.prev i)) (u (g.next (g.prev i))))
  refine FiniteVolume.incrementalUpdate_bounds g _ _ u m M i (incrementC_nonneg g dx dt hdx hdt u i)
    (incrementD_nonneg g dx dt hdx hdt u (g.prev i)) ?_ hm hM
  have h1 := hw i
  have h2 := hw (g.prev i)
  simp only [incrementC, incrementD]
  nlinarith [mul_le_mul_of_nonneg_left b1.1 hr, mul_le_mul_of_nonneg_left b2.2 hr]

end Rusanov

namespace Schemes.RusanovForwardEuler

open Scalar.FiniteVolume

variable {N : ℕ} [NeZero N]

/-- B1-S on `ZMod N`: total variation under the per-interface CFL hypothesis. -/
theorem step_totalVariation_le (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : ZMod N → ℝ)
    (hcfl : ∀ i, dt * Rusanov.waveSpeed (u i) (u ((grid (N := N)).next i)) ≤ dx) :
    totalVariation (grid (N := N)) (step (N := N) dx dt u) ≤ totalVariation (grid (N := N)) u :=
  Rusanov.step_totalVariation_le (grid (N := N)) dx dt hdx hdt u hcfl

/-- B1-S on `ZMod N`: bounds under the per-interface CFL hypothesis with constant 1/2. -/
theorem step_bounds (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : ZMod N → ℝ) (m M : ℝ)
    (hcfl : ∀ i, 2 * (dt * Rusanov.waveSpeed (u i) (u ((grid (N := N)).next i))) ≤ dx)
    (hm : ∀ j, m ≤ u j) (hM : ∀ j, u j ≤ M) (i : ZMod N) :
    m ≤ step (N := N) dx dt u i ∧ step (N := N) dx dt u i ≤ M :=
  Rusanov.step_bounds (grid (N := N)) dx dt hdx hdt u m M hcfl hm hM i

end Schemes.RusanovForwardEuler
end CFDLean.Burgers
