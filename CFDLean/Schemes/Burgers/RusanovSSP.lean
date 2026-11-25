import CFDLean.Schemes.Burgers.RusanovStability
import CFDLean.Discrete.Periodic.Convexity
import CFDLean.Time.SSP

/-! Burgers B2-B (Rusanov part) and B2-S: with one time step chosen from the bounds `m ≤ u ≤ M` of the initial state,
`2 · dt · max(|m|, |M|) ≤ dx`, the Rusanov scheme with Forward Euler, SSPRK2 or SSPRK3 keeps the bounds and does not
increase the total variation for every number of steps. The SSP results are compositions of the generic results of
`CFDLean.Time.SSP` with the one-step B1 theorems. -/
noncomputable section
namespace CFDLean.Burgers

open Scalar Periodic
open scoped BigOperators

namespace Rusanov

variable {I : Type*}

/-- The Rusanov Forward-Euler map of B0 on a periodic grid. -/
def eulerStep (g : Grid I) (dx dt : ℝ) : (I → ℝ) → I → ℝ :=
  Time.ForwardEuler.step dt (FiniteVolume.rhs g dx numericalFlux)

/-- B2-B: on states between `m` and `M` the Rusanov wave speed is at most `max(|m|, |M|)`. -/
theorem waveSpeed_le_of_bounds (m M a b : ℝ) (ha : m ≤ a ∧ a ≤ M) (hb : m ≤ b ∧ b ≤ M) :
    waveSpeed a b ≤ max |m| |M| := by
  unfold waveSpeed
  have h : ∀ x, m ≤ x ∧ x ≤ M → |x| ≤ max |m| |M| := by
    intro x hx
    have h1 := neg_abs_le m
    have h2 := le_max_left |m| |M|
    have h3 := le_abs_self M
    have h4 := le_max_right |m| |M|
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  exact max_le (h a ha) (h b hb)

/-- B2-B: the Euler map keeps the bounds of the state under the CFL hypothesis taken from the bounds. -/
theorem eulerStep_mem (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ FiniteVolume.boundedStates m M) :
    eulerStep g dx dt u ∈ FiniteVolume.boundedStates m M := by
  intro i
  refine step_bounds g dx dt hdx hdt u m M (fun j => ?_) (fun j => (hu j).1) (fun j => (hu j).2) i
  have h := mul_le_mul_of_nonneg_left (waveSpeed_le_of_bounds m M _ _ (hu j) (hu (g.next j))) hdt
  linarith

/-- B2-B: the Euler map does not increase the total variation of a bounded state under the same hypothesis. -/
theorem eulerStep_totalVariation_le [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ FiniteVolume.boundedStates m M) :
    FiniteVolume.totalVariation g (eulerStep g dx dt u) ≤ FiniteVolume.totalVariation g u := by
  refine step_totalVariation_le g dx dt hdx hdt u (fun j => ?_)
  have h := mul_le_mul_of_nonneg_left (waveSpeed_le_of_bounds m M _ _ (hu j) (hu (g.next j))) hdt
  have h0 : 0 ≤ dt * max |m| |M| := mul_nonneg hdt (le_max_of_le_left (abs_nonneg m))
  linarith

/-- The Euler map keeps the total sum (B0 conservation). -/
theorem eulerStep_sum [Fintype I] (g : Grid I) (dx dt : ℝ) (hdx : dx ≠ 0) (u : I → ℝ) :
    ∑ i, eulerStep g dx dt u i = ∑ i, u i :=
  Time.ForwardEuler.step_sum dt _ u (FiniteVolume.rhs_sum_zero g dx hdx numericalFlux u)

/-- The Euler map keeps constant states (B0 consistency). -/
theorem eulerStep_constant (g : Grid I) (dx dt c : ℝ) : eulerStep g dx dt (fun _ => c) = fun _ => c :=
  Time.ForwardEuler.step_constant dt _ c
    (funext fun i => FiniteVolume.rhs_constant g dx c law numericalFlux consistent i)

/-- B2-S: one SSPRK2 step of the Rusanov scheme. -/
def ssprk2Step (g : Grid I) (dx dt : ℝ) : (I → ℝ) → I → ℝ := Time.SSP.ssprk2 (eulerStep g dx dt)

/-- B2-S: one SSPRK3 step of the Rusanov scheme. -/
def ssprk3Step (g : Grid I) (dx dt : ℝ) : (I → ℝ) → I → ℝ := Time.SSP.ssprk3 (eulerStep g dx dt)

/-- B2-S: bounds and total variation after `n` Forward-Euler steps. -/
theorem eulerStep_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ FiniteVolume.boundedStates m M) (n : ℕ) :
    (eulerStep g dx dt)^[n] u ∈ FiniteVolume.boundedStates m M ∧
      FiniteVolume.totalVariation g ((eulerStep g dx dt)^[n] u) ≤ FiniteVolume.totalVariation g u :=
  ⟨Time.SSP.iterate_mem _ _ (eulerStep_mem g dx dt m M hdx hdt hcfl) u hu n,
    Time.SSP.iterate_le _ _ _ (eulerStep_mem g dx dt m M hdx hdt hcfl)
      (eulerStep_totalVariation_le g dx dt m M hdx hdt hcfl) u hu n⟩

/-- B2-S: bounds and total variation after `n` SSPRK2 steps. -/
theorem ssprk2Step_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ FiniteVolume.boundedStates m M) (n : ℕ) :
    (ssprk2Step g dx dt)^[n] u ∈ FiniteVolume.boundedStates m M ∧
      FiniteVolume.totalVariation g ((ssprk2Step g dx dt)^[n] u) ≤ FiniteVolume.totalVariation g u := by
  have hE := eulerStep_mem g dx dt m M hdx hdt hcfl
  have hS := FiniteVolume.boundedStates_convex (I := I) m M
  have hT : ∀ v ∈ FiniteVolume.boundedStates m M, ssprk2Step g dx dt v ∈ FiniteVolume.boundedStates m M :=
    fun v hv => Time.SSP.ssprk2_mem _ _ hS hE v hv
  exact ⟨Time.SSP.iterate_mem _ _ hT u hu n, Time.SSP.iterate_le _ _ _ hT
    (fun v hv => Time.SSP.ssprk2_le _ _ _ (FiniteVolume.totalVariation_convexOn g _ hS) hE
      (eulerStep_totalVariation_le g dx dt m M hdx hdt hcfl) v hv) u hu n⟩

/-- B2-S: bounds and total variation after `n` SSPRK3 steps. -/
theorem ssprk3Step_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ FiniteVolume.boundedStates m M) (n : ℕ) :
    (ssprk3Step g dx dt)^[n] u ∈ FiniteVolume.boundedStates m M ∧
      FiniteVolume.totalVariation g ((ssprk3Step g dx dt)^[n] u) ≤ FiniteVolume.totalVariation g u := by
  have hE := eulerStep_mem g dx dt m M hdx hdt hcfl
  have hS := FiniteVolume.boundedStates_convex (I := I) m M
  have hT : ∀ v ∈ FiniteVolume.boundedStates m M, ssprk3Step g dx dt v ∈ FiniteVolume.boundedStates m M :=
    fun v hv => Time.SSP.ssprk3_mem _ _ hS hE v hv
  exact ⟨Time.SSP.iterate_mem _ _ hT u hu n, Time.SSP.iterate_le _ _ _ hT
    (fun v hv => Time.SSP.ssprk3_le _ _ _ (FiniteVolume.totalVariation_convexOn g _ hS) hE
      (eulerStep_totalVariation_le g dx dt m M hdx hdt hcfl) v hv) u hu n⟩

/-- B2-S: one SSPRK2 step keeps the total sum. -/
theorem ssprk2Step_sum [Fintype I] (g : Grid I) (dx dt : ℝ) (hdx : dx ≠ 0) (u : I → ℝ) :
    ∑ i, ssprk2Step g dx dt u i = ∑ i, u i := by
  have h := Time.SSP.ssprk2_linear (eulerStep g dx dt) FiniteVolume.totalSum
    (fun v => by simp only [FiniteVolume.totalSum_apply, eulerStep_sum g dx dt hdx v]) u
  simp only [FiniteVolume.totalSum_apply] at h
  exact h

/-- B2-S: one SSPRK3 step keeps the total sum. -/
theorem ssprk3Step_sum [Fintype I] (g : Grid I) (dx dt : ℝ) (hdx : dx ≠ 0) (u : I → ℝ) :
    ∑ i, ssprk3Step g dx dt u i = ∑ i, u i := by
  have h := Time.SSP.ssprk3_linear (eulerStep g dx dt) FiniteVolume.totalSum
    (fun v => by simp only [FiniteVolume.totalSum_apply, eulerStep_sum g dx dt hdx v]) u
  simp only [FiniteVolume.totalSum_apply] at h
  exact h

/-- B2-S: one SSPRK2 step keeps constant states. -/
theorem ssprk2Step_constant (g : Grid I) (dx dt c : ℝ) : ssprk2Step g dx dt (fun _ => c) = fun _ => c :=
  Time.SSP.ssprk2_fixed _ _ (eulerStep_constant g dx dt c)

/-- B2-S: one SSPRK3 step keeps constant states. -/
theorem ssprk3Step_constant (g : Grid I) (dx dt c : ℝ) : ssprk3Step g dx dt (fun _ => c) = fun _ => c :=
  Time.SSP.ssprk3_fixed _ _ (eulerStep_constant g dx dt c)

end Rusanov

namespace Schemes.RusanovForwardEuler

variable {N : ℕ} [NeZero N]

/-- The assembled `ZMod N` step of B0 is the general Euler map on the grid `grid`. -/
theorem step_eq_eulerStep (dx dt : ℝ) : step (N := N) dx dt = Rusanov.eulerStep (grid (N := N)) dx dt :=
  rfl

end Schemes.RusanovForwardEuler
end CFDLean.Burgers
