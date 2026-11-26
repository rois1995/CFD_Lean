import CFDLean.Discrete.Periodic.Limiters
import CFDLean.Schemes.Burgers.RusanovMuscl

/-! Burgers B3b-S, B3b-N: the MUSCL-Rusanov scheme with a `θ`-bounded slope (`θ ≤ 2`) keeps the bounds of the initial
state and does not increase the total variation under `(4 + 2θ) · dt · max(|m|, |M|) ≤ dx`, with Forward Euler,
SSPRK2 and SSPRK3; instances for the five limiters. The unlimited scheme is not bound preserving: one exact example. -/
noncomputable section
namespace CFDLean.Burgers.Rusanov

open Scalar Periodic Scalar.FiniteVolume

variable {I : Type*}

theorem cfl_of_bounded (dx dt m M θ : ℝ) (hcfl : (4 + 2 * θ) * (dt * max |m| |M|) ≤ dx) :
    dt * ((1 + θ / 2) * (2 * max |m| |M| + 2 * max |m| |M|)) ≤ dx := by
  have e : dt * ((1 + θ / 2) * (2 * max |m| |M| + 2 * max |m| |M|)) = (4 + 2 * θ) * (dt * max |m| |M|) := by ring
  rw [e]
  exact hcfl

/-- B3b: under `(4 + 2θ) · dt · max(|m|, |M|) ≤ dx` the MUSCL-Rusanov Forward-Euler step keeps the bounds. -/
theorem musclEulerStep_mem_bounded (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hθ2 : θ ≤ 2) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : (4 + 2 * θ) * (dt * max |m| |M|) ≤ dx) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) : musclEulerStep g dx dt φ u ∈ boundedStates m M :=
  muscl_step_mem_bounded g numericalFlux φ θ hφ hθ2 monotone m M _ _ (lipschitzOnBounds m M) dx dt hdx hdt
    (cfl_of_bounded dx dt m M θ hcfl) u hu

/-- B3b: under `(4 + 2θ) · dt · max(|m|, |M|) ≤ dx` the MUSCL-Rusanov Forward-Euler step does not increase the
total variation. -/
theorem musclEulerStep_totalVariation_le_bounded [Fintype I] (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : (4 + 2 * θ) * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    totalVariation g (musclEulerStep g dx dt φ u) ≤ totalVariation g u :=
  muscl_step_totalVariation_le_bounded g numericalFlux φ θ hφ hθ2 monotone m M _ _ (lipschitzOnBounds m M) dx dt
    hdx hdt (cfl_of_bounded dx dt m M θ hcfl) u hu

/-- B3b: bounds and total variation after `n` MUSCL-Rusanov Forward-Euler steps. -/
theorem musclEulerStep_iterate_stable_bounded [Fintype I] (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : (4 + 2 * θ) * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclEulerStep g dx dt φ)^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclEulerStep g dx dt φ)^[n] u) ≤ totalVariation g u :=
  ⟨Time.SSP.iterate_mem _ _ (musclEulerStep_mem_bounded g dx dt m M φ θ hφ hθ2 hdx hdt hcfl) u hu n,
    Time.SSP.iterate_le _ _ _ (musclEulerStep_mem_bounded g dx dt m M φ θ hφ hθ2 hdx hdt hcfl)
      (musclEulerStep_totalVariation_le_bounded g dx dt m M φ θ hφ hθ2 hdx hdt hcfl) u hu n⟩

/-- B3b: bounds and total variation after `n` MUSCL-Rusanov SSPRK2 steps. -/
theorem musclSsprk2Step_iterate_stable_bounded [Fintype I] (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : (4 + 2 * θ) * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk2Step g dx dt φ)^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk2Step g dx dt φ)^[n] u) ≤ totalVariation g u := by
  have hE := musclEulerStep_mem_bounded g dx dt m M φ θ hφ hθ2 hdx hdt hcfl
  have hS := boundedStates_convex (I := I) m M
  have hT : ∀ v ∈ boundedStates m M, musclSsprk2Step g dx dt φ v ∈ boundedStates m M :=
    fun v hv => Time.SSP.ssprk2_mem _ _ hS hE v hv
  exact ⟨Time.SSP.iterate_mem _ _ hT u hu n, Time.SSP.iterate_le _ _ _ hT
    (fun v hv => Time.SSP.ssprk2_le _ _ _ (totalVariation_convexOn g _ hS) hE
      (musclEulerStep_totalVariation_le_bounded g dx dt m M φ θ hφ hθ2 hdx hdt hcfl) v hv) u hu n⟩

/-- B3b: bounds and total variation after `n` MUSCL-Rusanov SSPRK3 steps. -/
theorem musclSsprk3Step_iterate_stable_bounded [Fintype I] (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : (4 + 2 * θ) * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk3Step g dx dt φ)^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk3Step g dx dt φ)^[n] u) ≤ totalVariation g u := by
  have hE := musclEulerStep_mem_bounded g dx dt m M φ θ hφ hθ2 hdx hdt hcfl
  have hS := boundedStates_convex (I := I) m M
  have hT : ∀ v ∈ boundedStates m M, musclSsprk3Step g dx dt φ v ∈ boundedStates m M :=
    fun v hv => Time.SSP.ssprk3_mem _ _ hS hE v hv
  exact ⟨Time.SSP.iterate_mem _ _ hT u hu n, Time.SSP.iterate_le _ _ _ hT
    (fun v hv => Time.SSP.ssprk3_le _ _ _ (totalVariation_convexOn g _ hS) hE
      (musclEulerStep_totalVariation_le_bounded g dx dt m M φ θ hφ hθ2 hdx hdt hcfl) v hv) u hu n⟩

/-- B3b with the minmod factor (`θ = 1`): SSPRK3 under `6 · dt · max(|m|, |M|) ≤ dx`. -/
theorem musclSsprk3Step_minmodFactor_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk3Step g dx dt (limitedSlope minmodFactor))^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk3Step g dx dt (limitedSlope minmodFactor))^[n] u) ≤ totalVariation g u :=
  musclSsprk3Step_iterate_stable_bounded g dx dt m M _ 1 slopeBounded_minmodFactor one_le_two hdx hdt
    (by linarith) u hu n

/-- B3b with the MC factor (`θ = 2`): SSPRK3 under `8 · dt · max(|m|, |M|) ≤ dx`. -/
theorem musclSsprk3Step_mc_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : 8 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk3Step g dx dt (limitedSlope mcFactor))^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk3Step g dx dt (limitedSlope mcFactor))^[n] u) ≤ totalVariation g u :=
  musclSsprk3Step_iterate_stable_bounded g dx dt m M _ 2 slopeBounded_mcFactor le_rfl hdx hdt (by linarith) u hu n

/-- B3b with the superbee factor (`θ = 2`): SSPRK3 under `8 · dt · max(|m|, |M|) ≤ dx`. -/
theorem musclSsprk3Step_superbee_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : 8 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk3Step g dx dt (limitedSlope superbeeFactor))^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk3Step g dx dt (limitedSlope superbeeFactor))^[n] u) ≤ totalVariation g u :=
  musclSsprk3Step_iterate_stable_bounded g dx dt m M _ 2 slopeBounded_superbeeFactor le_rfl hdx hdt (by linarith)
    u hu n

/-- B3b with the van Leer factor (`θ = 2`): SSPRK3 under `8 · dt · max(|m|, |M|) ≤ dx`. -/
theorem musclSsprk3Step_vanLeer_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : 8 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk3Step g dx dt (limitedSlope vanLeerFactor))^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk3Step g dx dt (limitedSlope vanLeerFactor))^[n] u) ≤ totalVariation g u :=
  musclSsprk3Step_iterate_stable_bounded g dx dt m M _ 2 slopeBounded_vanLeerFactor le_rfl hdx hdt (by linarith)
    u hu n

/-- B3b with the van Albada factor (`θ = 5/4`): SSPRK3 under `13/2 · dt · max(|m|, |M|) ≤ dx`. -/
theorem musclSsprk3Step_vanAlbada_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : 13 / 2 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk3Step g dx dt (limitedSlope vanAlbadaFactor))^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk3Step g dx dt (limitedSlope vanAlbadaFactor))^[n] u) ≤ totalVariation g u :=
  musclSsprk3Step_iterate_stable_bounded g dx dt m M _ (5 / 4) slopeBounded_vanAlbadaFactor (by norm_num) hdx hdt
    (by linarith) u hu n

/-! ### The unlimited scheme is not bound preserving -/

/-- The four-cell state `(0, 0, 1, 1)`. -/
def stepData : ZMod 4 → ℝ := fun i => if i = 2 ∨ i = 3 then 1 else 0

theorem stepData_mem : stepData ∈ boundedStates 0 1 := fun j => by
  simp only [stepData]
  split_ifs <;> norm_num

open CFDLean.Burgers.Schemes.RusanovForwardEuler in
/-- B3b: the unlimited scheme is not bound preserving. On four cells with the state `(0, 0, 1, 1)` in `[0, 1]`,
`dx = 1` and `dt = 1/10` (so the CFL condition `8 · dt · max(|0|, |1|) ≤ dx` of the `θ = 2` limiters holds), one
unlimited MUSCL-Rusanov Forward-Euler step gives `167/160 > 1` in cell 3. -/
theorem unlimited_step_leaves_bounds :
    8 * (1 / 10 * max |(0 : ℝ)| |1|) ≤ (1 : ℝ) ∧
      musclEulerStep grid 1 (1 / 10) centralSlope stepData 3 = 167 / 160 := by
  refine ⟨by norm_num, ?_⟩
  have e1 : (3 + 1 : ZMod 4) = 0 := by decide
  have e2 : (3 + -1 : ZMod 4) = 2 := by decide
  have e3 : (0 + 1 : ZMod 4) = 1 := by decide
  have e4 : (2 + -1 : ZMod 4) = 1 := by decide
  have e5 : (2 + 1 : ZMod 4) = 3 := by decide
  have e6 : (0 + -1 : ZMod 4) = 3 := by decide
  have v0 : stepData 0 = 0 := ite_eq_right (by decide)
  have v1 : stepData 1 = 0 := ite_eq_right (by decide)
  have v2 : stepData 2 = 1 := ite_eq_left (by decide)
  have v3 : stepData 3 = 1 := ite_eq_left (by decide)
  simp only [musclEulerStep, Time.ForwardEuler.step, musclRhs, musclFlux, leftState, rightState, FiniteVolume.slope,
    centralSlope, grid, zmodGrid, Grid.prev, Equiv.addRight_symm, Equiv.coe_addRight, e1, e2, e3, e4, e5, e6, v0, v1,
    v2, v3]
  norm_num [numericalFlux, eval, waveSpeed, physicalFlux]

end CFDLean.Burgers.Rusanov
