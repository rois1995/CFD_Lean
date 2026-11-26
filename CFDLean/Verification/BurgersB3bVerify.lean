import CFDLean.Verification.BurgersB3bChallenge
import CFDLean.Schemes.Burgers.RusanovLimiters

/-! Bridge: the B3b implementation proves the trusted B3b statements. -/
noncomputable section
namespace CFDLean.Verification.BurgersB3bVerify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Scalar
open CFDLean.Periodic

theorem centralSlope_eq : BurgersB3bChallenge.centralSlope = FiniteVolume.centralSlope := rfl

theorem minmod_eq : BurgersB3bChallenge.minmod = FiniteVolume.limitedSlope FiniteVolume.minmodFactor :=
  FiniteVolume.limitedSlope_minmodFactor.symm

theorem mc_eq : BurgersB3bChallenge.mc = FiniteVolume.limitedSlope FiniteVolume.mcFactor :=
  funext fun a => funext fun b => (FiniteVolume.limitedSlope_mcFactor a b).symm

theorem superbee_eq : BurgersB3bChallenge.superbee = FiniteVolume.limitedSlope FiniteVolume.superbeeFactor :=
  funext fun a => funext fun b => (FiniteVolume.limitedSlope_superbeeFactor a b).symm

theorem vanLeer_eq : BurgersB3bChallenge.vanLeer = FiniteVolume.limitedSlope FiniteVolume.vanLeerFactor :=
  funext fun a => funext fun b => (FiniteVolume.limitedSlope_vanLeerFactor a b).symm

theorem vanAlbada_eq : BurgersB3bChallenge.vanAlbada = FiniteVolume.limitedSlope FiniteVolume.vanAlbadaFactor :=
  funext fun a => funext fun b => (FiniteVolume.limitedSlope_vanAlbadaFactor a b).symm

/-- A limited slope with a factor in `[0, c]` is a factor on the trusted central slope. -/
theorem factor_form {L ψ : ℝ → ℝ → ℝ} {c : ℝ} (hL : L = FiniteVolume.limitedSlope ψ)
    (hψ : ∀ a b, 0 ≤ ψ a b ∧ ψ a b ≤ c) : BurgersB3bChallenge.IsFactorOnCentral L c :=
  fun a b => ⟨ψ a b, (hψ a b).1, (hψ a b).2, by rw [hL]; rfl⟩

theorem limiter_factor_forms : BurgersB3bChallenge.LimiterFactorForms :=
  ⟨factor_form minmod_eq FiniteVolume.minmodFactor_mem, factor_form mc_eq FiniteVolume.mcFactor_mem,
    factor_form superbee_eq FiniteVolume.superbeeFactor_mem, factor_form vanLeer_eq FiniteVolume.vanLeerFactor_mem,
    factor_form vanAlbada_eq FiniteVolume.vanAlbadaFactor_mem⟩

theorem limiter_bounds : BurgersB3bChallenge.LimiterBounds := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [minmod_eq]; exact FiniteVolume.slopeBounded_minmodFactor
  · rw [mc_eq]; exact FiniteVolume.slopeBounded_mcFactor
  · rw [superbee_eq]; exact FiniteVolume.slopeBounded_superbeeFactor
  · rw [vanLeer_eq]; exact FiniteVolume.slopeBounded_vanLeerFactor
  · rw [vanAlbada_eq]; exact FiniteVolume.slopeBounded_vanAlbadaFactor

/-- The trusted MUSCL Euler step is the implemented one on the grid of `next`, for every slope function. -/
theorem musclEulerStep_eq {I : Type*} (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (dx dt : ℝ) :
    BurgersB3bChallenge.musclEulerStep φ next dx dt = Rusanov.musclEulerStep ⟨next⟩ dx dt φ := by
  funext u i
  simp [BurgersB3bChallenge.musclEulerStep, BurgersB3bChallenge.facePlus, BurgersB3bChallenge.faceMinus,
    BurgersB3bChallenge.slope, BurgersB3bChallenge.rusanov, BurgersB3bChallenge.burgersFlux,
    BurgersB3bChallenge.rusanovWaveSpeed, Rusanov.musclEulerStep, Time.ForwardEuler.step, FiniteVolume.musclRhs,
    FiniteVolume.musclFlux, FiniteVolume.leftState, FiniteVolume.rightState, FiniteVolume.slope,
    Rusanov.numericalFlux, Rusanov.eval, Rusanov.waveSpeed, physicalFlux, Grid.prev]

theorem muscl_euler_bounded_multi_step {I : Type*} [Fintype I] :
    BurgersB3bChallenge.MusclEulerBoundedMultiStep I := by
  intro θ φ next dx dt u m M n hθ hφ hdx hdt hcfl hu
  rw [musclEulerStep_eq]
  exact Rusanov.musclEulerStep_iterate_stable_bounded ⟨next⟩ dx dt m M φ θ hφ hθ hdx hdt hcfl u hu n

theorem muscl_ssprk2_bounded_multi_step {I : Type*} [Fintype I] :
    BurgersB3bChallenge.MusclSSPRK2BoundedMultiStep I := by
  intro θ φ next dx dt u m M n hθ hφ hdx hdt hcfl hu
  simp only [musclEulerStep_eq]
  exact Rusanov.musclSsprk2Step_iterate_stable_bounded ⟨next⟩ dx dt m M φ θ hφ hθ hdx hdt hcfl u hu n

theorem muscl_ssprk3_bounded_multi_step {I : Type*} [Fintype I] :
    BurgersB3bChallenge.MusclSSPRK3BoundedMultiStep I := by
  intro θ φ next dx dt u m M n hθ hφ hdx hdt hcfl hu
  simp only [musclEulerStep_eq]
  exact Rusanov.musclSsprk3Step_iterate_stable_bounded ⟨next⟩ dx dt m M φ θ hφ hθ hdx hdt hcfl u hu n

theorem unlimited_overshoot : BurgersB3bChallenge.UnlimitedOvershoot := by
  refine ⟨Rusanov.stepData_mem, Rusanov.unlimited_step_leaves_bounds.1, ?_⟩
  rw [musclEulerStep_eq]
  exact Rusanov.unlimited_step_leaves_bounds.2

end CFDLean.Verification.BurgersB3bVerify
