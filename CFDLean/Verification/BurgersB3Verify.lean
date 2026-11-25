import CFDLean.Verification.BurgersB3Challenge
import CFDLean.Schemes.Burgers.RusanovMuscl

/-! Bridge: the B3 implementation proves the trusted B3 statements. -/
noncomputable section
namespace CFDLean.Verification.BurgersB3Verify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Scalar
open CFDLean.Periodic

/-- The trusted minmod is the implemented minmod. -/
theorem minmod_eq : BurgersB3Challenge.minmod = FiniteVolume.minmod := rfl

/-- The trusted MUSCL Euler step is the implemented one on the grid of `next` with the minmod limiter. -/
theorem musclEulerStep_eq {I : Type*} (next : I ≃ I) (dx dt : ℝ) :
    BurgersB3Challenge.musclEulerStep next dx dt = Rusanov.musclEulerStep ⟨next⟩ dx dt FiniteVolume.minmod := by
  funext u i
  simp [BurgersB3Challenge.musclEulerStep, BurgersB3Challenge.facePlus, BurgersB3Challenge.faceMinus,
    BurgersB3Challenge.slope, minmod_eq, BurgersB3Challenge.rusanov, BurgersB3Challenge.burgersFlux,
    BurgersB3Challenge.rusanovWaveSpeed, Rusanov.musclEulerStep, Time.ForwardEuler.step, FiniteVolume.musclRhs,
    FiniteVolume.musclFlux, FiniteVolume.leftState, FiniteVolume.rightState, FiniteVolume.slope,
    Rusanov.numericalFlux, Rusanov.eval, Rusanov.waveSpeed, physicalFlux, Grid.prev]

theorem minmod_properties : BurgersB3Challenge.MinmodProperties :=
  FiniteVolume.minmod_minmodBounded

theorem rusanov_lipschitz : BurgersB3Challenge.RusanovLipschitz := by
  intro A a a' b ha ha' hb
  exact ⟨Rusanov.eval_lipschitz_left A a a' b ha ha' hb, Rusanov.eval_lipschitz_right A b a a' hb ha ha'⟩

theorem muscl_euler_multi_step {I : Type*} [Fintype I] : BurgersB3Challenge.MusclEulerMultiStep I := by
  intro next dx dt u m M n hdx hdt hcfl hu
  rw [musclEulerStep_eq]
  exact Rusanov.musclEulerStep_iterate_stable ⟨next⟩ dx dt m M _ FiniteVolume.minmod_minmodBounded hdx hdt hcfl
    u hu n

theorem muscl_ssprk2_multi_step {I : Type*} [Fintype I] : BurgersB3Challenge.MusclSSPRK2MultiStep I := by
  intro next dx dt u m M n hdx hdt hcfl hu
  simp only [musclEulerStep_eq]
  exact Rusanov.musclSsprk2Step_iterate_stable ⟨next⟩ dx dt m M _ FiniteVolume.minmod_minmodBounded hdx hdt hcfl
    u hu n

theorem muscl_ssprk3_multi_step {I : Type*} [Fintype I] : BurgersB3Challenge.MusclSSPRK3MultiStep I := by
  intro next dx dt u m M n hdx hdt hcfl hu
  simp only [musclEulerStep_eq]
  exact Rusanov.musclSsprk3Step_iterate_stable ⟨next⟩ dx dt m M _ FiniteVolume.minmod_minmodBounded hdx hdt hcfl
    u hu n

theorem muscl_euler_conservation {I : Type*} [Fintype I] : BurgersB3Challenge.MusclEulerConservation I := by
  intro next dx dt u hdx
  rw [musclEulerStep_eq]
  exact Rusanov.musclEulerStep_sum ⟨next⟩ dx dt _ hdx u

theorem muscl_ssprk2_conservation {I : Type*} [Fintype I] : BurgersB3Challenge.MusclSSPRK2Conservation I := by
  intro next dx dt u hdx
  rw [musclEulerStep_eq]
  exact Rusanov.musclSsprk2Step_sum ⟨next⟩ dx dt _ hdx u

theorem muscl_ssprk3_conservation {I : Type*} [Fintype I] : BurgersB3Challenge.MusclSSPRK3Conservation I := by
  intro next dx dt u hdx
  rw [musclEulerStep_eq]
  exact Rusanov.musclSsprk3Step_sum ⟨next⟩ dx dt _ hdx u

end CFDLean.Verification.BurgersB3Verify
