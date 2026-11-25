import CFDLean.Verification.BurgersB2Challenge
import CFDLean.Schemes.Burgers.RusanovSSP

/-! Bridge: the B2 implementation proves the trusted B2 statements. -/
noncomputable section
namespace CFDLean.Verification.BurgersB2Verify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Scalar
open CFDLean.Periodic

/-- The trusted Euler step is the implemented Euler map on the grid of `next`. -/
theorem eulerStep_eq {I : Type*} (next : I ≃ I) (dx dt : ℝ) :
    BurgersB2Challenge.eulerStep next dx dt = Rusanov.eulerStep ⟨next⟩ dx dt := by
  funext u i
  simp [BurgersB2Challenge.eulerStep, BurgersB2Challenge.rusanov, BurgersB2Challenge.burgersFlux,
    BurgersB2Challenge.rusanovWaveSpeed, Rusanov.eulerStep, Time.ForwardEuler.step, FiniteVolume.rhs,
    FiniteVolume.interfaceFlux, Rusanov.numericalFlux, Rusanov.eval, Rusanov.waveSpeed, physicalFlux, Grid.prev]

theorem ssprk2_convex {V : Type*} [AddCommGroup V] [Module ℝ V] : BurgersB2Challenge.SSPRK2Convex V := by
  intro E S Φ hΦ hE hΦE u hu
  exact ⟨Time.SSP.ssprk2_mem E S hΦ.1 hE u hu, Time.SSP.ssprk2_le E S Φ hΦ hE hΦE u hu⟩

theorem ssprk3_convex {V : Type*} [AddCommGroup V] [Module ℝ V] : BurgersB2Challenge.SSPRK3Convex V := by
  intro E S Φ hΦ hE hΦE u hu
  exact ⟨Time.SSP.ssprk3_mem E S hΦ.1 hE u hu, Time.SSP.ssprk3_le E S Φ hΦ hE hΦE u hu⟩

theorem euler_multi_step {I : Type*} [Fintype I] : BurgersB2Challenge.EulerMultiStep I := by
  intro next dx dt u m M n hdx hdt hcfl hu
  rw [eulerStep_eq]
  exact Rusanov.eulerStep_iterate_stable ⟨next⟩ dx dt m M hdx hdt hcfl u hu n

theorem ssprk2_multi_step {I : Type*} [Fintype I] : BurgersB2Challenge.SSPRK2MultiStep I := by
  intro next dx dt u m M n hdx hdt hcfl hu
  simp only [eulerStep_eq]
  exact Rusanov.ssprk2Step_iterate_stable ⟨next⟩ dx dt m M hdx hdt hcfl u hu n

theorem ssprk3_multi_step {I : Type*} [Fintype I] : BurgersB2Challenge.SSPRK3MultiStep I := by
  intro next dx dt u m M n hdx hdt hcfl hu
  simp only [eulerStep_eq]
  exact Rusanov.ssprk3Step_iterate_stable ⟨next⟩ dx dt m M hdx hdt hcfl u hu n

theorem ssprk2_conservation {I : Type*} [Fintype I] : BurgersB2Challenge.SSPRK2Conservation I := by
  intro next dx dt u hdx
  rw [eulerStep_eq]
  exact Rusanov.ssprk2Step_sum ⟨next⟩ dx dt hdx u

theorem ssprk3_conservation {I : Type*} [Fintype I] : BurgersB2Challenge.SSPRK3Conservation I := by
  intro next dx dt u hdx
  rw [eulerStep_eq]
  exact Rusanov.ssprk3Step_sum ⟨next⟩ dx dt hdx u

end CFDLean.Verification.BurgersB2Verify
