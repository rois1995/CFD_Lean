import CFDLean.Verification.BurgersB1Challenge
import CFDLean.Schemes.Burgers.RusanovStability

/-! Bridge: the B1 implementation proves the trusted B1 statements. -/
noncomputable section
namespace CFDLean.Verification.BurgersB1Verify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Scalar
open CFDLean.Periodic

/-- The trusted Rusanov step is the implemented Forward-Euler step on the grid of `next`. -/
theorem rusanovStep_eq {I : Type*} (next : I ≃ I) (dx dt : ℝ) (u : I → ℝ) :
    BurgersB1Challenge.rusanovStep next dx dt u =
      Time.ForwardEuler.step dt (FiniteVolume.rhs ⟨next⟩ dx Rusanov.numericalFlux) u := by
  funext i
  simp [BurgersB1Challenge.rusanovStep, BurgersB1Challenge.rusanov, BurgersB1Challenge.burgersFlux,
    BurgersB1Challenge.rusanovWaveSpeed, Time.ForwardEuler.step, FiniteVolume.rhs, FiniteVolume.interfaceFlux,
    Rusanov.numericalFlux, Rusanov.eval, Rusanov.waveSpeed, physicalFlux, Grid.prev]

theorem rusanov_monotone : BurgersB1Challenge.RusanovMonotone :=
  Rusanov.monotone

theorem harten_total_variation {I : Type*} [Fintype I] : BurgersB1Challenge.HartenTotalVariation I := by
  intro next C D u hC hD hCD
  exact FiniteVolume.incrementalUpdate_totalVariation_le ⟨next⟩ C D u hC hD hCD

theorem incremental_bounds {I : Type*} : BurgersB1Challenge.IncrementalBounds I := by
  intro next C D u m M i hC hD hCD hm hM
  exact FiniteVolume.incrementalUpdate_bounds ⟨next⟩ C D u m M i hC hD hCD hm hM

theorem rusanov_total_variation {I : Type*} [Fintype I] : BurgersB1Challenge.RusanovTotalVariation I := by
  intro next dx dt u hdx hdt hcfl
  rw [rusanovStep_eq]
  exact Rusanov.step_totalVariation_le ⟨next⟩ dx dt hdx hdt u hcfl

theorem rusanov_bounds {I : Type*} : BurgersB1Challenge.RusanovBounds I := by
  intro next dx dt u m M hdx hdt hcfl hm hM i
  rw [rusanovStep_eq]
  exact Rusanov.step_bounds ⟨next⟩ dx dt hdx hdt u m M hcfl hm hM i

end CFDLean.Verification.BurgersB1Verify
