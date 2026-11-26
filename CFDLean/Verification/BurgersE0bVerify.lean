import CFDLean.Verification.BurgersE0bChallenge
import CFDLean.Exec.MusclRefinement

/-! Bridge: the E0b refinement theorems prove the trusted E0b statements. -/
noncomputable section
namespace CFDLean.Verification.BurgersE0bVerify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Periodic

/-- The trusted representation relation is the implemented one. -/
theorem represents_iff {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) :
    BurgersE0bChallenge.Represents a u ↔ Exec.Represents a u :=
  ⟨fun h => ⟨h.1, fun i => h.2 i (h.1 ▸ i.isLt)⟩, fun ⟨hs, h⟩ => ⟨hs, fun i _ => h i⟩⟩

/-- The trusted minmod is the implemented minmod. -/
theorem minmod_eq : BurgersE0bChallenge.minmod = Scalar.FiniteVolume.minmod := rfl

/-- The trusted MUSCL Euler step on `Fin n` is the MUSCL-Rusanov Euler map on `finGrid n` with minmod. -/
theorem musclEulerStep_eq {n : ℕ} [NeZero n] (dx dt : ℝ) :
    BurgersE0bChallenge.musclEulerStep (n := n) dx dt =
      Rusanov.musclEulerStep (Exec.finGrid n) dx dt Scalar.FiniteVolume.minmod := by
  funext u i
  simp [BurgersE0bChallenge.musclEulerStep, BurgersE0bChallenge.facePlus, BurgersE0bChallenge.faceMinus,
    BurgersE0bChallenge.slope, minmod_eq, BurgersE0bChallenge.rusanov, BurgersE0bChallenge.burgersFlux,
    BurgersE0bChallenge.rusanovWaveSpeed, Rusanov.musclEulerStep, Time.ForwardEuler.step,
    Scalar.FiniteVolume.musclRhs, Scalar.FiniteVolume.musclFlux, Scalar.FiniteVolume.leftState,
    Scalar.FiniteVolume.rightState, Scalar.FiniteVolume.slope, Rusanov.numericalFlux, Rusanov.eval,
    Rusanov.waveSpeed, physicalFlux, Exec.finGrid, Grid.prev, sub_eq_add_neg]

theorem kernel_minmod_is_minmod : BurgersE0bChallenge.KernelMinmodIsMinmod :=
  fun a b => Exec.minmod_eq a b

theorem muscl_euler_step_refines : BurgersE0bChallenge.MusclEulerStepRefines := by
  intro n _ dx dt a u h
  rw [musclEulerStep_eq]
  exact (represents_iff _ _).mpr (Exec.musclEulerStepArray_refines dx dt ((represents_iff _ _).mp h))

theorem muscl_ssprk3_step_refines : BurgersE0bChallenge.MusclSSPRK3StepRefines := by
  intro n _ dx dt a u h
  rw [musclEulerStep_eq]
  exact (represents_iff _ _).mpr (Exec.musclSsprk3StepArray_refines dx dt ((represents_iff _ _).mp h))

theorem muscl_ssprk3_run_refines : BurgersE0bChallenge.MusclSSPRK3RunRefines := by
  intro n _ dx dt a u k h
  rw [musclEulerStep_eq]
  exact (represents_iff _ _).mpr
    (Exec.run_refines (fun _ _ h => Exec.musclSsprk3StepArray_refines dx dt h) k ((represents_iff _ _).mp h))

theorem muscl_ssprk3_run_bounds : BurgersE0bChallenge.MusclSSPRK3RunBounds := by
  intro dx dt m M a k hdx hdt hcfl hb
  exact Exec.run_musclSsprk3StepArray_bounds dx dt m M hdx hdt hcfl a hb k

theorem muscl_ssprk3_run_sum : BurgersE0bChallenge.MusclSSPRK3RunSum := by
  intro dx dt a k hdx
  exact Exec.run_musclSsprk3StepArray_sum dx dt hdx a k

theorem muscl_ssprk3_run_total_variation : BurgersE0bChallenge.MusclSSPRK3RunTotalVariation := by
  intro dx dt m M a k hdx hdt hcfl hb
  exact Exec.run_musclSsprk3StepArray_totalVariation_le dx dt m M hdx hdt hcfl a hb k

end CFDLean.Verification.BurgersE0bVerify
