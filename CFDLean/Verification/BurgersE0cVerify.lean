import CFDLean.Verification.BurgersE0cChallenge
import CFDLean.Exec.LimiterRefinement

/-! Bridge: the E0c refinement theorems prove the trusted E0c statements. -/
noncomputable section
namespace CFDLean.Verification.BurgersE0cVerify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Periodic
open CFDLean.Exec (Limiter)

/-- The trusted representation relation is the implemented one. -/
theorem represents_iff {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) :
    BurgersE0cChallenge.Represents a u ↔ Exec.Represents a u :=
  ⟨fun h => ⟨h.1, fun i => h.2 i (h.1 ▸ i.isLt)⟩, fun ⟨hs, h⟩ => ⟨hs, fun i _ => h i⟩⟩

/-- The trusted classical slope function of a limiter is the implemented slope function. -/
theorem slopeOf_eq (L : Limiter) : BurgersE0cChallenge.slopeOf L = L.slopeFn := by
  funext a b
  cases L
  · rfl
  · exact (congrFun (congrFun Scalar.FiniteVolume.limitedSlope_minmodFactor a) b).symm
  · exact (Scalar.FiniteVolume.limitedSlope_mcFactor a b).symm
  · exact (Scalar.FiniteVolume.limitedSlope_superbeeFactor a b).symm
  · exact (Scalar.FiniteVolume.limitedSlope_vanLeerFactor a b).symm
  · exact (Scalar.FiniteVolume.limitedSlope_vanAlbadaFactor a b).symm

theorem thetaOf_eq (L : Limiter) : BurgersE0cChallenge.thetaOf L = L.theta := by
  cases L <;> rfl

/-- The trusted MUSCL Euler step on `Fin n` is the MUSCL-Rusanov Euler map on `finGrid n`, for every slope function. -/
theorem musclEulerStep_eq {n : ℕ} [NeZero n] (φ : ℝ → ℝ → ℝ) (dx dt : ℝ) :
    BurgersE0cChallenge.musclEulerStep (n := n) φ dx dt = Rusanov.musclEulerStep (Exec.finGrid n) dx dt φ := by
  funext u i
  simp [BurgersE0cChallenge.musclEulerStep, BurgersE0cChallenge.facePlus, BurgersE0cChallenge.faceMinus,
    BurgersE0cChallenge.slope, BurgersE0cChallenge.rusanov, BurgersE0cChallenge.burgersFlux,
    BurgersE0cChallenge.rusanovWaveSpeed, Rusanov.musclEulerStep, Time.ForwardEuler.step,
    Scalar.FiniteVolume.musclRhs, Scalar.FiniteVolume.musclFlux, Scalar.FiniteVolume.leftState,
    Scalar.FiniteVolume.rightState, Scalar.FiniteVolume.slope, Rusanov.numericalFlux, Rusanov.eval,
    Rusanov.waveSpeed, physicalFlux, Exec.finGrid, Grid.prev, sub_eq_add_neg]

theorem real_sign_is_standard : BurgersE0cChallenge.RealSignIsStandard := by
  intro x
  rw [Exec.isPos_eq]
  exact decide_eq_true_iff

theorem kernel_slope_is_limiter : BurgersE0cChallenge.KernelSlopeIsLimiter := by
  intro L a b
  rw [slopeOf_eq]
  exact Exec.limiterSlope_eq L a b

theorem limiter_euler_step_refines : BurgersE0cChallenge.LimiterEulerStepRefines := by
  intro L n _ dx dt a u h
  rw [slopeOf_eq, musclEulerStep_eq]
  exact (represents_iff _ _).mpr (Exec.limiterEulerStepArray_refines L dx dt ((represents_iff _ _).mp h))

theorem limiter_ssprk3_step_refines : BurgersE0cChallenge.LimiterSSPRK3StepRefines := by
  intro L n _ dx dt a u h
  rw [slopeOf_eq, musclEulerStep_eq]
  exact (represents_iff _ _).mpr (Exec.limiterSsprk3StepArray_refines L dx dt ((represents_iff _ _).mp h))

theorem limiter_ssprk3_run_refines : BurgersE0cChallenge.LimiterSSPRK3RunRefines := by
  intro L n _ dx dt a u k h
  rw [slopeOf_eq, musclEulerStep_eq]
  exact (represents_iff _ _).mpr
    (Exec.run_refines (fun _ _ h => Exec.limiterSsprk3StepArray_refines L dx dt h) k ((represents_iff _ _).mp h))

theorem limiter_ssprk3_run_sum : BurgersE0cChallenge.LimiterSSPRK3RunSum := by
  intro L dx dt a k hdx
  exact Exec.run_limiterSsprk3StepArray_sum L dx dt hdx a k

theorem limiter_ssprk3_run_bounds : BurgersE0cChallenge.LimiterSSPRK3RunBounds := by
  intro L dx dt m M a k hL hdx hdt hcfl hb
  rw [thetaOf_eq] at hcfl
  exact Exec.run_limiterSsprk3StepArray_bounds L hL dx dt m M hdx hdt hcfl a hb k

theorem limiter_ssprk3_run_total_variation : BurgersE0cChallenge.LimiterSSPRK3RunTotalVariation := by
  intro L dx dt m M a k hL hdx hdt hcfl hb
  rw [thetaOf_eq] at hcfl
  exact Exec.run_limiterSsprk3StepArray_totalVariation_le L hL dx dt m M hdx hdt hcfl a hb k

end CFDLean.Verification.BurgersE0cVerify
