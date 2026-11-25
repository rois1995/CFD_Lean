import CFDLean.Verification.BurgersE0Challenge
import CFDLean.Exec.Refinement

/-! Bridge: the E0 refinement theorems prove the trusted E0 statements. -/
noncomputable section
namespace CFDLean.Verification.BurgersE0Verify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Periodic

/-- The trusted representation relation is the implemented one. -/
theorem represents_iff {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) :
    BurgersE0Challenge.Represents a u ↔ Exec.Represents a u :=
  ⟨fun h => ⟨h.1, fun i => h.2 i (h.1 ▸ i.isLt)⟩, fun ⟨hs, h⟩ => ⟨hs, fun i _ => h i⟩⟩

/-- The trusted Euler step on `Fin n` is the Rusanov Euler map on `finGrid n`. -/
theorem eulerStep_eq {n : ℕ} [NeZero n] (dx dt : ℝ) :
    BurgersE0Challenge.eulerStep (n := n) dx dt = Rusanov.eulerStep (Exec.finGrid n) dx dt := by
  funext u i
  simp [BurgersE0Challenge.eulerStep, BurgersE0Challenge.rusanov, BurgersE0Challenge.burgersFlux,
    BurgersE0Challenge.rusanovWaveSpeed, Rusanov.eulerStep, Time.ForwardEuler.step, Scalar.FiniteVolume.rhs,
    Scalar.FiniteVolume.interfaceFlux, Rusanov.numericalFlux, Rusanov.eval, Rusanov.waveSpeed, physicalFlux,
    Exec.finGrid, Grid.prev, sub_eq_add_neg]

theorem real_scalar_is_standard : BurgersE0Challenge.RealScalarIsStandard :=
  fun x y => Exec.instScalarReal_standard x y

theorem kernel_flux_is_rusanov : BurgersE0Challenge.KernelFluxIsRusanov :=
  fun uL uR => Exec.rusanov_eq uL uR

theorem euler_step_refines : BurgersE0Challenge.EulerStepRefines := by
  intro n _ dx dt a u h
  rw [eulerStep_eq]
  exact (represents_iff _ _).mpr (Exec.eulerStepArray_refines dx dt ((represents_iff _ _).mp h))

theorem ssprk3_step_refines : BurgersE0Challenge.SSPRK3StepRefines := by
  intro n _ dx dt a u h
  rw [eulerStep_eq]
  exact (represents_iff _ _).mpr (Exec.ssprk3StepArray_refines dx dt ((represents_iff _ _).mp h))

theorem ssprk3_run_refines : BurgersE0Challenge.SSPRK3RunRefines := by
  intro n _ dx dt a u k h
  rw [eulerStep_eq]
  exact (represents_iff _ _).mpr
    (Exec.run_refines (fun _ _ h => Exec.ssprk3StepArray_refines dx dt h) k ((represents_iff _ _).mp h))

theorem sum_diagnostic : BurgersE0Challenge.SumDiagnostic := by
  intro n a u h
  exact Exec.sumArray_eq ((represents_iff _ _).mp h)

theorem total_variation_diagnostic : BurgersE0Challenge.TotalVariationDiagnostic := by
  intro n _ a u h
  rw [Exec.totalVariationArray_eq ((represents_iff _ _).mp h)]
  simp [Scalar.FiniteVolume.totalVariation, Exec.finGrid]

theorem ssprk3_run_bounds : BurgersE0Challenge.SSPRK3RunBounds := by
  intro dx dt m M a k hdx hdt hcfl hb
  exact Exec.run_ssprk3StepArray_bounds dx dt m M hdx hdt hcfl a hb k

theorem ssprk3_run_sum : BurgersE0Challenge.SSPRK3RunSum := by
  intro dx dt a k hdx
  exact Exec.run_ssprk3StepArray_sum dx dt hdx a k

theorem ssprk3_run_total_variation : BurgersE0Challenge.SSPRK3RunTotalVariation := by
  intro dx dt m M a k hdx hdt hcfl hb
  exact Exec.run_ssprk3StepArray_totalVariation_le dx dt m M hdx hdt hcfl a hb k

end CFDLean.Verification.BurgersE0Verify
