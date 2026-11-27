import CFDLean.Verification.FV1DNonuniformArrayChallenge
import CFDLean.Exec.NonuniformTransfer

/-! Bridge: the FVNA refinement and transfer theorems prove the trusted FVNA statements (FVNA-M and FVNA-T). -/
noncomputable section
namespace CFDLean.Verification.FV1DNonuniformArrayVerify

open CFDLean.Periodic
open CFDLean.Burgers
open CFDLean.Exec (Limiter widthAt widthAt_of_lt meshOf meshOf_grid meshOf_width)
open CFDLean.Exec.FV1D (samples samples_size samples_getElem)

/-! ### Definitions of the trusted statements and their implementations -/

/-- The trusted classical slope function of a limiter is the implemented slope function. -/
theorem slopeOf_eq (L : Limiter) : FV1DNonuniformArrayChallenge.slopeOf L = L.slopeFn := by
  funext a b
  cases L
  · rfl
  · exact (congrFun (congrFun Scalar.FiniteVolume.limitedSlope_minmodFactor a) b).symm
  · exact (Scalar.FiniteVolume.limitedSlope_mcFactor a b).symm
  · exact (Scalar.FiniteVolume.limitedSlope_superbeeFactor a b).symm
  · exact (Scalar.FiniteVolume.limitedSlope_vanLeerFactor a b).symm
  · exact (Scalar.FiniteVolume.limitedSlope_vanAlbadaFactor a b).symm

/-- The trusted bound constant of a limiter is the implemented one. -/
theorem thetaOf_eq (L : Limiter) : FV1DNonuniformArrayChallenge.thetaOf L = L.theta := by
  cases L <;> rfl

/-- The trusted Burgers Rusanov flux is the implemented Burgers face. -/
theorem rusanov_eq : FV1DNonuniformArrayChallenge.rusanov = Nonuniform.face :=
  Nonuniform.face_eq.symm

section Periodic

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- A stored field represents its cell function. -/
theorem represents_samples (u : ZMod n → ℝ) : FV1DNonuniformArrayChallenge.Represents (samples u) u :=
  ⟨samples_size u, fun i hi => samples_getElem u i hi⟩

omit [NeZero n] in
/-- An array that represents `u` is the stored field of `u`. -/
theorem eq_samples {a : Array ℝ} {u : ZMod n → ℝ} (h : FV1DNonuniformArrayChallenge.Represents a u) :
    a = samples u := by
  apply Array.ext (by rw [samples_size, h.1])
  intro i hi _
  rw [h.2 i hi, samples_getElem]

omit [NeZero n] in
/-- The entries of a width array that represents positive widths are positive. -/
theorem pos_of_represents {widths : Array ℝ} {w : ZMod n → ℝ} (h : FV1DNonuniformArrayChallenge.Represents widths w)
    (hw : ∀ j, 0 < w j) : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i] := fun i hi => by
  rw [h.2 i hi]
  exact hw _

/-- The mesh of a width array that represents `w` has the widths `w`. -/
theorem meshOf_width_eq {widths : Array ℝ} {w : ZMod n → ℝ} (h : FV1DNonuniformArrayChallenge.Represents widths w)
    (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) : (meshOf widths h.1 hpos).width = w := by
  funext j
  rw [meshOf_width, h.2, ZMod.natCast_zmod_val]

/-- The trusted MUSCL step on the widths of a mesh over `zmodGrid n` is the implemented Burgers MUSCL step. -/
theorem musclStep_eq (m : Mesh1D (ZMod n)) (hg : m.grid = zmodGrid n) (φ : ℝ → ℝ → ℝ) (dt : ℝ) :
    Nonuniform.musclStep m dt φ = FV1DNonuniformArrayChallenge.musclStep φ m.width dt := by
  obtain ⟨g, w, hw⟩ := m
  dsimp only at hg ⊢
  subst hg
  have hn : ∀ j : ZMod n, (zmodGrid n).next j = j + 1 := fun _ => rfl
  have hp : ∀ j : ZMod n, (zmodGrid n).prev j = j - 1 := fun _ => by
    simp [zmodGrid, Grid.prev, sub_eq_add_neg]
  funext u j
  simp only [Nonuniform.musclStep, FV1D.Nonuniform.musclStep, FV1D.Nonuniform.update, FV1D.Nonuniform.leftState,
    FV1D.Nonuniform.rightState, FV1D.Nonuniform.slope, FV1D.Nonuniform.backDiff, FV1D.Nonuniform.fwdDiff,
    Mesh1D.spacing, hn, hp, smul_eq_mul, ← rusanov_eq, FV1DNonuniformArrayChallenge.musclStep,
    FV1DNonuniformArrayChallenge.leftState, FV1DNonuniformArrayChallenge.rightState,
    FV1DNonuniformArrayChallenge.slope, FV1DNonuniformArrayChallenge.backDiff, FV1DNonuniformArrayChallenge.fwdDiff,
    FV1DNonuniformArrayChallenge.spacing]

/-- The trusted SSPRK2 combination of the trusted MUSCL step is the implemented Burgers MUSCL SSPRK2 step. -/
theorem musclSsprk2Step_eq (m : Mesh1D (ZMod n)) (hg : m.grid = zmodGrid n) (φ : ℝ → ℝ → ℝ) (dt : ℝ) :
    Nonuniform.musclSsprk2Step m dt φ =
      FV1DNonuniformArrayChallenge.ssprk2 (FV1DNonuniformArrayChallenge.musclStep φ m.width dt) := by
  rw [Nonuniform.musclSsprk2Step, musclStep_eq m hg]
  rfl

/-- The trusted SSPRK3 combination of the trusted MUSCL step is the implemented Burgers MUSCL SSPRK3 step. -/
theorem musclSsprk3Step_eq (m : Mesh1D (ZMod n)) (hg : m.grid = zmodGrid n) (φ : ℝ → ℝ → ℝ) (dt : ℝ) :
    Nonuniform.musclSsprk3Step m dt φ =
      FV1DNonuniformArrayChallenge.ssprk3 (FV1DNonuniformArrayChallenge.musclStep φ m.width dt) := by
  rw [Nonuniform.musclSsprk3Step, musclStep_eq m hg]
  rfl

end Periodic

/-! ### FVNA-M -/

theorem muscl_euler_step_refines : FV1DNonuniformArrayChallenge.MusclEulerStepRefines := by
  intro L n _ dt widths a w u hwid hw hu
  have hpos := pos_of_represents hwid hw
  rw [Exec.nuLimiterEulerStepArray_refines L widths hwid.1 hpos u dt a (eq_samples hu),
    musclStep_eq _ (meshOf_grid widths hwid.1 hpos), meshOf_width_eq hwid hpos, slopeOf_eq]
  exact represents_samples _

theorem muscl_ssprk2_step_refines : FV1DNonuniformArrayChallenge.MusclSSPRK2StepRefines := by
  intro L n _ dt widths a w u hwid hw hu
  have hpos := pos_of_represents hwid hw
  rw [Exec.nuLimiterSsprk2StepArray_refines L widths hwid.1 hpos u dt a (eq_samples hu),
    musclSsprk2Step_eq _ (meshOf_grid widths hwid.1 hpos), meshOf_width_eq hwid hpos, slopeOf_eq]
  exact represents_samples _

theorem muscl_ssprk3_step_refines : FV1DNonuniformArrayChallenge.MusclSSPRK3StepRefines := by
  intro L n _ dt widths a w u hwid hw hu
  have hpos := pos_of_represents hwid hw
  rw [Exec.nuLimiterSsprk3StepArray_refines L widths hwid.1 hpos u dt a (eq_samples hu),
    musclSsprk3Step_eq _ (meshOf_grid widths hwid.1 hpos), meshOf_width_eq hwid hpos, slopeOf_eq]
  exact represents_samples _

/-! ### FVNA-T (a) -/

theorem first_order_weighted_sum : FV1DNonuniformArrayChallenge.FirstOrderWeightedSum := by
  intro n _ dt widths u hw hu hpos
  exact Exec.burgers_nonuniformStepArray_weighted_sum widths hw hpos dt u hu

theorem muscl_euler_weighted_sum : FV1DNonuniformArrayChallenge.MusclEulerWeightedSum := by
  intro L n _ dt widths u hw hu hpos
  exact Exec.nuLimiterEulerStepArray_weighted_sum widths hw hpos L dt u hu

theorem muscl_ssprk2_weighted_sum : FV1DNonuniformArrayChallenge.MusclSSPRK2WeightedSum := by
  intro L n _ dt widths u hw hu hpos
  exact Exec.nuLimiterSsprk2StepArray_weighted_sum widths hw hpos L dt u hu

theorem muscl_ssprk3_weighted_sum : FV1DNonuniformArrayChallenge.MusclSSPRK3WeightedSum := by
  intro L n _ dt widths u hw hu hpos
  exact Exec.nuLimiterSsprk3StepArray_weighted_sum widths hw hpos L dt u hu

theorem euler_first_order_weighted_sum : FV1DNonuniformArrayChallenge.EulerFirstOrderWeightedSum := by
  intro n _ γ dt widths U hw hU hpos k
  exact Exec.euler_nonuniformStepArray_weighted_sum widths hw hpos γ dt U hU k

/-! ### FVNA-T (b)

The trusted conditions read the widths as `widths[i]`; the kernel reads them with `widthAt`, equal in range. -/

theorem first_order_bounds : FV1DNonuniformArrayChallenge.FirstOrderBounds := by
  intro n _ dt m M widths u hw hu hpos hdt hb hcfl
  refine Exec.burgers_nonuniformStepArray_bounds widths hw hpos dt m M hdt u hu hb fun i => ?_
  rw [widthAt_of_lt widths (by omega)]
  exact hcfl i

theorem first_order_total_variation : FV1DNonuniformArrayChallenge.FirstOrderTotalVariation := by
  intro n _ dt widths u hw hu hpos hdt hcfl
  refine Exec.burgers_nonuniformStepArray_totalVariation_le widths hw hpos dt hdt u hu fun i => ?_
  rw [widthAt_of_lt widths (by omega), widthAt_of_lt widths (by omega)]
  exact hcfl i

/-! ### FVNA-T (c)

The trusted mesh ratio of the width array is the mesh ratio of `meshOf widths` (`Exec.meshOf_meshRatio_iff`). -/

theorem muscl_euler_run_stable : FV1DNonuniformArrayChallenge.MusclEulerRunStable := by
  intro L n _ dt m M widths u k hw hu hpos hL hr hdt hb hcfl
  rw [thetaOf_eq] at hr
  exact Exec.run_nuLimiterEulerStepArray_stable L hL widths hw hpos
    ((Exec.meshOf_meshRatio_iff widths hw hpos L.theta).mpr hr) dt m M hdt hcfl u hu hb k

theorem muscl_ssprk2_run_stable : FV1DNonuniformArrayChallenge.MusclSSPRK2RunStable := by
  intro L n _ dt m M widths u k hw hu hpos hL hr hdt hb hcfl
  rw [thetaOf_eq] at hr
  exact Exec.run_nuLimiterSsprk2StepArray_stable L hL widths hw hpos
    ((Exec.meshOf_meshRatio_iff widths hw hpos L.theta).mpr hr) dt m M hdt hcfl u hu hb k

theorem muscl_ssprk3_run_stable : FV1DNonuniformArrayChallenge.MusclSSPRK3RunStable := by
  intro L n _ dt m M widths u k hw hu hpos hL hr hdt hb hcfl
  rw [thetaOf_eq] at hr
  exact Exec.run_nuLimiterSsprk3StepArray_stable L hL widths hw hpos
    ((Exec.meshOf_meshRatio_iff widths hw hpos L.theta).mpr hr) dt m M hdt hcfl u hu hb k

end CFDLean.Verification.FV1DNonuniformArrayVerify
