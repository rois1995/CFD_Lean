import CFDLean.Verification.FV1DNonuniformChallenge
import CFDLean.Schemes.Burgers.NonuniformControls

/-! Bridge: the FVN implementation proves the trusted FVN statements for the scalar claims. -/
noncomputable section
namespace CFDLean.Verification.FV1DNonuniformVerify

open CFDLean.Periodic
open CFDLean.Burgers
open CFDLean.Scalar

/-- The mesh of the trusted statements: the grid of `next` and the positive widths `w`. -/
def mesh {I : Type*} (next : I ≃ I) (w : I → ℝ) (hw : ∀ i, 0 < w i) : Mesh1D I := ⟨⟨next⟩, w, hw⟩

/-- The trusted Burgers Rusanov flux is the implemented Burgers face. -/
theorem rusanov_eq : FV1DNonuniformChallenge.rusanov = Nonuniform.face :=
  Nonuniform.face_eq.symm

/-- The trusted left state is the implemented one. -/
theorem leftState_eq {I : Type*} (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (hw : ∀ i, 0 < w i) (u : I → ℝ)
    (i : I) :
    FV1DNonuniformChallenge.leftState φ next w u i = FV1D.Nonuniform.leftState (mesh next w hw) φ u i := rfl

/-- The trusted right state is the implemented one. -/
theorem rightState_eq {I : Type*} (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (hw : ∀ i, 0 < w i) (u : I → ℝ)
    (i : I) :
    FV1DNonuniformChallenge.rightState φ next w u i = FV1D.Nonuniform.rightState (mesh next w hw) φ u i := rfl

/-- The trusted first-order Burgers step is the implemented one. -/
theorem firstOrderStep_eq {I : Type*} (next : I ≃ I) (w : I → ℝ) (hw : ∀ i, 0 < w i) (dt : ℝ) :
    FV1DNonuniformChallenge.firstOrderStep FV1DNonuniformChallenge.rusanov next w dt =
      Nonuniform.firstOrderStep (mesh next w hw) dt := by
  rw [rusanov_eq]
  rfl

/-- The trusted MUSCL step with the flux `H` is the implemented scalar MUSCL step. -/
theorem musclStep_eq {I : Type*} (H φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (hw : ∀ i, 0 < w i) (dt : ℝ) :
    FV1DNonuniformChallenge.musclStep H φ next w dt = FV1D.Nonuniform.musclStep (mesh next w hw) H φ dt := rfl

/-- The trusted Burgers MUSCL step is the implemented one. -/
theorem burgersMusclStep_eq {I : Type*} (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (hw : ∀ i, 0 < w i)
    (dt : ℝ) :
    FV1DNonuniformChallenge.musclStep FV1DNonuniformChallenge.rusanov φ next w dt =
      Nonuniform.musclStep (mesh next w hw) dt φ := by
  rw [rusanov_eq]
  rfl

theorem first_order_bounds {I : Type*} : FV1DNonuniformChallenge.FirstOrderBounds I := by
  intro next w dt m M u hw hdt hu hcfl
  rw [firstOrderStep_eq next w hw dt]
  exact Nonuniform.firstOrderStep_mem (mesh next w hw) dt hdt m M u hu hcfl

theorem first_order_total_variation {I : Type*} [Fintype I] :
    FV1DNonuniformChallenge.FirstOrderTotalVariation I := by
  intro next w dt u hw hdt hcfl
  rw [firstOrderStep_eq next w hw dt]
  exact Nonuniform.firstOrderStep_totalVariation_le (mesh next w hw) dt hdt u hcfl

theorem reconstruction_bounds {I : Type*} : FV1DNonuniformChallenge.ReconstructionBounds I := by
  intro θ φ next w m M u hw hφ hr hu i
  rw [leftState_eq φ next w hw, rightState_eq φ next w hw]
  exact ⟨FV1D.Nonuniform.leftState_mem (mesh next w hw) φ θ hφ hr m M u hu i,
    FV1D.Nonuniform.rightState_mem (mesh next w hw) φ θ hφ hr m M u hu i⟩

theorem muscl_bounds {I : Type*} : FV1DNonuniformChallenge.MusclBounds I := by
  intro H KL KR θ φ next w dt m M u hw hmono hlip hφ hr hdt hu hcfl
  rw [musclStep_eq H φ next w hw dt]
  exact FV1D.Nonuniform.musclStep_mem (mesh next w hw) φ θ hφ hr m M u hu ⟨H⟩ hmono KL KR hlip dt hdt hcfl

theorem muscl_total_variation {I : Type*} [Fintype I] : FV1DNonuniformChallenge.MusclTotalVariation I := by
  intro H KL KR θ φ next w dt m M u hw hmono hlip hφ hr hdt hu hcfl
  rw [musclStep_eq H φ next w hw dt]
  exact FV1D.Nonuniform.musclStep_totalVariation_le (mesh next w hw) φ θ hφ hr m M u hu ⟨H⟩ hmono KL KR hlip dt
    hdt hcfl

theorem muscl_euler_multi_step {I : Type*} [Fintype I] : FV1DNonuniformChallenge.MusclEulerMultiStep I := by
  intro θ φ next w dt u m M n hw hφ hr hdt hcfl hu
  simp only [burgersMusclStep_eq φ next w hw dt]
  exact Nonuniform.musclStep_iterate_stable (mesh next w hw) dt m M φ θ hφ hr hdt hcfl u hu n

theorem muscl_ssprk2_multi_step {I : Type*} [Fintype I] : FV1DNonuniformChallenge.MusclSSPRK2MultiStep I := by
  intro θ φ next w dt u m M n hw hφ hr hdt hcfl hu
  simp only [burgersMusclStep_eq φ next w hw dt]
  exact Nonuniform.musclSsprk2Step_iterate_stable (mesh next w hw) dt m M φ θ hφ hr hdt hcfl u hu n

theorem muscl_ssprk3_multi_step {I : Type*} [Fintype I] : FV1DNonuniformChallenge.MusclSSPRK3MultiStep I := by
  intro θ φ next w dt u m M n hw hφ hr hdt hcfl hu
  simp only [burgersMusclStep_eq φ next w hw dt]
  exact Nonuniform.musclSsprk3Step_iterate_stable (mesh next w hw) dt m M φ θ hφ hr hdt hcfl u hu n

/-! ### FVN-X

The trusted slope functions are the implemented ones: minmod and the central slope by definition, the other four
through their limiter factors. -/

theorem minmod_eq : FV1DNonuniformChallenge.minmod = FiniteVolume.minmod := rfl

theorem centralSlope_eq : FV1DNonuniformChallenge.centralSlope = FiniteVolume.centralSlope := rfl

theorem mc_eq : FV1DNonuniformChallenge.mc = FiniteVolume.limitedSlope FiniteVolume.mcFactor :=
  funext fun a => funext fun b => (FiniteVolume.limitedSlope_mcFactor a b).symm

theorem superbee_eq : FV1DNonuniformChallenge.superbee = FiniteVolume.limitedSlope FiniteVolume.superbeeFactor :=
  funext fun a => funext fun b => (FiniteVolume.limitedSlope_superbeeFactor a b).symm

theorem vanLeer_eq : FV1DNonuniformChallenge.vanLeer = FiniteVolume.limitedSlope FiniteVolume.vanLeerFactor :=
  funext fun a => funext fun b => (FiniteVolume.limitedSlope_vanLeerFactor a b).symm

theorem vanAlbada_eq : FV1DNonuniformChallenge.vanAlbada = FiniteVolume.limitedSlope FiniteVolume.vanAlbadaFactor :=
  funext fun a => funext fun b => (FiniteVolume.limitedSlope_vanAlbadaFactor a b).symm

/-- The trusted FVN-X left state at face 1 is the left state of the implemented control mesh `fvnMesh` and state
`fvnState`. -/
theorem leftState_fvnMesh (φ : ℝ → ℝ → ℝ) :
    FV1DNonuniformChallenge.leftState φ (Equiv.addRight (1 : ZMod 4)) FV1DNonuniformChallenge.widthData
      FV1DNonuniformChallenge.stateData 1 = FV1D.Nonuniform.leftState Nonuniform.fvnMesh φ Nonuniform.fvnState 1 :=
  rfl

/-- The trusted FVN-X backward difference of cell 1 is the implemented one on `fvnMesh` and `fvnState`. -/
theorem backDiff_fvnMesh :
    FV1DNonuniformChallenge.backDiff (Equiv.addRight (1 : ZMod 4)) FV1DNonuniformChallenge.widthData
      FV1DNonuniformChallenge.stateData 1 = FV1D.Nonuniform.backDiff Nonuniform.fvnMesh Nonuniform.fvnState 1 :=
  rfl

/-- The trusted FVN-X forward difference of cell 1 is the implemented one on `fvnMesh` and `fvnState`. -/
theorem fwdDiff_fvnMesh :
    FV1DNonuniformChallenge.fwdDiff (Equiv.addRight (1 : ZMod 4)) FV1DNonuniformChallenge.widthData
      FV1DNonuniformChallenge.stateData 1 = FV1D.Nonuniform.fwdDiff Nonuniform.fvnMesh Nonuniform.fvnState 1 :=
  rfl

theorem mesh_ratio_overshoot : FV1DNonuniformChallenge.MeshRatioOvershoot := by
  obtain ⟨hu, hr, hr2, hb, hf, hmm, hva, hvl, hmc, hsb, hc⟩ := Nonuniform.meshRatio_needed
  refine ⟨hu, hr, hr2, backDiff_fvnMesh.trans hb, fwdDiff_fvnMesh.trans hf, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [leftState_fvnMesh]
  · rw [minmod_eq]; exact hmm
  · rw [vanAlbada_eq]; exact hva
  · rw [vanLeer_eq]; exact hvl
  · rw [mc_eq]; exact hmc
  · rw [superbee_eq]; exact hsb
  · rw [centralSlope_eq]; exact hc

end CFDLean.Verification.FV1DNonuniformVerify
