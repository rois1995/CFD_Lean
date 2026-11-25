import CFDLean.Verification.BurgersB4Challenge
import CFDLean.Entropy.Scalar.Burgers

/-! Bridge: the B4 implementation proves the trusted B4 statements. -/
noncomputable section
namespace CFDLean.Verification.BurgersB4Verify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Scalar
open CFDLean.Periodic

/-- The trusted right-hand side is the implemented one on the grid of `next`. -/
theorem rhs_eq {I : Type*} (next : I ≃ I) (dx : ℝ) (F : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) :
    BurgersB4Challenge.rhs next dx F u i = FiniteVolume.rhs ⟨next⟩ dx ⟨F⟩ u i := by
  simp [BurgersB4Challenge.rhs, FiniteVolume.rhs, FiniteVolume.interfaceFlux, Grid.prev]

/-- The trusted numerical entropy flux is the implemented one. -/
theorem entropyFlux_eq {I : Type*} (next : I ≃ I) (v ψ : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) :
    BurgersB4Challenge.entropyFlux next v ψ F u i = FiniteVolume.entropyFlux ⟨next⟩ v ψ ⟨F⟩ u i :=
  rfl

/-- The trusted Rusanov flux is the implemented one. -/
theorem rusanov_eq : BurgersB4Challenge.rusanov = Rusanov.numericalFlux.eval := rfl

theorem entropy_conservative_flux_properties : BurgersB4Challenge.EntropyConservativeFluxProperties :=
  ⟨fun u => EntropyConservativeFlux.consistent u, fun a b => EntropyConservativeFlux.entropyConservative a b⟩

theorem rusanov_entropy_stable : BurgersB4Challenge.RusanovEntropyStable :=
  fun a b => Rusanov.entropyStable a b

theorem cell_entropy_inequality {I : Type*} : BurgersB4Challenge.CellEntropyInequality I := by
  intro next dx v ψ F u i hdx h
  rw [rhs_eq, entropyFlux_eq, entropyFlux_eq]
  exact FiniteVolume.cell_entropy_inequality ⟨next⟩ dx hdx v ψ ⟨F⟩ h u i

theorem entropy_production_nonpos {I : Type*} [Fintype I] : BurgersB4Challenge.EntropyProductionNonpos I := by
  intro next dx v ψ F u hdx h
  simp only [rhs_eq]
  exact FiniteVolume.entropy_production_nonpos ⟨next⟩ dx hdx v ψ ⟨F⟩ h u

theorem rusanov_energy_production {I : Type*} [Fintype I] : BurgersB4Challenge.RusanovEnergyProduction I := by
  intro next dx u hdx
  simp only [rhs_eq, rusanov_eq]
  exact Rusanov.energy_production_nonpos ⟨next⟩ dx hdx u

end CFDLean.Verification.BurgersB4Verify
