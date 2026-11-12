import CFDLean

open CFDLean

-- These declarations require kernel proofs, including boundary cases.
theorem ReviewerCopy.domainInThreeDimensions (γ : ℝ) (hγ : 1 < γ) : ∃ U : Conservative 3, U.Admissible γ :=
  admissible_exists γ hγ

theorem ReviewerCopy.zeroArea (γ : ℝ) (U : Conservative 3) :
    physicalFlux γ U (fun _ => 0) = ⟨0, fun _ => 0, 0⟩ := physicalFlux_zero γ U

-- A moving one-dimensional state checks energy density and area-vector conventions.
theorem ReviewerCopy.moving1D : physicalFlux 2 (Conservative.mk 2 (fun _ : Fin 1 => 6) 14) (fun _ => 4) =
    ⟨24, fun _ => 92, 228⟩ := by
  norm_num [physicalFlux, dot, Conservative.pressure, squareSum]

-- Singular states remain outside the physical domain.
theorem ReviewerCopy.zeroPrimitiveDensity (v : Vector 3) (p : ℝ) : ¬ (Primitive.mk 0 v p).Admissible := by
  simp [Primitive.Admissible]

theorem ReviewerCopy.pressureGammaOne (U : Conservative 3) : U.pressure 1 = 0 := by
  simp [Conservative.pressure]

#print axioms ReviewerCopy.domainInThreeDimensions
#print axioms ReviewerCopy.zeroArea
#print axioms ReviewerCopy.moving1D
#print axioms ReviewerCopy.zeroPrimitiveDensity
#print axioms ReviewerCopy.pressureGammaOne
