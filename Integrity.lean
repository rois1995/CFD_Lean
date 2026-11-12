import CFDLean

open CFDLean

-- These declarations require kernel proofs, including boundary cases.
example (γ : ℝ) (hγ : 1 < γ) : ∃ U : Conservative 3, U.Admissible γ :=
  admissible_exists γ hγ

example (γ : ℝ) (U : Conservative 3) :
    physicalFlux γ U (fun _ => 0) = ⟨0, fun _ => 0, 0⟩ := physicalFlux_zero γ U

-- A moving one-dimensional state checks energy density and area-vector conventions.
example : physicalFlux 2 (Conservative.mk 2 (fun _ : Fin 1 => 6) 14) (fun _ => 4) =
    ⟨24, fun _ => 92, 228⟩ := by
  norm_num [physicalFlux, dot, Conservative.pressure, squareSum]

-- Singular states remain outside the physical domain.
example (v : Vector 3) (p : ℝ) : ¬ (Primitive.mk 0 v p).Admissible := by
  simp [Primitive.Admissible]

example (U : Conservative 3) : U.pressure 1 = 0 := by
  simp [Conservative.pressure]

#print axioms squareSum_mul
#print axioms squareSum_div
#print axioms pressure_toConservative
#print axioms primitive_roundTrip
#print axioms conservative_roundTrip
#print axioms primitive_admissible_toConservative
#print axioms conservative_admissible_toPrimitive
#print axioms admissible_iff_internalEnergy_pos
#print axioms admissible_exists
#print axioms dot_add
#print axioms dot_mul
#print axioms physicalFlux_add
#print axioms physicalFlux_mul
#print axioms physicalFlux_reverse
#print axioms physicalFlux_zero
