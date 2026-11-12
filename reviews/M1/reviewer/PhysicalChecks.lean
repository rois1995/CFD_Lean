import CFDLean

open CFDLean
open scoped BigOperators

namespace ReviewerM1

/-- Independent primitive-variable expression for the normal contraction of the Euler flux. -/
theorem primitiveFlux {d : ℕ} (γ : ℝ) (W : Primitive d) (S : Vector d)
    (hγ : γ ≠ 1) (hρ : W.density ≠ 0) :
    physicalFlux γ (W.toConservative γ) S =
      ⟨W.density * dot W.velocity S,
       fun i => (W.density * W.velocity i) * dot W.velocity S + W.pressure * S i,
       (W.pressure / (γ - 1) + W.density * squareSum W.velocity / 2 + W.pressure) *
         dot W.velocity S⟩ := by
  have hm : dot (W.toConservative γ).momentum S = W.density * dot W.velocity S := by
    simp only [dot, Primitive.toConservative, Finset.mul_sum, mul_assoc]
  have hq : dot (W.toConservative γ).momentum S / (W.toConservative γ).density =
      dot W.velocity S := by
    change dot (W.toConservative γ).momentum S / W.density = _
    rw [hm, mul_div_cancel_left₀ _ hρ]
  unfold physicalFlux
  rw [hq, hm, pressure_toConservative γ W hγ hρ]
  rfl

theorem conservativeZeroDensity {d : ℕ} (γ E : ℝ) (m : Vector d) :
    ¬ (Conservative.mk 0 m E).Admissible γ := by
  simp [Conservative.Admissible]

theorem gammaOne {d : ℕ} (U : Conservative d) : ¬ U.Admissible 1 := by
  simp [Conservative.Admissible, Conservative.pressure]

theorem belowOneExample :
    (Conservative.mk 1 (fun _ : Fin 1 => 0) (-1)).Admissible 0 := by
  norm_num [Conservative.Admissible, Conservative.pressure, squareSum]

#print axioms primitiveFlux
#print axioms conservativeZeroDensity
#print axioms gammaOne
#print axioms belowOneExample
end ReviewerM1
