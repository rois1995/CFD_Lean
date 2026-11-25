import CFDLean.Flux.Roe.Flux

noncomputable section
namespace CFDLean.MedianDual.RoeAggregation
open Coordinates PhysicalJacobian Roe Roe.Spectral
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] Spectral.shift Spectral.b Spectral.dp

def cold : StateCoordinates := ![1,0,0,0,1]
def hot : StateCoordinates := ![1,0,0,0,4]
def jump : StateCoordinates := ![0,0,0,0,3]

theorem states_admissible : (decode cold).Admissible 2 ∧ (decode hot).Admissible 2 := by
  norm_num [Conservative.Admissible, Conservative.pressure, decode, cold, hot, squareSum_three]

theorem averages : averageVelocity cold hot = 0 ∧ averageEnthalpy 2 cold hot = 5 ∧
    soundSpeed 2 cold hot = Real.sqrt 5 := by
  have hu : averageVelocity cold hot = 0 := by
    ext i
    fin_cases i <;> norm_num [averageVelocity, velocity, decode, cold, hot]
  have hh : averageEnthalpy 2 cold hot = 5 := by
    norm_num [averageEnthalpy, weight, root, enthalpy, pressure_formula, cold, hot]
  exact ⟨hu, hh, by norm_num [soundSpeed, soundSquare, hu, hh, squareSum_three]⟩

theorem dissipation_mass (n : Vector 3) (hn : dot n n = 1) :
    (Spectral.dissipation 2 cold hot n jump) 0 = 3 * Real.sqrt 5 / 5 := by
  have hc : Real.sqrt 5 ^ 2 = (2-1 : ℝ) * (5 - squareSum (0 : Vector 3) / 2) := by
    norm_num [Real.sq_sqrt, squareSum_three]
  have hm : (minus 2 0 5 n (Real.sqrt 5) jump) 0 = 3/10 := by
    rw [minus_apply _ _ _ _ _ hn hc]
    norm_num [Spectral.dp, Spectral.b, jump, acoustic, vb, vp, normalMomentum, projection, dot_three, squareSum_three, Real.sq_sqrt]
  have hp : (plus 2 0 5 n (Real.sqrt 5) jump) 0 = 3/10 := by
    rw [plus_apply _ _ _ _ _ hn hc]
    norm_num [Spectral.dp, Spectral.b, jump, acoustic, vb, vp, normalMomentum, projection, dot_three, squareSum_three, Real.sq_sqrt]
  unfold dissipation
  rw [averages.1, averages.2.1, averages.2.2]
  simp only [absolute, speed, offset, dot_three, Pi.zero_apply, zero_mul, zero_add,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, abs_neg, abs_of_nonneg (Real.sqrt_nonneg 5), abs_zero,
    zero_smul, add_zero, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, hp]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  rw [abs_of_nonneg (Real.sqrt_nonneg 5)]
  ring

theorem mass_formula (S : Vector 3) (hS : S ≠ 0) :
    roeFluxCoordinates 2 cold hot S 0 = -3 * Real.sqrt 5 * area S / 10 := by
  have hj : hot - cold = jump := by ext i; fin_cases i <;> norm_num [hot, cold, jump]
  rw [roeFluxCoordinates, ite_eq_right hS, hj]
  change (1/2 : ℝ) * (coordinateFlux 2 S cold 0 + coordinateFlux 2 S hot 0) -
    (area S / 2) * (dissipation 2 cold hot (unitNormal S) jump 0) = _
  rw [dissipation_mass _ (unitNormal_dot_self S hS)]
  norm_num [coordinateFlux, encode, physicalFlux, decode, cold, hot, dot_three]
  ring

/-- Two nonparallel unit facets give a different actual Roe transfer from their vector sum. -/
theorem nonparallel_not_additive :
    roeFluxCoordinates 2 cold hot (![1,1,0] : Vector 3) ≠
      roeFluxCoordinates 2 cold hot (![1,0,0] : Vector 3) +
      roeFluxCoordinates 2 cold hot (![0,1,0] : Vector 3) := by
  intro h
  have hs0 : (![1,1,0] : Vector 3) ≠ 0 := by intro hh; have := congrFun hh 0; norm_num at this
  have hs1 : (![1,0,0] : Vector 3) ≠ 0 := by intro hh; have := congrFun hh 0; norm_num at this
  have hs2 : (![0,1,0] : Vector 3) ≠ 0 := by intro hh; have := congrFun hh 1; norm_num at this
  have he := congrFun h 0
  change roeFluxCoordinates 2 cold hot (![1,1,0] : Vector 3) 0 =
    roeFluxCoordinates 2 cold hot (![1,0,0] : Vector 3) 0 + roeFluxCoordinates 2 cold hot (![0,1,0] : Vector 3) 0 at he
  rw [mass_formula _ hs0, mass_formula _ hs1, mass_formula _ hs2] at he
  norm_num [area, squareSum_three] at he
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : Real.sqrt 2 < 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  nlinarith

end CFDLean.MedianDual.RoeAggregation
