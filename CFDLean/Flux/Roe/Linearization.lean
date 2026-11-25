import CFDLean.Flux.Roe.Averages

noncomputable section
namespace CFDLean.Roe
open Coordinates PhysicalJacobian

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

def embed (i : Fin 5) : ℝ →L[ℝ] StateCoordinates :=
  ContinuousLinearMap.pi (fun j => if j = i then ContinuousLinearMap.id ℝ ℝ else 0)

def assemble (r : Fin 5 → (StateCoordinates →L[ℝ] ℝ)) :
    StateCoordinates →L[ℝ] StateCoordinates :=
  (embed 0).comp (r 0) + (embed 1).comp (r 1) + (embed 2).comp (r 2) +
    (embed 3).comp (r 3) + (embed 4).comp (r 4)

theorem assemble_eq_pi (r : Fin 5 → (StateCoordinates →L[ℝ] ℝ)) :
    assemble r = ContinuousLinearMap.pi r := by
  ext v i
  fin_cases i <;> simp [assemble, embed]

def operator (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) :
    StateCoordinates →L[ℝ] StateCoordinates :=
  let q := dot u n
  let b := normalMomentum n - q • projection 0
  let dp := (γ - 1) • (projection 4 -
    (u 0 • projection 1 + u 1 • projection 2 + u 2 • projection 3) +
    (squareSum u / 2) • projection 0)
  assemble ![normalMomentum n,
    q • projection 1 + u 0 • b + n 0 • dp,
    q • projection 2 + u 1 • b + n 1 • dp,
    q • projection 3 + u 2 • b + n 2 • dp,
    q • (projection 4 + dp) + H • b]

def roeMatrix (γ : ℝ) (x y : StateCoordinates) (n : Vector 3) :
    StateCoordinates →L[ℝ] StateCoordinates :=
  operator γ (averageVelocity x y) (averageEnthalpy γ x y) n

def parameter (γ : ℝ) (x : StateCoordinates) : StateCoordinates :=
  ![root x, root x * velocity x 0, root x * velocity x 1,
    root x * velocity x 2, root x * enthalpy γ x]

def midpoint (γ : ℝ) (x y : StateCoordinates) : StateCoordinates :=
  fun i => (parameter γ x i + parameter γ y i) / 2

def parameterState (γ : ℝ) (z : StateCoordinates) : StateCoordinates :=
  ![z 0 ^ 2, z 0 * z 1, z 0 * z 2, z 0 * z 3,
    (z 0 * z 4 + (γ - 1) / 2 * (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2)) / γ]

def parameterPressure (γ : ℝ) (z : StateCoordinates) : ℝ :=
  (γ - 1) / γ * (z 0 * z 4 - (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) / 2)

def parameterFlux (γ : ℝ) (n : Vector 3) (z : StateCoordinates) : StateCoordinates :=
  let q := normalMomentum n z
  ![z 0 * q, z 1 * q + parameterPressure γ z * n 0,
    z 2 * q + parameterPressure γ z * n 1,
    z 3 * q + parameterPressure γ z * n 2, z 4 * q]

def B (γ : ℝ) (z : StateCoordinates) : StateCoordinates →L[ℝ] StateCoordinates :=
  ContinuousLinearMap.pi ![(2 * z 0) • projection 0,
    z 1 • projection 0 + z 0 • projection 1,
    z 2 • projection 0 + z 0 • projection 2,
    z 3 • projection 0 + z 0 • projection 3,
    (1 / γ) • (z 4 • projection 0 + z 0 • projection 4 +
      (γ - 1) • (z 1 • projection 1 + z 2 • projection 2 + z 3 • projection 3))]

def pressureGradient (γ : ℝ) (z : StateCoordinates) : StateCoordinates →L[ℝ] ℝ :=
  ((γ - 1) / γ) • (z 4 • projection 0 + z 0 • projection 4 -
    (z 1 • projection 1 + z 2 • projection 2 + z 3 • projection 3))

def C (γ : ℝ) (n : Vector 3) (z : StateCoordinates) : StateCoordinates →L[ℝ] StateCoordinates :=
  let q := normalMomentum n z
  let dp := pressureGradient γ z
  ContinuousLinearMap.pi ![q • projection 0 + z 0 • normalMomentum n,
    q • projection 1 + z 1 • normalMomentum n + n 0 • dp,
    q • projection 2 + z 2 • normalMomentum n + n 1 • dp,
    q • projection 3 + z 3 • normalMomentum n + n 2 • dp,
    q • projection 4 + z 4 • normalMomentum n]

def inverseB (γ : ℝ) (z : StateCoordinates) : StateCoordinates →L[ℝ] StateCoordinates :=
  let d0 := (1 / (2 * z 0)) • projection 0
  let d1 := (1 / z 0) • (projection 1 - z 1 • d0)
  let d2 := (1 / z 0) • (projection 2 - z 2 • d0)
  let d3 := (1 / z 0) • (projection 3 - z 3 • d0)
  let d4 := (1 / z 0) • (γ • projection 4 - z 4 • d0 -
    (γ - 1) • (z 1 • d1 + z 2 • d2 + z 3 • d3))
  ContinuousLinearMap.pi ![d0, d1, d2, d3, d4]

theorem operator_physical (γ : ℝ) (x : StateCoordinates) (n : Vector 3) :
    operator γ (velocity x) (enthalpy γ x) n = jacobian γ x n := by
  unfold operator
  rw [assemble_eq_pi]
  rfl

theorem parameter_state (γ : ℝ) (x : StateCoordinates) (hγ : γ ≠ 0) (hx : 0 < x 0) :
    parameterState γ (parameter γ x) = x := by
  have hr := root_sq x (le_of_lt hx)
  have hr0 := ne_of_gt (root_pos x hx)
  funext i
  fin_cases i <;>
    simp [parameterState, parameter, velocity, enthalpy, pressure_formula, decode]
  all_goals rw [← hr]
  all_goals field_simp [hγ, hr0]
  ring1

theorem parameter_flux (γ : ℝ) (n : Vector 3) (x : StateCoordinates)
    (hγ : γ ≠ 0) (hx : 0 < x 0) :
    parameterFlux γ n (parameter γ x) = coordinateFlux γ n x := by
  have hr := root_sq x (le_of_lt hx)
  have hr0 := ne_of_gt (root_pos x hx)
  funext i
  fin_cases i <;>
    simp [parameterFlux, parameterPressure, parameter, coordinateFlux, physicalFlux, encode,
      normalMomentum, projection, velocity, enthalpy, coordinatePressure,
      Conservative.pressure, decode, squareSum_three, dot_three]
  all_goals rw [← hr]
  all_goals field_simp [hγ, hr0]
  all_goals ring1

theorem state_midpoint_jump (γ : ℝ) (z t : StateCoordinates) :
    parameterState γ t - parameterState γ z = B γ (fun i => (z i + t i) / 2) (t - z) := by
  funext i
  fin_cases i <;> simp [parameterState, B, projection, div_eq_mul_inv] <;> ring1

theorem flux_midpoint_jump (γ : ℝ) (n : Vector 3) (z t : StateCoordinates) :
    parameterFlux γ n t - parameterFlux γ n z = C γ n (fun i => (z i + t i) / 2) (t - z) := by
  funext i
  fin_cases i <;> simp [parameterFlux, parameterPressure, C, pressureGradient, normalMomentum, projection,
    div_eq_mul_inv] <;> ring1

theorem inverseB_B (γ : ℝ) (z : StateCoordinates) (hγ : γ ≠ 0) (hz : z 0 ≠ 0)
    (v : StateCoordinates) : inverseB γ z (B γ z v) = v := by
  funext i
  fin_cases i <;> simp [inverseB, B, projection]
  all_goals field_simp [hγ, hz]
  all_goals ring1

theorem B_inverseB (γ : ℝ) (z : StateCoordinates) (hγ : γ ≠ 0) (hz : z 0 ≠ 0)
    (v : StateCoordinates) : B γ z (inverseB γ z v) = v := by
  funext i
  fin_cases i <;> simp [inverseB, B, projection]
  all_goals field_simp [hγ, hz]
  all_goals ring1

theorem B_bijective (γ : ℝ) (z : StateCoordinates) (hγ : γ ≠ 0) (hz : z 0 ≠ 0) :
    Function.Bijective (B γ z) := by
  constructor
  · intro a b hab
    rw [← inverseB_B γ z hγ hz a, ← inverseB_B γ z hγ hz b, hab]
  · intro v
    exact ⟨inverseB γ z v, B_inverseB γ z hγ hz v⟩

theorem midpoint_pos (γ : ℝ) (x y : StateCoordinates) (hx : 0 < x 0) (hy : 0 < y 0) :
    0 < midpoint γ x y 0 := by
  change 0 < (root x + root y) / 2
  exact div_pos (root_sum_pos x y hx hy) (by norm_num)

open Fin.NatCast in
theorem midpoint_velocity (γ : ℝ) (x y : StateCoordinates) (hx : 0 < x 0) (hy : 0 < y 0) :
    (fun i : Fin 3 => midpoint γ x y i.succ / midpoint γ x y 0) = averageVelocity x y := by
  have hw := ne_of_gt (root_sum_pos x y hx hy)
  funext i
  fin_cases i <;> simp [midpoint, parameter, averageVelocity, weight, add_comm (root y) (root x)]
  all_goals field_simp [hw]

theorem midpoint_enthalpy (γ : ℝ) (x y : StateCoordinates) (hx : 0 < x 0) (hy : 0 < y 0) :
    midpoint γ x y 4 / midpoint γ x y 0 = averageEnthalpy γ x y := by
  have hw := ne_of_gt (root_sum_pos x y hx hy)
  simp [midpoint, parameter, averageEnthalpy, weight, add_comm (root y) (root x)]
  field_simp [hw]

open Fin.NatCast in
theorem operator_B (γ : ℝ) (n : Vector 3) (z : StateCoordinates) (hγ : γ ≠ 0) (hz : z 0 ≠ 0) :
    (operator γ (fun i => z i.succ / z 0) (z 4 / z 0) n).comp (B γ z) = C γ n z := by
  unfold operator
  rw [assemble_eq_pi]
  ext v i
  fin_cases i <;> simp [B, C, pressureGradient, normalMomentum, projection, dot_three, squareSum_three]
  all_goals field_simp [hγ, hz]
  all_goals ring1

theorem roeMatrix_B (γ : ℝ) (n : Vector 3) (x y : StateCoordinates)
    (hγ : γ ≠ 0) (hx : 0 < x 0) (hy : 0 < y 0) :
    (roeMatrix γ x y n).comp (B γ (midpoint γ x y)) = C γ n (midpoint γ x y) := by
  unfold roeMatrix
  rw [← midpoint_velocity γ x y hx hy, ← midpoint_enthalpy γ x y hx hy]
  exact operator_B γ n _ hγ (ne_of_gt (midpoint_pos γ x y hx hy))

theorem secant_identity (γ : ℝ) (n : Vector 3) (x y : StateCoordinates)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) :
    roeMatrix γ x y n (y - x) = coordinateFlux γ n y - coordinateFlux γ n x := by
  have hg : γ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hγ)
  have hU := state_midpoint_jump γ (parameter γ x) (parameter γ y)
  rw [parameter_state γ x hg hx.1, parameter_state γ y hg hy.1] at hU
  rw [hU]
  change ((roeMatrix γ x y n).comp (B γ (midpoint γ x y))) _ = _
  rw [roeMatrix_B γ n x y hg hx.1 hy.1]
  change C γ n (fun i => (parameter γ x i + parameter γ y i) / 2)
    (parameter γ y - parameter γ x) = _
  rw [← flux_midpoint_jump]
  rw [parameter_flux γ n x hg hx.1, parameter_flux γ n y hg hy.1]

theorem hasFDerivAt_parameterState (γ : ℝ) (z : StateCoordinates) :
    HasFDerivAt (parameterState γ) (B γ z) z := by
  have h0 := (projection 0).hasFDerivAt (x := z)
  have h1 := (projection 1).hasFDerivAt (x := z)
  have h2 := (projection 2).hasFDerivAt (x := z)
  have h3 := (projection 3).hasFDerivAt (x := z)
  have h4 := (projection 4).hasFDerivAt (x := z)
  have hQ := ((h1.mul h1).add (h2.mul h2)).add (h3.mul h3)
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert h0.mul h0 using 1
    · funext y; simp [parameterState, projection, pow_two]
    · ext v; simp [projection]; ring1
  · convert h0.mul h1 using 1
    · rfl
    ext v; simp [projection]; ring1
  · convert h0.mul h2 using 1
    · rfl
    ext v; simp [projection]; ring1
  · convert h0.mul h3 using 1
    · rfl
    ext v; simp [projection]; ring1
  · convert ((h0.mul h4).add (hQ.const_mul ((γ - 1) / 2))).mul_const (1 / γ) using 1
    · funext y; simp [parameterState, projection, pow_two, div_eq_mul_inv]
    · ext v; simp [projection]; ring1

theorem hasFDerivAt_parameterPressure (γ : ℝ) (z : StateCoordinates) :
    HasFDerivAt (parameterPressure γ) (pressureGradient γ z) z := by
  have h0 := (projection 0).hasFDerivAt (x := z)
  have h1 := (projection 1).hasFDerivAt (x := z)
  have h2 := (projection 2).hasFDerivAt (x := z)
  have h3 := (projection 3).hasFDerivAt (x := z)
  have h4 := (projection 4).hasFDerivAt (x := z)
  have hQ := ((h1.mul h1).add (h2.mul h2)).add (h3.mul h3)
  convert ((h0.mul h4).sub (hQ.mul_const (1 / 2 : ℝ))).const_mul ((γ - 1) / γ) using 1
  · funext y; simp [parameterPressure, projection, pow_two, div_eq_mul_inv]
  · apply ContinuousLinearMap.ext
    intro v
    change ((γ - 1) / γ) * (z 4 * v 0 + z 0 * v 4 -
      (z 1 * v 1 + z 2 * v 2 + z 3 * v 3)) =
      ((γ - 1) / γ) * (z 0 * v 4 + z 4 * v 0 - (1 / 2 : ℝ) *
        ((z 1 * v 1 + z 1 * v 1) + (z 2 * v 2 + z 2 * v 2) + (z 3 * v 3 + z 3 * v 3)))
    ring1

theorem hasFDerivAt_parameterFlux (γ : ℝ) (n : Vector 3) (z : StateCoordinates) :
    HasFDerivAt (parameterFlux γ n) (C γ n z) z := by
  have h0 := (projection 0).hasFDerivAt (x := z)
  have h1 := (projection 1).hasFDerivAt (x := z)
  have h2 := (projection 2).hasFDerivAt (x := z)
  have h3 := (projection 3).hasFDerivAt (x := z)
  have h4 := (projection 4).hasFDerivAt (x := z)
  have hq := (normalMomentum n).hasFDerivAt (x := z)
  have hp := hasFDerivAt_parameterPressure γ z
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert h0.mul hq using 1
    · rfl
    ext v; simp [projection]; ring1
  · convert (h1.mul hq).add (hp.mul_const (n 0)) using 1
    · rfl
    ext v; simp [projection]; ring1
  · convert (h2.mul hq).add (hp.mul_const (n 1)) using 1
    · rfl
    ext v; simp [projection]; ring1
  · convert (h3.mul hq).add (hp.mul_const (n 2)) using 1
    · rfl
    ext v; simp [projection]; ring1
  · convert h4.mul hq using 1
    · rfl
    ext v; simp [projection]; ring1

theorem roeMatrix_CB_inverse (γ : ℝ) (n : Vector 3) (x y : StateCoordinates)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) :
    roeMatrix γ x y n = (C γ n (midpoint γ x y)).comp (inverseB γ (midpoint γ x y)) := by
  have hg : γ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hγ)
  have hz := ne_of_gt (midpoint_pos γ x y hx.1 hy.1)
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun f : StateCoordinates →L[ℝ] StateCoordinates =>
    f (inverseB γ (midpoint γ x y) v)) (roeMatrix_B γ n x y hg hx.1 hy.1)
  simpa only [ContinuousLinearMap.comp_apply, B_inverseB γ _ hg hz] using h

theorem roeMatrix_swap (γ : ℝ) (n : Vector 3) (x y : StateCoordinates) :
    roeMatrix γ y x n = roeMatrix γ x y n := by
  unfold roeMatrix
  rw [(averages_swap γ x y).1, (averages_swap γ x y).2.1]

theorem operator_smul (γ : ℝ) (u : Vector 3) (H a : ℝ) (n : Vector 3) :
    operator γ u H (fun i => a * n i) = a • operator γ u H n := by
  simp only [operator, assemble_eq_pi]
  ext v i
  fin_cases i <;> simp [normalMomentum, projection, dot_three] <;> ring1

theorem integrated_secant (γ : ℝ) (S : Vector 3) (x y : StateCoordinates)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) (hS : S ≠ 0) :
    (area S • roeMatrix γ x y (unitNormal S)) (y - x) =
      coordinateFlux γ S y - coordinateFlux γ S x := by
  have hmat : roeMatrix γ x y S = area S • roeMatrix γ x y (unitNormal S) := by
    conv_lhs => rw [reconstruct_area S hS]
    exact operator_smul γ _ _ _ _
  rw [← hmat]
  exact secant_identity γ S x y hγ hx hy

theorem operator_continuous (γ : ℝ) (n : Vector 3) :
    Continuous (fun p : Vector 3 × ℝ => operator γ p.1 p.2 n) := by
  have hu (i : Fin 3) : Continuous (fun p : Vector 3 × ℝ => p.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hq : Continuous (fun p : Vector 3 × ℝ => dot p.1 n) := by
    simp only [dot_three]
    exact (((hu 0).mul continuous_const).add ((hu 1).mul continuous_const)).add
      ((hu 2).mul continuous_const)
  have hs : Continuous (fun p : Vector 3 × ℝ => squareSum p.1) := by
    simp only [squareSum_three]
    exact (((hu 0).pow 2).add ((hu 1).pow 2)).add ((hu 2).pow 2)
  have hb : Continuous (fun p : Vector 3 × ℝ => normalMomentum n - dot p.1 n • projection 0) :=
    by fun_prop
  have hp : Continuous (fun p : Vector 3 × ℝ => (γ - 1) • (projection 4 -
      (p.1 0 • projection 1 + p.1 1 • projection 2 + p.1 2 • projection 3) +
      (squareSum p.1 / 2) • projection 0)) :=
    by fun_prop
  have hr0 : Continuous (fun _ : Vector 3 × ℝ => normalMomentum n) := continuous_const
  have hr (i : Fin 3) (j : Fin 5) : Continuous (fun p : Vector 3 × ℝ =>
      dot p.1 n • projection j + p.1 i • (normalMomentum n - dot p.1 n • projection 0) +
      n i • ((γ - 1) • (projection 4 -
        (p.1 0 • projection 1 + p.1 1 • projection 2 + p.1 2 • projection 3) +
        (squareSum p.1 / 2) • projection 0))) :=
    by fun_prop
  have hE : Continuous (fun p : Vector 3 × ℝ => dot p.1 n • (projection 4 +
      (γ - 1) • (projection 4 -
        (p.1 0 • projection 1 + p.1 1 • projection 2 + p.1 2 • projection 3) +
        (squareSum p.1 / 2) • projection 0)) +
      p.2 • (normalMomentum n - dot p.1 n • projection 0)) :=
    by fun_prop
  exact ((((hr0.const_clm_comp (embed 0)).add ((hr 0 1).const_clm_comp (embed 1))).add
    ((hr 1 2).const_clm_comp (embed 2))).add ((hr 2 3).const_clm_comp (embed 3))).add
      (hE.const_clm_comp (embed 4))

theorem roeMatrix_continuousAt (γ : ℝ) (n : Vector 3) (p : StateCoordinates × StateCoordinates)
    (hx : 0 < p.1 0) (hy : 0 < p.2 0) :
    ContinuousAt (fun q : StateCoordinates × StateCoordinates => roeMatrix γ q.1 q.2 n) p := by
  exact ContinuousAt.comp
    (f := fun q : StateCoordinates × StateCoordinates =>
      (averageVelocity q.1 q.2, averageEnthalpy γ q.1 q.2))
    (g := fun r : Vector 3 × ℝ => operator γ r.1 r.2 n)
    (operator_continuous γ n).continuousAt (averages_continuousAt γ p hx hy)

theorem roeMatrix_continuousOn (γ : ℝ) (n : Vector 3) :
    ContinuousOn (fun q : StateCoordinates × StateCoordinates => roeMatrix γ q.1 q.2 n)
      {p | (decode p.1).Admissible γ ∧ (decode p.2).Admissible γ} := by
  intro p hp
  exact (roeMatrix_continuousAt γ n p hp.1.1 hp.2.1).continuousWithinAt

theorem roeMatrix_diagonal (γ : ℝ) (x : StateCoordinates) (n : Vector 3) (hx : 0 < x 0) :
    roeMatrix γ x x n = jacobian γ x n := by
  unfold roeMatrix
  rw [(averages_diagonal γ x hx).1, (averages_diagonal γ x hx).2]
  exact operator_physical γ x n

theorem hasFDerivAt_diagonal (γ : ℝ) (x : StateCoordinates) (n : Vector 3)
    (hx : (decode x).Admissible γ) :
    HasFDerivAt (fun y => encode (physicalFlux γ (decode y) n)) (roeMatrix γ x x n) x := by
  rw [roeMatrix_diagonal γ x n hx.1]
  exact hasFDerivAt_coordinateFlux γ n x (ne_of_gt hx.1)

theorem roeMatrix_equal_state_limit (γ : ℝ) (x : StateCoordinates) (n : Vector 3)
    (hx : (decode x).Admissible γ) :
    Filter.Tendsto (fun p : StateCoordinates × StateCoordinates => roeMatrix γ p.1 p.2 n)
      (nhds (x, x)) (nhds (jacobian γ x n)) := by
  rw [← roeMatrix_diagonal γ x n hx.1]
  exact (roeMatrix_continuousAt γ n (x, x) hx.1 hx.1).tendsto

end CFDLean.Roe
