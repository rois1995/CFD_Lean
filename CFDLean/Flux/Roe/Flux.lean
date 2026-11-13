import CFDLean.Flux.Roe.Spectral

noncomputable section
namespace CFDLean.Roe
open Coordinates PhysicalJacobian

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] Spectral.shift Spectral.b Spectral.dp

/-- Original Roe flux in conservative coordinates; S is an oriented area vector. -/
def roeFluxCoordinates (γ : ℝ) (x y : StateCoordinates) (S : Vector 3) : StateCoordinates := by
  classical
  exact if S = 0 then 0 else
    (1 / 2 : ℝ) • (coordinateFlux γ S x + coordinateFlux γ S y) -
      (area S / 2) • Spectral.dissipation γ x y (unitNormal S) (y - x)

/-- Integrated transfer in the conserved-vector layout, not an admissible state assertion. -/
def numericalFlux (γ : ℝ) (U V : Conservative 3) (S : Vector 3) : Conservative 3 :=
  decode (roeFluxCoordinates γ (encode U) (encode V) S)

theorem area_neg (S : Vector 3) : area (-S) = area S := by
  unfold area squareSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (-S i) ^ 2 = S i ^ 2
  ring1

theorem unitNormal_neg (S : Vector 3) : unitNormal (-S) = -unitNormal S := by
  funext i
  simp only [unitNormal, Pi.neg_apply, area_neg, neg_div]

theorem area_scale (a : ℝ) (S : Vector 3) (ha : 0 ≤ a) :
    area (fun i => a * S i) = a * area S := by
  unfold area
  rw [squareSum_mul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

theorem unitNormal_scale (a : ℝ) (S : Vector 3) (ha : 0 < a) (hS : S ≠ 0) :
    unitNormal (fun i => a * S i) = unitNormal S := by
  funext i
  simp only [unitNormal, area_scale a S (le_of_lt ha)]
  field_simp [ne_of_gt ha, ne_of_gt (area_pos S hS)]
  ring1

theorem coordinateFlux_scale (γ a : ℝ) (S : Vector 3) (x : StateCoordinates) :
    coordinateFlux γ (fun i => a * S i) x = a • coordinateFlux γ S x := by
  unfold coordinateFlux
  rw [physicalFlux_mul]
  funext i
  fin_cases i <;> rfl

theorem coordinateFlux_neg (γ : ℝ) (S : Vector 3) (x : StateCoordinates) :
    coordinateFlux γ (-S) x = -coordinateFlux γ S x := by
  change encode (physicalFlux γ (decode x) (fun i => -S i)) = _
  rw [physicalFlux_reverse]
  funext i
  fin_cases i <;> rfl

theorem decode_zero : decode (0 : StateCoordinates) = ⟨0, fun _ => 0, 0⟩ := by
  have h : encode (Conservative.mk 0 (fun _ : Fin 3 => 0) 0) = 0 := by
    funext i
    fin_cases i <;> rfl
  rw [← h, decode_encode]

theorem decode_neg (x : StateCoordinates) :
    decode (-x) = ⟨-(decode x).density, fun i => -(decode x).momentum i, -(decode x).energy⟩ := by
  have h : encode (Conservative.mk (-(decode x).density) (fun i => -(decode x).momentum i)
      (-(decode x).energy)) = -x := by
    funext i
    fin_cases i <;> rfl
  rw [← h, decode_encode]

theorem decode_scale (a : ℝ) (x : StateCoordinates) :
    decode (a • x) = ⟨a * (decode x).density, fun i => a * (decode x).momentum i, a * (decode x).energy⟩ := by
  have h : encode (Conservative.mk (a * (decode x).density) (fun i => a * (decode x).momentum i)
      (a * (decode x).energy)) = a • x := by
    funext i
    fin_cases i <;> rfl
  rw [← h, decode_encode]

theorem roeFluxCoordinates_zero (γ : ℝ) (x y : StateCoordinates) :
    roeFluxCoordinates γ x y (0 : Vector 3) = 0 := by
  simp [roeFluxCoordinates]

theorem roeFluxCoordinates_consistency (γ : ℝ) (x : StateCoordinates) (S : Vector 3) :
    roeFluxCoordinates γ x x S = coordinateFlux γ S x := by
  classical
  by_cases hS : S = 0
  · subst S
    simp [roeFluxCoordinates_zero, coordinateFlux_zero]
  · rw [roeFluxCoordinates, if_neg hS, sub_self, map_zero]
    module

theorem roeFluxCoordinates_reverse (γ : ℝ) (x y : StateCoordinates) (S : Vector 3) :
    roeFluxCoordinates γ y x (-S) = -roeFluxCoordinates γ x y S := by
  classical
  by_cases hS : S = 0
  · subst S
    simp [roeFluxCoordinates_zero]
  · rw [roeFluxCoordinates, if_neg (neg_ne_zero.mpr hS), roeFluxCoordinates, if_neg hS,
      area_neg, unitNormal_neg, coordinateFlux_neg, coordinateFlux_neg]
    rw [(Spectral.roe_swap γ x y (-unitNormal S)).2.2, Spectral.roe_absolute_reverse]
    have h : x - y = -(y - x) := by module
    rw [h, map_neg]
    module

theorem roeFluxCoordinates_scale (γ a : ℝ) (x y : StateCoordinates) (S : Vector 3) (ha : 0 ≤ a) :
    roeFluxCoordinates γ x y (fun i => a * S i) = a • roeFluxCoordinates γ x y S := by
  classical
  by_cases ha0 : a = 0
  · subst a
    simp only [zero_mul, zero_smul]
    change roeFluxCoordinates γ x y (0 : Vector 3) = 0
    exact roeFluxCoordinates_zero γ x y
  · by_cases hS : S = 0
    · subst S
      simp only [Pi.zero_apply, mul_zero, roeFluxCoordinates_zero, smul_zero]
      change roeFluxCoordinates γ x y (0 : Vector 3) = 0
      exact roeFluxCoordinates_zero γ x y
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hAS : (fun i => a * S i) ≠ 0 := by
        intro h
        apply hS
        funext i
        have hi := congrFun h i
        change a * S i = 0 at hi
        exact (mul_eq_zero.mp hi).resolve_left ha0
      rw [roeFluxCoordinates, if_neg hAS, roeFluxCoordinates, if_neg hS,
        coordinateFlux_scale, coordinateFlux_scale, area_scale a S ha, unitNormal_scale a S hap hS]
      module

theorem numericalFlux_zero (γ : ℝ) (U V : Conservative 3) :
    numericalFlux γ U V (0 : Vector 3) = ⟨0, fun _ => 0, 0⟩ := by
  rw [numericalFlux, roeFluxCoordinates_zero, decode_zero]

theorem numericalFlux_consistency (γ : ℝ) (U : Conservative 3) (S : Vector 3) :
    numericalFlux γ U U S = physicalFlux γ U S := by
  rw [numericalFlux, roeFluxCoordinates_consistency]
  simp only [coordinateFlux, decode_encode]

theorem numericalFlux_reverse (γ : ℝ) (U V : Conservative 3) (S : Vector 3) :
    numericalFlux γ V U (-S) = ⟨-(numericalFlux γ U V S).density,
      fun i => -(numericalFlux γ U V S).momentum i, -(numericalFlux γ U V S).energy⟩ := by
  unfold numericalFlux
  rw [roeFluxCoordinates_reverse, decode_neg]

theorem numericalFlux_scale (γ a : ℝ) (U V : Conservative 3) (S : Vector 3) (ha : 0 ≤ a) :
    numericalFlux γ U V (fun i => a * S i) = ⟨a * (numericalFlux γ U V S).density,
      fun i => a * (numericalFlux γ U V S).momentum i, a * (numericalFlux γ U V S).energy⟩ := by
  unfold numericalFlux
  rw [roeFluxCoordinates_scale γ a _ _ S ha, decode_scale]

theorem dissipation_of_nonnegative (γ : ℝ) (x y : StateCoordinates) (n : Vector 3)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ)
    (h0 : 0 ≤ Spectral.roeSpeed γ x y n 0) (h1 : 0 ≤ Spectral.roeSpeed γ x y n 1)
    (h2 : 0 ≤ Spectral.roeSpeed γ x y n 2) :
    Spectral.dissipation γ x y n = (roeMatrix γ x y n).toLinearMap := by
  change |Spectral.roeSpeed γ x y n 0| • Spectral.roeProjector γ x y n 0 +
    |Spectral.roeSpeed γ x y n 1| • Spectral.roeProjector γ x y n 1 +
    |Spectral.roeSpeed γ x y n 2| • Spectral.roeProjector γ x y n 2 = _
  rw [abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonneg h2,
    ← Spectral.roe_spectral_decomposition γ x y n hγ hx hy]

theorem dissipation_of_nonpositive (γ : ℝ) (x y : StateCoordinates) (n : Vector 3)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ)
    (h0 : Spectral.roeSpeed γ x y n 0 ≤ 0) (h1 : Spectral.roeSpeed γ x y n 1 ≤ 0)
    (h2 : Spectral.roeSpeed γ x y n 2 ≤ 0) :
    Spectral.dissipation γ x y n = -(roeMatrix γ x y n).toLinearMap := by
  change |Spectral.roeSpeed γ x y n 0| • Spectral.roeProjector γ x y n 0 +
    |Spectral.roeSpeed γ x y n 1| • Spectral.roeProjector γ x y n 1 +
    |Spectral.roeSpeed γ x y n 2| • Spectral.roeProjector γ x y n 2 = _
  rw [abs_of_nonpos h0, abs_of_nonpos h1, abs_of_nonpos h2,
    Spectral.roe_spectral_decomposition γ x y n hγ hx hy]
  module

theorem dissipation_upwind_left (γ : ℝ) (x y : StateCoordinates) (n : Vector 3)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ)
    (hup : soundSpeed γ x y ≤ dot (averageVelocity x y) n) :
    Spectral.dissipation γ x y n = (roeMatrix γ x y n).toLinearMap := by
  have hc := soundSpeed_pos γ x y hγ hx hy
  apply dissipation_of_nonnegative γ x y n hγ hx hy
  · change 0 ≤ dot (averageVelocity x y) n + -soundSpeed γ x y
    linarith
  · change 0 ≤ dot (averageVelocity x y) n + 0
    linarith
  · change 0 ≤ dot (averageVelocity x y) n + soundSpeed γ x y
    linarith

theorem dissipation_upwind_right (γ : ℝ) (x y : StateCoordinates) (n : Vector 3)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ)
    (hup : dot (averageVelocity x y) n ≤ -soundSpeed γ x y) :
    Spectral.dissipation γ x y n = -(roeMatrix γ x y n).toLinearMap := by
  have hc := soundSpeed_pos γ x y hγ hx hy
  apply dissipation_of_nonpositive γ x y n hγ hx hy
  · change dot (averageVelocity x y) n + -soundSpeed γ x y ≤ 0
    linarith
  · change dot (averageVelocity x y) n + 0 ≤ 0
    linarith
  · change dot (averageVelocity x y) n + soundSpeed γ x y ≤ 0
    linarith

theorem roeFluxCoordinates_upwind_left (γ : ℝ) (x y : StateCoordinates) (S : Vector 3)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) (hS : S ≠ 0)
    (hup : soundSpeed γ x y ≤ dot (averageVelocity x y) (unitNormal S)) :
    roeFluxCoordinates γ x y S = coordinateFlux γ S x := by
  classical
  rw [roeFluxCoordinates, if_neg hS, dissipation_upwind_left γ x y _ hγ hx hy hup]
  have hs := integrated_secant γ S x y hγ hx hy hS
  change area S • roeMatrix γ x y (unitNormal S) (y - x) =
    coordinateFlux γ S y - coordinateFlux γ S x at hs
  change (1 / 2 : ℝ) • (coordinateFlux γ S x + coordinateFlux γ S y) -
    (area S / 2) • roeMatrix γ x y (unitNormal S) (y - x) = _
  calc
    _ = (1 / 2 : ℝ) • (coordinateFlux γ S x + coordinateFlux γ S y) -
        (1 / 2 : ℝ) • (area S • roeMatrix γ x y (unitNormal S) (y - x)) := by module
    _ = _ := by rw [hs]; module

theorem roeFluxCoordinates_upwind_right (γ : ℝ) (x y : StateCoordinates) (S : Vector 3)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) (hS : S ≠ 0)
    (hup : dot (averageVelocity x y) (unitNormal S) ≤ -soundSpeed γ x y) :
    roeFluxCoordinates γ x y S = coordinateFlux γ S y := by
  classical
  rw [roeFluxCoordinates, if_neg hS, dissipation_upwind_right γ x y _ hγ hx hy hup]
  have hs := integrated_secant γ S x y hγ hx hy hS
  change area S • roeMatrix γ x y (unitNormal S) (y - x) =
    coordinateFlux γ S y - coordinateFlux γ S x at hs
  change (1 / 2 : ℝ) • (coordinateFlux γ S x + coordinateFlux γ S y) -
    (area S / 2) • (-roeMatrix γ x y (unitNormal S) (y - x)) = _
  calc
    _ = (1 / 2 : ℝ) • (coordinateFlux γ S x + coordinateFlux γ S y) +
        (1 / 2 : ℝ) • (area S • roeMatrix γ x y (unitNormal S) (y - x)) := by module
    _ = _ := by rw [hs]; module

theorem numericalFlux_upwind_left (γ : ℝ) (U V : Conservative 3) (S : Vector 3)
    (hγ : 1 < γ) (hU : U.Admissible γ) (hV : V.Admissible γ) (hS : S ≠ 0)
    (hup : soundSpeed γ (encode U) (encode V) ≤ dot (averageVelocity (encode U) (encode V)) (unitNormal S)) :
    numericalFlux γ U V S = physicalFlux γ U S := by
  unfold numericalFlux
  rw [roeFluxCoordinates_upwind_left γ _ _ S hγ (by simpa only [decode_encode] using hU)
    (by simpa only [decode_encode] using hV) hS hup]
  simp only [coordinateFlux, decode_encode]

theorem numericalFlux_upwind_right (γ : ℝ) (U V : Conservative 3) (S : Vector 3)
    (hγ : 1 < γ) (hU : U.Admissible γ) (hV : V.Admissible γ) (hS : S ≠ 0)
    (hup : dot (averageVelocity (encode U) (encode V)) (unitNormal S) ≤ -soundSpeed γ (encode U) (encode V)) :
    numericalFlux γ U V S = physicalFlux γ V S := by
  unfold numericalFlux
  rw [roeFluxCoordinates_upwind_right γ _ _ S hγ (by simpa only [decode_encode] using hU)
    (by simpa only [decode_encode] using hV) hS hup]
  simp only [coordinateFlux, decode_encode]

theorem dissipation_zero_of_matrix_zero (γ : ℝ) (x y : StateCoordinates) (n : Vector 3)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) (hn : dot n n = 1)
    (v : StateCoordinates) (he : roeMatrix γ x y n v = 0) : Spectral.dissipation γ x y n v = 0 := by
  by_cases hv : v = 0
  · subst v
    exact (Spectral.dissipation γ x y n).map_zero
  · have he' : roeMatrix γ x y n v = (0 : ℝ) • v := by rw [zero_smul]; exact he
    have hd := Spectral.roe_absolute_eigen γ x y n hγ hx hy hn 0 v hv he'
    rw [abs_zero, zero_smul] at hd
    exact hd

theorem roeFluxCoordinates_central_of_zero (γ : ℝ) (x y : StateCoordinates) (S : Vector 3)
    (hγ : 1 < γ) (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) (hS : S ≠ 0)
    (he : roeMatrix γ x y (unitNormal S) (y - x) = 0) :
    roeFluxCoordinates γ x y S = (1 / 2 : ℝ) • (coordinateFlux γ S x + coordinateFlux γ S y) := by
  classical
  rw [roeFluxCoordinates, if_neg hS,
    dissipation_zero_of_matrix_zero γ x y _ hγ hx hy (unitNormal_dot_self S hS) _ he, smul_zero, sub_zero]

/-- Approved receding-state endpoints, formed through the accepted primitive conversion. -/
def witnessLeft : Conservative 3 := (Primitive.mk 1 ![-2, 0, 0] (1 / 2)).toConservative 2
def witnessRight : Conservative 3 := (Primitive.mk 1 ![2, 0, 0] (1 / 2)).toConservative 2

def witnessIntermediate : Conservative 3 := decode (encode witnessLeft +
  Spectral.roeProjector 2 (encode witnessLeft) (encode witnessRight) ![1, 0, 0] 0
    (encode witnessRight - encode witnessLeft))

theorem witness_endpoints : encode witnessLeft = ![1, -2, 0, 0, 5 / 2] ∧
    encode witnessRight = ![1, 2, 0, 0, 5 / 2] := by
  constructor <;> norm_num [witnessLeft, witnessRight, Primitive.toConservative, encode, squareSum_three]

theorem witness_admissible : witnessLeft.Admissible 2 ∧ witnessRight.Admissible 2 := by
  constructor <;> norm_num [witnessLeft, witnessRight, Primitive.toConservative,
    Conservative.Admissible, Conservative.pressure, squareSum_three]

theorem witness_averages : averageVelocity (encode witnessLeft) (encode witnessRight) = 0 ∧
    averageEnthalpy 2 (encode witnessLeft) (encode witnessRight) = 3 ∧
    soundSquare 2 (encode witnessLeft) (encode witnessRight) = 3 := by
  rw [witness_endpoints.1, witness_endpoints.2]
  norm_num [averageVelocity, averageEnthalpy, soundSquare, weight, root, velocity, enthalpy,
    coordinatePressure, Conservative.pressure, decode, squareSum_three]
  funext i
  fin_cases i <;> norm_num [averageVelocity, weight, root, velocity, decode]

theorem witness_intermediate_coordinates : encode witnessIntermediate =
    ![1 - 2 / Real.sqrt 3, 0, 0, 0, 5 / 2 - 2 * Real.sqrt 3] := by
  have hc : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold witnessIntermediate
  rw [encode_decode]
  have hp : Spectral.roeProjector 2 (encode witnessLeft) (encode witnessRight) ![1, 0, 0] 0 =
      Spectral.minus 2 0 3 ![1, 0, 0] (Real.sqrt 3) := by
    change Spectral.minus 2 _ _ _ _ = _
    rw [witness_averages.1, witness_averages.2.1, soundSpeed, witness_averages.2.2]
  rw [hp, Spectral.minus_apply 2 0 3 ![1, 0, 0] (Real.sqrt 3)
    (by norm_num [dot_three]) (by norm_num [squareSum_three, hs]),
    witness_endpoints.1, witness_endpoints.2]
  funext i
  fin_cases i <;> norm_num [Spectral.dp, Spectral.b, Spectral.acoustic, Spectral.vb, Spectral.vp,
    projection, normalMomentum, squareSum_three, dot_three, Pi.smul_apply] <;>
    field_simp [ne_of_gt hc] <;> nlinarith [hs]

theorem positivity_counterexample : witnessLeft.Admissible 2 ∧ witnessRight.Admissible 2 ∧
    0 < soundSquare 2 (encode witnessLeft) (encode witnessRight) ∧ witnessIntermediate.density < 0 := by
  refine ⟨witness_admissible.1, witness_admissible.2, ?_, ?_⟩
  · rw [witness_averages.2.2]
    norm_num
  · have hc : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hlt : Real.sqrt (3 : ℝ) < 2 := by nlinarith
    have hd := congrFun witness_intermediate_coordinates 0
    change witnessIntermediate.density = 1 - 2 / Real.sqrt 3 at hd
    rw [hd]
    have : (1 : ℝ) < 2 / Real.sqrt 3 := (lt_div_iff₀ hc).mpr (by simpa using hlt)
    linarith

end CFDLean.Roe
