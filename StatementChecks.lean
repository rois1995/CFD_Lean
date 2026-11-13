import CFDLean

open CFDLean Coordinates PhysicalJacobian
open scoped Topology

example (U : Conservative 3) : decode (encode U) = U := decode_encode U
example (x : StateCoordinates) : encode (decode x) = x := encode_decode x
example (g : ℝ) : IsOpen {x : StateCoordinates | (decode x).Admissible g} := isOpen_admissible g

example (s : Vector 3) (hs : s ≠ 0) :
    dot (fun i => s i / Real.sqrt (squareSum s)) (fun i => s i / Real.sqrt (squareSum s)) = 1 :=
  unitNormal_dot_self s hs

example (g : ℝ) (U V : Conservative 3) (n : Vector 3) :
    let u : Vector 3 := fun i => U.momentum i / U.density
    let q := dot u n
    let b := dot V.momentum n - q * V.density
    let dp := (g - 1) * (V.energy - dot u V.momentum + squareSum u / 2 * V.density)
    jacobian g (encode U) n (encode V) = encode
      ⟨dot V.momentum n, fun i => q * V.momentum i + u i * b + dp * n i,
       q * (V.energy + dp) + ((U.energy + U.pressure g) / U.density) * b⟩ := by
  exact jacobian_action g U V n

-- State the link using the accepted flux directly.
example (g : ℝ) (n : Vector 3) (x : StateCoordinates) (hr : x 0 ≠ 0) :
    HasFDerivAt (fun y => encode (physicalFlux g (decode y) n)) (jacobian g x n) x :=
  hasFDerivAt_coordinateFlux g n x hr

example (g : ℝ) (S : Vector 3) (x : StateCoordinates) (hr : x 0 ≠ 0) (hs : S ≠ 0) :
    HasFDerivAt (fun y => encode (physicalFlux g (decode y) S)) (area S • jacobian g x (unitNormal S)) x :=
  hasFDerivAt_integratedFlux g S x hr hs

example (g : ℝ) (x : StateCoordinates) : HasFDerivAt (𝕜 := ℝ)
    (fun y => encode (physicalFlux g (decode y) (0 : Vector 3))) 0 x :=
  hasFDerivAt_zeroArea g x

open CFDLean.Roe

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

example (g : ℝ) (x y : StateCoordinates) (_hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) :
    0 < weight x y ∧ weight x y < 1 ∧ weight x y + weight y x = 1 :=
  ⟨weight_pos x y hx.1 hy.1, weight_lt_one x y hx.1 hy.1, weight_sum x y hx.1 hy.1⟩

example (g : ℝ) (x y : StateCoordinates) (hx : 0 < x 0) (hy : 0 < y 0) :
    soundSquare g x y = weight x y * (g * (decode x).pressure g / x 0) +
      weight y x * (g * (decode y).pressure g / y 0) +
      (g - 1) / 2 * weight x y * weight y x * squareSum (fun i => velocity y i - velocity x i) :=
  variance_identity g x y hx hy

example (g : ℝ) (x y : StateCoordinates) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) :
    0 < soundSquare g x y ∧ 0 < soundSpeed g x y :=
  ⟨soundSquare_pos g x y hg hx hy, soundSpeed_pos g x y hg hx hy⟩

example (g : ℝ) (x : StateCoordinates) (hg : g ≠ 0) (hx : 0 < x 0) :
    parameterState g (parameter g x) = x := parameter_state g x hg hx

example (g : ℝ) (n : Vector 3) (x : StateCoordinates) (hg : g ≠ 0) (hx : 0 < x 0) :
    parameterFlux g n (parameter g x) = encode (physicalFlux g (decode x) n) :=
  parameter_flux g n x hg hx

example (g : ℝ) (n : Vector 3) (z : StateCoordinates) :
    HasFDerivAt (parameterState g) (B g z) z ∧
    HasFDerivAt (parameterFlux g n) (C g n z) z :=
  ⟨hasFDerivAt_parameterState g z, hasFDerivAt_parameterFlux g n z⟩

example (g : ℝ) (x y : StateCoordinates) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) :
    Function.Bijective (B g (midpoint g x y)) :=
  B_bijective g _ (ne_of_gt (lt_trans zero_lt_one hg)) (ne_of_gt (midpoint_pos g x y hx.1 hy.1))

example (g : ℝ) (n : Vector 3) (x y : StateCoordinates) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) :
    roeMatrix g x y n (y - x) = encode (physicalFlux g (decode y) n) -
      encode (physicalFlux g (decode x) n) := secant_identity g n x y hg hx hy

example (g : ℝ) (n : Vector 3) (x y : StateCoordinates) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) :
    roeMatrix g x y n = (C g n (midpoint g x y)).comp (inverseB g (midpoint g x y)) :=
  roeMatrix_CB_inverse g n x y hg hx hy

example (g : ℝ) (n : Vector 3) :
    ContinuousOn (fun p : StateCoordinates × StateCoordinates => roeMatrix g p.1 p.2 n)
      {p | (decode p.1).Admissible g ∧ (decode p.2).Admissible g} := roeMatrix_continuousOn g n

example (g : ℝ) (n : Vector 3) (x : StateCoordinates) (hx : (decode x).Admissible g) :
    HasFDerivAt (fun y => encode (physicalFlux g (decode y) n)) (roeMatrix g x x n) x :=
  hasFDerivAt_diagonal g x n hx

example (g : ℝ) (n : Vector 3) (x : StateCoordinates) (hx : (decode x).Admissible g) :
    Filter.Tendsto (fun p : StateCoordinates × StateCoordinates => roeMatrix g p.1 p.2 n)
      (𝓝 (x, x)) (𝓝 (jacobian g x n)) := roeMatrix_equal_state_limit g x n hx

example : soundSquare 2 (![1, 0, 0, 0, 1]) (![4, 0, 0, 0, 1]) = 1 := by
  have hs : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  norm_num [soundSquare, averageEnthalpy, averageVelocity, weight, root, velocity,
    enthalpy, coordinatePressure, Conservative.pressure, decode, squareSum_three, hs]

example : soundSquare 2 (![1, 0, 1, 0, 3 / 2]) (![1, 0, -1, 0, 3 / 2]) = 5 / 2 := by
  norm_num [soundSquare, averageEnthalpy, averageVelocity, weight, root, velocity,
    enthalpy, coordinatePressure, Conservative.pressure, decode, squareSum_three]
