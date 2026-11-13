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

open CFDLean.Roe.Spectral

example (g : ℝ) (x y : E) (n : Vector 3) :
    roeShift g x y n = (roeMatrix g x y n).toLinearMap - dot (averageVelocity x y) n • 1 := rfl

example (g : ℝ) (x y : E) (n : Vector 3) :
    roeProjector g x y n 0 = (1 / (2 * soundSpeed g x y ^ 2)) •
      (roeShift g x y n ^ 2 - soundSpeed g x y • roeShift g x y n) ∧
    roeProjector g x y n 1 = 1 - (1 / soundSpeed g x y ^ 2) • roeShift g x y n ^ 2 ∧
    roeProjector g x y n 2 = (1 / (2 * soundSpeed g x y ^ 2)) •
      (roeShift g x y n ^ 2 + soundSpeed g x y • roeShift g x y n) := ⟨rfl, rfl, rfl⟩

example (g : ℝ) (x y : E) (n : Vector 3) :
    dissipation g x y n = |dot (averageVelocity x y) n - soundSpeed g x y| • roeProjector g x y n 0 +
      |dot (averageVelocity x y) n| • roeProjector g x y n 1 +
      |dot (averageVelocity x y) n + soundSpeed g x y| • roeProjector g x y n 2 := by
  simp [dissipation, absolute, roeProjector, projector, speed, offset, sub_eq_add_neg]

example (g : ℝ) (x y : E) (n : Vector 3) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) (hn : dot n n = 1) :
    roeShift g x y n ^ 3 = soundSpeed g x y ^ 2 • roeShift g x y n := roe_cubic g x y n hg hx hy hn

example (g : ℝ) (x y : E) (n : Vector 3) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) (hn : dot n n = 1) (i j : Fin 3) :
    roeProjector g x y n i * roeProjector g x y n j =
      if i = j then roeProjector g x y n i else 0 := roe_projector_algebra g x y n hg hx hy hn i j

example (g : ℝ) (x y : E) (n : Vector 3) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) (hn : dot n n = 1) (i : Fin 3) :
    LinearMap.range (roeProjector g x y n i) =
      Module.End.eigenspace (roeMatrix g x y n).toLinearMap (roeSpeed g x y n i) ∧
    Module.finrank ℝ (Module.End.eigenspace (roeMatrix g x y n).toLinearMap (roeSpeed g x y n i)) =
      ![1, 3, 1] i := ⟨roe_projector_ranges g x y n hg hx hy hn i, roe_dimensions g x y n hg hx hy hn i⟩

example (g : ℝ) (x y : E) (n : Vector 3) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) (hn : dot n n = 1) :
    ∃ bas : Basis (Fin 5) ℝ E, ∀ j, ∃ i : Fin 3, roeMatrix g x y n (bas j) = roeSpeed g x y n i • bas j :=
  roe_complete_basis g x y n hg hx hy hn

example (g : ℝ) (x y : E) (n : Vector 3) (hg : 1 < g) (hn : dot n n = 1)
    (tb : Basis (Fin 2) ℝ (tangent n)) :
    Submodule.span ℝ ({contact (averageVelocity x y)} ∪ Set.range (fun i => shear (averageVelocity x y) (tb i))) =
      Module.End.eigenspace (roeMatrix g x y n).toLinearMap (dot (averageVelocity x y) n) :=
  roe_convective_tangent_span g x y n hg hn tb

example (n : Vector 3) (hn : dot n n = 1) :
    Module.finrank ℝ (tangent n) = 2 ∧ Nonempty (Basis (Fin 2) ℝ (tangent n)) :=
  ⟨tangent_dimension n hn, exists_tangent_basis n hn⟩

example (g : ℝ) (x y : E) (n : Vector 3) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) :
    roeProjector g x y n 0 + roeProjector g x y n 1 + roeProjector g x y n 2 = 1 ∧
    (roeMatrix g x y n).toLinearMap = roeSpeed g x y n 0 • roeProjector g x y n 0 +
      roeSpeed g x y n 1 • roeProjector g x y n 1 + roeSpeed g x y n 2 • roeProjector g x y n 2 :=
  ⟨roe_projector_sum g x y n hg hx hy, roe_spectral_decomposition g x y n hg hx hy⟩

example {ι : Type*} [Fintype ι] (g : ℝ) (x y : E) (n : Vector 3) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) (hn : dot n n = 1)
    (bas : Basis ι ℝ E) (speeds : ι → ℝ) (he : ∀ i, roeMatrix g x y n (bas i) = speeds i • bas i) :
    dissipation g x y n = bas.equivFun.symm.toLinearMap.comp
      ((diagonal (fun i => |speeds i|)).comp bas.equivFun.toLinearMap) :=
  roe_absolute_basis g x y n hg hx hy hn bas speeds he

example (g : ℝ) (x y : E) (n : Vector 3) (i : Fin 3) :
    roeMatrix g x y (-n) = -roeMatrix g x y n ∧
    roeProjector g x y (-n) i = roeProjector g x y n i.rev ∧
    dissipation g x y (-n) = dissipation g x y n :=
  ⟨roe_matrix_reverse g x y n, roe_projector_reverse g x y n i, roe_absolute_reverse g x y n⟩

example (g : ℝ) (x y : E) (n : Vector 3) :
    roeMatrix g y x n = roeMatrix g x y n ∧ dissipation g y x n = dissipation g x y n :=
  ⟨roeMatrix_swap g n x y, (roe_swap g x y n).2.2⟩

example : dissipation 2 (![1, 0, 0, 0, 1]) (![1, 0, 0, 0, 1]) (![1, 0, 0]) (![1, 0, 0, 0, 0]) = 0 := by
  generalize hxe : (![1, 0, 0, 0, 1] : E) = x
  generalize hne : (![1, 0, 0] : Vector 3) = n
  generalize hve : (![1, 0, 0, 0, 0] : E) = v
  have hx : (decode x).Admissible 2 := by
    rw [← hxe]
    norm_num [Conservative.Admissible, Conservative.pressure, decode, squareSum_three]
  have hn : dot n n = 1 := by rw [← hne]; norm_num [dot_three]
  have hv : v ≠ 0 := by
    rw [← hve]
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  have he : roeMatrix 2 x x n v = (0 : ℝ) • v := by
    rw [roeMatrix_diagonal 2 x n (by rw [← hxe]; norm_num), ← hxe, ← hne, ← hve]
    ext i
    fin_cases i <;> norm_num [jacobian, normalMomentum, normalIncrement, pressureDifferential,
      projection, velocity, enthalpy, coordinatePressure, Conservative.pressure, decode, squareSum_three, dot_three]
  simpa only [abs_zero, zero_smul] using roe_absolute_eigen 2 x x n (by norm_num) hx hx hn 0 v hv he

example : dissipation 2 (![1, 1, 0, 0, 1]) (![1, 1, 0, 0, 1]) (![1, 0, 0]) (![1, 0, 0, 0, 1 / 2]) = 0 := by
  generalize hxe : (![1, 1, 0, 0, 1] : E) = x
  generalize hne : (![1, 0, 0] : Vector 3) = n
  generalize hve : (![1, 0, 0, 0, 1 / 2] : E) = v
  have hx : (decode x).Admissible 2 := by
    rw [← hxe]
    norm_num [Conservative.Admissible, Conservative.pressure, decode, squareSum_three]
  have hn : dot n n = 1 := by rw [← hne]; norm_num [dot_three]
  have hv : v ≠ 0 := by
    rw [← hve]
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  have he : roeMatrix 2 x x n v = (0 : ℝ) • v := by
    rw [roeMatrix_diagonal 2 x n (by rw [← hxe]; norm_num), ← hxe, ← hne, ← hve]
    ext i
    fin_cases i <;> norm_num [jacobian, normalMomentum, normalIncrement, pressureDifferential,
      projection, velocity, enthalpy, coordinatePressure, Conservative.pressure, decode, squareSum_three, dot_three]
  simpa only [abs_zero, zero_smul] using roe_absolute_eigen 2 x x n (by norm_num) hx hx hn 0 v hv he

example (i : Fin 3) : Module.finrank ℝ
    (Module.End.eigenspace (roeMatrix 2 (![1, 0, 0, 0, 1]) (![1, 0, 0, 0, 1])
      (![2 / 7, 3 / 7, 6 / 7])).toLinearMap
      (roeSpeed 2 (![1, 0, 0, 0, 1]) (![1, 0, 0, 0, 1]) (![2 / 7, 3 / 7, 6 / 7]) i)) = ![1, 3, 1] i := by
  apply roe_dimensions
  · norm_num
  · norm_num [Conservative.Admissible, Conservative.pressure, decode, squareSum_three]
  · norm_num [Conservative.Admissible, Conservative.pressure, decode, squareSum_three]
  · norm_num [dot_three]

example (g : ℝ) (x y : E) (n : Vector 3) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) (hn : dot n n = 1)
    (s : ℝ) (hs : s = -soundSpeed g x y ∨ s = soundSpeed g x y) :
    let u := averageVelocity x y
    let H := averageEnthalpy g x y
    roeMatrix g x y n (![1, u 0 + s * n 0, u 1 + s * n 1, u 2 + s * n 2, H + s * dot u n]) =
      (dot u n + s) • (![1, u 0 + s * n 0, u 1 + s * n 1, u 2 + s * n 2, H + s * dot u n]) := by
  have h := (roe_eigenvectors g x y n hg hx hy hn).1 s hs
  have hv : acoustic (averageVelocity x y) (averageEnthalpy g x y) n s =
      ![1, averageVelocity x y 0 + s * n 0, averageVelocity x y 1 + s * n 1,
        averageVelocity x y 2 + s * n 2, averageEnthalpy g x y + s * dot (averageVelocity x y) n] := by
    funext i
    fin_cases i <;> simp [acoustic, vb, vp]
  rwa [hv] at h

example (g : ℝ) (x y : E) (n : Vector 3) (hg : 1 < g)
    (hx : (decode x).Admissible g) (hy : (decode y).Admissible g) (hn : dot n n = 1) :
    let u := averageVelocity x y
    roeMatrix g x y n (![1, u 0, u 1, u 2, squareSum u / 2]) =
      dot u n • (![1, u 0, u 1, u 2, squareSum u / 2]) ∧
    (∀ t : Vector 3, dot t n = 0 → roeMatrix g x y n (![0, t 0, t 1, t 2, dot u t]) =
      dot u n • (![0, t 0, t 1, t 2, dot u t])) :=
  (roe_eigenvectors g x y n hg hx hy hn).2

example : roeSpeed 2 (![1, 1, 0, 0, 1]) (![1, 1, 0, 0, 1]) (![1, 0, 0]) 0 = 0 := by
  norm_num [roeSpeed, speed, offset, averageVelocity, averageEnthalpy, soundSpeed, soundSquare,
    weight, root, velocity, enthalpy, coordinatePressure, Conservative.pressure, decode, squareSum_three, dot_three]
