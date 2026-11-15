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

namespace M2dChecks
noncomputable section
open CFDLean.Roe
attribute [local irreducible] CFDLean.Roe.Spectral.shift

example (g : ℝ) (U : Conservative 3) (S : Vector 3) :
    numericalFlux g U U S = physicalFlux g U S := numericalFlux_consistency g U S

example (g : ℝ) (U V : Conservative 3) (S : Vector 3) :
    numericalFlux g V U (-S) = ⟨-(numericalFlux g U V S).density,
      fun i => -(numericalFlux g U V S).momentum i, -(numericalFlux g U V S).energy⟩ :=
  numericalFlux_reverse g U V S

example (g : ℝ) (U V : Conservative 3) :
    numericalFlux g U V 0 = ⟨0, fun _ => 0, 0⟩ := numericalFlux_zero g U V

example (g a : ℝ) (U V : Conservative 3) (S : Vector 3) (ha : 0 ≤ a) :
    numericalFlux g U V (fun i => a * S i) = ⟨a * (numericalFlux g U V S).density,
      fun i => a * (numericalFlux g U V S).momentum i, a * (numericalFlux g U V S).energy⟩ :=
  numericalFlux_scale g a U V S ha

example (g : ℝ) (U V : Conservative 3) (S : Vector 3) (hg : 1 < g)
    (hU : U.Admissible g) (hV : V.Admissible g) (hS : S ≠ 0)
    (hup : soundSpeed g (encode U) (encode V) ≤ dot (averageVelocity (encode U) (encode V)) (unitNormal S)) :
    numericalFlux g U V S = physicalFlux g U S := numericalFlux_upwind_left g U V S hg hU hV hS hup

example (g : ℝ) (U V : Conservative 3) (S : Vector 3) (hg : 1 < g)
    (hU : U.Admissible g) (hV : V.Admissible g) (hS : S ≠ 0)
    (hup : dot (averageVelocity (encode U) (encode V)) (unitNormal S) ≤ -soundSpeed g (encode U) (encode V)) :
    numericalFlux g U V S = physicalFlux g V S := numericalFlux_upwind_right g U V S hg hU hV hS hup

example : encode witnessIntermediate = ![1 - 2 / Real.sqrt 3, 0, 0, 0, 5 / 2 - 2 * Real.sqrt 3] :=
  witness_intermediate_coordinates

example : witnessLeft.Admissible 2 ∧ witnessRight.Admissible 2 ∧
    0 < soundSquare 2 (encode witnessLeft) (encode witnessRight) ∧ witnessIntermediate.density < 0 :=
  positivity_counterexample

example (g : ℝ) (x y : StateCoordinates) (S : Vector 3) (hS : S ≠ 0) :
    roeFluxCoordinates g x y S = (1 / 2 : ℝ) •
      (encode (physicalFlux g (decode x) S) + encode (physicalFlux g (decode y) S)) -
      (Real.sqrt (squareSum S) / 2) •
        dissipation g x y (fun i => S i / Real.sqrt (squareSum S)) (y - x) := by
  rw [roeFluxCoordinates, if_neg hS]
  rfl

example : numericalFlux 2 ((Primitive.mk 2 ![3, 0, 0] 5).toConservative 2)
    ((Primitive.mk 2 ![3, 0, 0] 5).toConservative 2) ![4, 0, 0] = ⟨24, ![92, 0, 0], 228⟩ := by
  rw [numericalFlux_consistency]
  norm_num [physicalFlux, Primitive.toConservative, Conservative.pressure, dot_three, squareSum_three]
  funext i
  fin_cases i <;> norm_num

example : numericalFlux (7 / 5) ((Primitive.mk 2 ![3, -1, 0] 5).toConservative (7 / 5))
    ((Primitive.mk 2 ![3, -1, 0] 5).toConservative (7 / 5)) ![2, 3, 0] = ⟨6, ![28, 9, 0], 165 / 2⟩ := by
  rw [numericalFlux_consistency]
  norm_num [physicalFlux, Primitive.toConservative, Conservative.pressure, dot_three, squareSum_three]
  funext i
  fin_cases i <;> norm_num

-- All two-state controls start with M1 primitive conversion.
def contactLeft (u : ℝ) : Conservative 3 := (Primitive.mk 1 ![u, 0, 0] 1).toConservative 2
def contactRight (u : ℝ) : Conservative 3 := (Primitive.mk 4 ![u, 0, 0] 1).toConservative 2

theorem sqrt_four : Real.sqrt (4 : ℝ) = 2 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

attribute [local simp] sqrt_four

theorem contact_coordinates (u : ℝ) : encode (contactLeft u) = ![1, u, 0, 0, 1 + u ^ 2 / 2] ∧
    encode (contactRight u) = ![4, 4 * u, 0, 0, 1 + 2 * u ^ 2] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [contactLeft, contactRight, Primitive.toConservative, encode, squareSum_three]
  all_goals ring1

example : numericalFlux 2 (contactLeft 0) (contactRight 0) ![1, 0, 0] = ⟨0, ![1, 0, 0], 0⟩ := by
  generalize hxe : encode (contactLeft 0) = x
  generalize hye : encode (contactRight 0) = y
  have hx : (decode x).Admissible 2 := by
    rw [← hxe, decode_encode]
    norm_num [contactLeft, Primitive.toConservative, Conservative.Admissible, Conservative.pressure, squareSum_three]
  have hy : (decode y).Admissible 2 := by
    rw [← hye, decode_encode]
    norm_num [contactRight, Primitive.toConservative, Conservative.Admissible, Conservative.pressure, squareSum_three]
  have hn : unitNormal (![1, 0, 0] : Vector 3) = ![1, 0, 0] := by
    funext i
    fin_cases i <;> norm_num [unitNormal, area, squareSum_three]
  have he : roeMatrix 2 x y (unitNormal ![1, 0, 0]) (y - x) = 0 := by
    rw [← hxe, ← hye, (contact_coordinates 0).1, (contact_coordinates 0).2, hn]
    ext i
    fin_cases i <;> norm_num [roeMatrix, operator, assemble_eq_pi, normalMomentum, projection,
      averageVelocity, averageEnthalpy, weight, root, velocity, enthalpy, coordinatePressure,
      Conservative.pressure, decode, squareSum_three, dot_three]
  unfold numericalFlux
  rw [hxe, hye, roeFluxCoordinates_central_of_zero 2 x y _ (by norm_num) hx hy (by norm_num) he,
    ← hxe, ← hye, (contact_coordinates 0).1, (contact_coordinates 0).2]
  norm_num [coordinateFlux, physicalFlux, Conservative.pressure, decode, encode, squareSum_three, dot_three]

theorem contact_averages (u : ℝ) : averageVelocity (encode (contactLeft u)) (encode (contactRight u)) = ![u, 0, 0] ∧
    averageEnthalpy 2 (encode (contactLeft u)) (encode (contactRight u)) = 1 + u ^ 2 / 2 ∧
    soundSpeed 2 (encode (contactLeft u)) (encode (contactRight u)) = 1 := by
  rw [(contact_coordinates u).1, (contact_coordinates u).2]
  have hv : averageVelocity (![1, u, 0, 0, 1 + u ^ 2 / 2]) (![4, 4 * u, 0, 0, 1 + 2 * u ^ 2]) = ![u, 0, 0] := by
    funext i
    fin_cases i <;> norm_num [averageVelocity, weight, root, velocity, decode]
    all_goals ring1
  have hH : averageEnthalpy 2 (![1, u, 0, 0, 1 + u ^ 2 / 2]) (![4, 4 * u, 0, 0, 1 + 2 * u ^ 2]) = 1 + u ^ 2 / 2 := by
    norm_num [averageEnthalpy, weight, root, enthalpy, coordinatePressure, Conservative.pressure, decode, squareSum_three]
    ring1
  exact ⟨hv, hH, by norm_num [soundSpeed, soundSquare, hv, hH, squareSum_three]⟩

theorem contact_admissible (u : ℝ) : (contactLeft u).Admissible 2 ∧ (contactRight u).Admissible 2 := by
  constructor <;> constructor
  · norm_num [contactLeft, Primitive.toConservative]
  · norm_num [contactLeft, Primitive.toConservative, Conservative.pressure, squareSum_three]
  · norm_num [contactRight, Primitive.toConservative]
  · norm_num [contactRight, Primitive.toConservative, Conservative.pressure, squareSum_three]
    nlinarith

theorem unitNormal_two : unitNormal (![2, 0, 0] : Vector 3) = ![1, 0, 0] := by
  funext i
  fin_cases i <;> norm_num [unitNormal, area, squareSum_three]

example : numericalFlux 2 (contactLeft 1) (contactRight 1) ![2, 0, 0] = ⟨2, ![4, 0, 0], 5⟩ := by
  rw [numericalFlux_upwind_left 2 _ _ _ (by norm_num) (contact_admissible 1).1
    (contact_admissible 1).2 (by norm_num)
    (by rw [(contact_averages 1).1, (contact_averages 1).2.2, unitNormal_two]; norm_num [dot_three])]
  norm_num [physicalFlux, contactLeft, Primitive.toConservative, Conservative.pressure, squareSum_three, dot_three]
  funext i
  fin_cases i <;> norm_num

example : numericalFlux 2 (contactLeft (-1)) (contactRight (-1)) ![2, 0, 0] = ⟨-8, ![10, 0, 0], -8⟩ := by
  rw [numericalFlux_upwind_right 2 _ _ _ (by norm_num) (contact_admissible (-1)).1
    (contact_admissible (-1)).2 (by norm_num)
    (by rw [(contact_averages (-1)).1, (contact_averages (-1)).2.2, unitNormal_two]; norm_num [dot_three])]
  norm_num [physicalFlux, contactRight, Primitive.toConservative, Conservative.pressure, squareSum_three, dot_three]
  funext i
  fin_cases i <;> norm_num

example : numericalFlux 2 ((Primitive.mk 1 ![0, 1, 0] 1).toConservative 2)
    ((Primitive.mk 1 ![0, -1, 0] 1).toConservative 2) ![1, 0, 0] = ⟨0, ![1, 0, 0], 0⟩ := by
  generalize hxe : encode ((Primitive.mk 1 ![0, 1, 0] 1).toConservative 2) = x
  generalize hye : encode ((Primitive.mk 1 ![0, -1, 0] 1).toConservative 2) = y
  have hxc : x = ![1, 0, 1, 0, 3 / 2] := by
    rw [← hxe]
    norm_num [Primitive.toConservative, encode, squareSum_three]
  have hyc : y = ![1, 0, -1, 0, 3 / 2] := by
    rw [← hye]
    norm_num [Primitive.toConservative, encode, squareSum_three]
  have hx : (decode x).Admissible 2 := by
    rw [hxc]
    norm_num [Conservative.Admissible, Conservative.pressure, decode, squareSum_three]
  have hy : (decode y).Admissible 2 := by
    rw [hyc]
    norm_num [Conservative.Admissible, Conservative.pressure, decode, squareSum_three]
  have hn : unitNormal (![1, 0, 0] : Vector 3) = ![1, 0, 0] := by
    funext i
    fin_cases i <;> norm_num [unitNormal, area, squareSum_three]
  have he : roeMatrix 2 x y (unitNormal ![1, 0, 0]) (y - x) = 0 := by
    rw [hxc, hyc, hn]
    ext i
    fin_cases i <;> norm_num [roeMatrix, operator, assemble_eq_pi, normalMomentum, projection,
      averageVelocity, averageEnthalpy, weight, root, velocity, enthalpy, coordinatePressure,
      Conservative.pressure, decode, squareSum_three, dot_three]
  unfold numericalFlux
  rw [hxe, hye, roeFluxCoordinates_central_of_zero 2 x y _ (by norm_num) hx hy (by norm_num) he, hxc, hyc]
  norm_num [coordinateFlux, physicalFlux, Conservative.pressure, decode, encode, squareSum_three, dot_three]

end
end M2dChecks

namespace M3aChecks
noncomputable section
open CFDLean.Assembly
attribute [local irreducible] CFDLean.Roe.Spectral.shift
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

example {N E B : Type*} [DecidableEq N] (m : Interfaces N E B) (e : E) :
    incidence m (m.tail e) e = 1 ∧ incidence m (m.head e) e = -1 :=
  ⟨incidence_tail m e, incidence_head m e⟩

example {N E B : Type*} [Fintype N] [DecidableEq N] (m : Interfaces N E B) (e : E) :
    (∑ i, incidence m i e) = 0 ∧ (∀ i, incidence m i e = 1 ↔ i = m.tail e) ∧
      (∀ i, incidence m i e = -1 ↔ i = m.head e) :=
  ⟨incidence_sum m e, fun i => incidence_eq_one m i e, fun i => incidence_eq_neg_one m i e⟩

example {N E B : Type*} [Fintype N] [DecidableEq N] [Fintype E] [Fintype B]
    (m : Interfaces N E B) (f : E → StateCoordinates) (g : B → StateCoordinates) :
    ∑ i, residual m f g i = ∑ b, g b := global_balance m f g

example {N E B : Type*} [Fintype N] [DecidableEq N] [Fintype E] [Fintype B]
    (m : Interfaces N E B) (γ : ℝ) (U : N → Conservative 3) (S : E → Vector 3) (g : B → StateCoordinates) :
    ∑ i, residual m (fun e => encode (CFDLean.Roe.numericalFlux γ (U (m.tail e)) (U (m.head e)) (S e))) g i =
      ∑ b, g b := roe_global_balance m γ U S g

example {N E B : Type*} [DecidableEq N] (m : Interfaces N E B) (γ : ℝ)
    (U : N → Conservative 3) (S : E → Vector 3) (i : N) (e : E) :
    (if m.tail e = i then encode (CFDLean.Roe.numericalFlux γ (U (m.tail e)) (U (m.head e)) (S e))
      else if m.head e = i then encode (CFDLean.Roe.numericalFlux γ (U (m.head e)) (U (m.tail e)) (-S e)) else 0) =
      incidence m i e • roeTransfer m γ U S e := outwardTransfer_eq m γ U S i e

example {N E B : Type*} [DecidableEq N] [Fintype E] [Fintype B]
    (m : Interfaces N E B) (rev : E → Prop) [DecidablePred rev] (γ : ℝ) (U : N → Conservative 3)
    (S : E → Vector 3) (g : B → StateCoordinates) (i : N) :
    residual (m.reverse rev) (roeTransfer (m.reverse rev) γ U (fun e => if rev e then -S e else S e)) g i =
      residual m (roeTransfer m γ U S) g i := roe_residual_reverse m rev γ U S g i

example {N E B N' E' B' : Type*} [DecidableEq N] [DecidableEq N']
    [Fintype E] [Fintype E'] [Fintype B] [Fintype B']
    (m : Interfaces N E B) (n : N ≃ N') (e : E ≃ E') (b : B ≃ B') (γ : ℝ)
    (U : N → Conservative 3) (S : E → Vector 3) (g : B → StateCoordinates) (i : N) :
    residual (m.reindex n e b) (roeTransfer (m.reindex n e b) γ (fun j => U (n.symm j)) (fun j => S (e.symm j)))
      (fun j => g (b.symm j)) (n i) = residual m (roeTransfer m γ U S) g i :=
  roe_residual_reindex m n e b γ U S g i

example {N E B : Type*} [DecidableEq N] [Fintype E] [Fintype B]
    (m : Interfaces N E B) (γ : ℝ) (U : Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (i : N)
    (_hγ : 1 < γ) (_hU : U.Admissible γ) :
    residual m (roeTransfer m γ (fun _ => U) S) (fun b => encode (physicalFlux γ U (T b))) i =
      encode (physicalFlux γ U (metricDefect m S T i)) := constant_state_residual m γ U S T i

example {N E B : Type*} [DecidableEq N] [Fintype E] [Fintype B]
    (m : Interfaces N E B) (γ : ℝ) (U : Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (i : N)
    (h : metricDefect m S T i = 0) :
    residual m (roeTransfer m γ (fun _ => U) S) (fun b => encode (physicalFlux γ U (T b))) i = 0 :=
  constant_state_closed m γ U S T i h

example {N E B : Type*} (m : Interfaces N E B) (γ : ℝ) (U : N → Conservative 3) (e : E) :
    roeTransfer m γ U (fun _ => 0) e = 0 := roeTransfer_zero m γ U _ e rfl

example {N E B : Type*} [DecidableEq N] [Fintype E] [Fintype B]
    (m : Interfaces N E B) (f : E → StateCoordinates) (g : B → StateCoordinates) (i : N) :
    residual m f g i = (∑ e ∈ Finset.univ.filter (fun e => m.tail e = i), f e) -
      (∑ e ∈ Finset.univ.filter (fun e => m.head e = i), f e) +
      ∑ b ∈ Finset.univ.filter (fun b => m.owner b = i), g b := residual_outgoing m f g i

def oneEdge : Interfaces (Fin 2) (Fin 1) (Fin 0) where
  tail _ := 0
  head _ := 1
  distinct _ := by decide
  owner := Fin.elim0

example (i : Fin 2) : residual oneEdge (fun _ => (![24, 92, 0, 0, 228] : StateCoordinates))
    Fin.elim0 i = if i = 0 then ![24, 92, 0, 0, 228] else ![-24, -92, 0, 0, -228] := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [residual, incidence, oneEdge, Fin.sum_univ_succ]

def cycle : Interfaces (Fin 3) (Fin 3) (Fin 1) where
  tail := id
  head := ![1, 2, 0]
  distinct i := by fin_cases i <;> decide
  owner _ := 2

def cycleFlux : Fin 3 → StateCoordinates := ![![1, 2, 3, 4, 5], ![2, -1, 4, 0, 3], ![-3, 2, 1, 5, -1]]

example (i : Fin 3) : residual cycle cycleFlux (fun _ => ![1, 0, 0, 0, 0]) i =
    (![![4, 0, 2, -1, 6], ![1, -3, 1, -4, -2], ![-4, 3, -3, 5, -4]] : Fin 3 → StateCoordinates) i := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases i
  · ext j
    fin_cases j <;> norm_num [residual, incidence, cycle, cycleFlux, Fin.sum_univ_succ, h20, h21, Ne.symm h20, Ne.symm h21]
  · ext j
    fin_cases j <;> norm_num [residual, incidence, cycle, cycleFlux, Fin.sum_univ_succ, h20, h21, Ne.symm h20, Ne.symm h21]
  · change residual cycle cycleFlux (fun _ => ![1, 0, 0, 0, 0]) (2 : Fin 3) = ![-4, 3, -3, 5, -4]
    ext j
    fin_cases j <;> norm_num [residual, incidence, cycle, cycleFlux, Fin.sum_univ_succ, h20, h21, Ne.symm h20, Ne.symm h21]

def closedPair : Interfaces (Fin 2) (Fin 1) (Fin 2) where
  tail _ := 0
  head _ := 1
  distinct _ := by decide
  owner := id

def resting : Conservative 3 := (Primitive.mk 1 ![0, 0, 0] 1).toConservative 2
def pairArea : Fin 1 → Vector 3 := fun _ => ![1, 0, 0]
def pairBoundary (b : Fin 2) : Vector 3 := if b = 0 then ![-1, 0, 0] else ![1, 0, 0]

theorem pair_closed (i : Fin 2) : metricDefect closedPair pairArea pairBoundary i = 0 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [metricDefect, residual, incidence, closedPair, pairArea, pairBoundary, Fin.sum_univ_succ]

example : resting.Admissible 2 := by
  norm_num [resting, Primitive.toConservative, Conservative.Admissible, Conservative.pressure, squareSum_three]

example (i : Fin 2) : residual closedPair (roeTransfer closedPair 2 (fun _ => resting) pairArea)
    (fun b => physicalTransfer 2 resting (pairBoundary b)) i = 0 :=
  constant_state_closed closedPair 2 resting pairArea pairBoundary i (pair_closed i)

def incompatibleBoundary (b : Fin 2) : StateCoordinates :=
  physicalTransfer 2 resting (pairBoundary b) + if b = 0 then ![1, 0, 0, 0, 0] else 0

theorem incompatible_actual_roe : residual closedPair (roeTransfer closedPair 2 (fun _ => resting) pairArea)
    incompatibleBoundary 0 = ![1, 0, 0, 0, 0] := by
  have hf : roeTransfer closedPair 2 (fun _ => resting) pairArea =
      fun e => physicalTransfer 2 resting (pairArea e) := by
    funext e
    exact roeTransfer_consistency closedPair 2 resting pairArea e
  rw [hf]
  ext j
  fin_cases j <;> norm_num [residual, incidence, closedPair, pairArea, pairBoundary, incompatibleBoundary,
    physicalTransfer, resting, physicalFlux, Primitive.toConservative, Conservative.pressure,
    encode, squareSum_three, dot_three, Fin.sum_univ_succ]

example : residual closedPair (roeTransfer closedPair 2 (fun _ => resting) pairArea) incompatibleBoundary 0 ≠ 0 := by
  rw [incompatible_actual_roe]
  intro h
  have hh := congrFun h 0
  norm_num at hh

example : residual (closedPair.reindex (Equiv.swap 0 1) (Equiv.refl _) (Equiv.swap 0 1))
    (roeTransfer (closedPair.reindex (Equiv.swap 0 1) (Equiv.refl _) (Equiv.swap 0 1)) 2
      (fun _ => resting) (fun e => pairArea ((Equiv.refl _).symm e)))
    (fun b => incompatibleBoundary ((Equiv.swap 0 1).symm b)) 1 = ![1, 0, 0, 0, 0] := by
  have h := roe_residual_reindex closedPair (Equiv.swap 0 1) (Equiv.refl _) (Equiv.swap 0 1)
    2 (fun _ => resting) pairArea incompatibleBoundary 0
  simpa only [Equiv.swap_apply_left] using h.trans incompatible_actual_roe

end
end M3aChecks

namespace M3bChecks
noncomputable section
open CFDLean.MedianDual CFDLean.MedianDual.MeshData
open CFDLean.Assembly

example (p : Points) : ∑ i, faceVector p i = 0 := faceVector_sum p
example (p : Points) (i : Fin 4) :
    (∑ j, localInterface p i j) + ∑ j, localPatch p j i = 0 := local_closure p i
example (p : Points) (i j k l : Fin 4) (h : valid i j k l) :
    dot (outwardTriangle p i j k l) (p j - p i) = sixVolume p / 24 := outwardTriangle_dot p i j k l h
example (p : Points) (i j k l : Fin 4) (h : valid i j k l) :
    volume (flagPoints p i j k l) = volume p / 24 := flag_volume p i j k l h
example (p : Points) (i : Fin 4) : localDualVolume p i = volume p / 4 := localDualVolume_eq p i
example : Fintype.card (Σ i : Fin 4, VertexFlags i) = 24 := flag_card
example (i : Fin 4) : Fintype.card (VertexFlags i) = 6 := vertexFlags_card i
example {n m : ℕ} (M : MeshData n m) (a : Fin n) :
    M.dualVolume a = ∑ t, if a ∈ M.cellNodes t then volume (M.points t) / 4 else 0 := M.dualVolume_formula a
example {n m : ℕ} (M : MeshData n m) (a : Fin n) (ha : M.Used a) : 0 < M.dualVolume a := M.dualVolume_pos a ha
example {n m : ℕ} (M : MeshData n m) (a : Fin n) (ha : ¬M.Used a) : M.dualVolume a = 0 := M.dualVolume_unused a ha
example {n m : ℕ} (M : MeshData n m) (h : M.Conforming) :
    ∑ a, M.dualVolume a = ∑ t, volume (M.points t) := M.volume_partition h
example {n m : ℕ} (M : MeshData n m) (e : M.Edge) :
    e.1.1 < e.1.2 ∧ ∃ t, e.1.1 ∈ M.cellNodes t ∧ e.1.2 ∈ M.cellNodes t := e.prop
example {n m : ℕ} (M : MeshData n m) : Function.Injective M.boundaryKey := M.boundaryKey_injective
example {n m : ℕ} (M : MeshData n m) (F : Finset (Fin n)) (a : Fin n) :
    (∃ b : M.Boundary, M.boundaryKey b = (F,a)) ↔ M.faceCount F = 1 ∧ a ∈ F := M.boundaryKey_range F a
example {n m : ℕ} (M : MeshData n m) (h : M.Conforming) (a : Fin n) :
    metricDefect M.interfaces M.edgeArea M.boundaryArea a = 0 := M.metric_closed h a
example {n m : ℕ} (M : MeshData n m) (h : M.Conforming) (γ : ℝ) (U : Conservative 3)
    (_hγ : 1 < γ) (_hU : U.Admissible γ) (a : Fin n) :
    residual M.interfaces (roeTransfer M.interfaces γ (fun _ => U) M.edgeArea)
      (fun b => encode (physicalFlux γ U (M.boundaryArea b))) a = 0 := M.constant_state h γ U a
example {n m : ℕ} (M : MeshData n m) (γ : ℝ) (U : Fin n → Conservative 3) (g : M.Boundary → StateCoordinates) :
    (∑ a, residual M.interfaces (roeTransfer M.interfaces γ U M.edgeArea) g a) = ∑ b, g b := M.roe_boundary_balance γ U g
example : Controls.standard.Conforming := Controls.standard_conforming
example : Controls.oblique.Conforming := Controls.oblique_conforming
example : Controls.twoCells.Conforming := Controls.two_cells_conforming
example (a : Fin 4) : Controls.standard.dualVolume a = 1/24 := Controls.standard_volume a
example : localInterface Controls.standardPoints 0 1 = ![1/12,1/24,1/24] := Controls.standard_local_area
example : Controls.standard.assembledArea 0 1 = ![1/12,1/24,1/24] := Controls.standard_assembled_area
example (i j k l : Fin 4) (h : valid i j k l) :
    volume (flagPoints Controls.standardPoints i j k l) = 1/144 := Controls.standard_flags i j k l h
example (i j k l : Fin 4) (h : valid i j k l) :
    volume (flagPoints Controls.obliquePoints i j k l) = volume Controls.obliquePoints / 24 := Controls.oblique_flags i j k l h
example (a : Fin 4) : metricDefect Controls.standard.interfaces Controls.standard.edgeArea Controls.standard.boundaryArea a = 0 := Controls.standard_closed a
example (a : Fin 4) : metricDefect Controls.oblique.interfaces Controls.oblique.edgeArea Controls.oblique.boundaryArea a = 0 := Controls.oblique_closed a
example (a : Fin 5) : metricDefect Controls.twoCells.interfaces Controls.twoCells.edgeArea Controls.twoCells.boundaryArea a = 0 := Controls.two_cells_closed a
example (a : Fin 5) : Controls.twoCells.dualVolume a = if a.val < 3 then 1/12 else 1/24 := Controls.two_cells_volume a
example : (∑ a, Controls.twoCells.dualVolume a) = 1/3 := Controls.two_cells_total_volume
example : Controls.twoCells.assembledArea 0 1 = ![1/6,1/12,0] := Controls.two_cells_assembled_area
example (i : Fin 5) : Controls.twoCells.ownedPatch (0,3) i + Controls.twoCells.ownedPatch (1,3) i = 0 := Controls.shared_patches_cancel i
example : Controls.resting.Admissible 2 := Controls.resting_admissible
example (a : Fin 4) : residual Controls.standard.interfaces
    (roeTransfer Controls.standard.interfaces 2 (fun _ => Controls.resting) Controls.standard.edgeArea)
    (fun b => physicalTransfer 2 Controls.resting (Controls.standard.boundaryArea b)) a = 0 := Controls.compatible_standard a
example : residual Controls.standard.interfaces
    (roeTransfer Controls.standard.interfaces 2 (fun _ => Controls.resting) Controls.standard.edgeArea)
    (fun b => physicalTransfer 2 Controls.resting (Controls.standard.boundaryArea b) +
      if b = Controls.standardBoundary then (![1,0,0,0,0] : StateCoordinates) else 0) 0 ≠ 0 := Controls.incompatible_standard
example : ¬ (0 < sixVolume (fun _ : Fin 4 => (0 : Vector 3))) := Controls.degenerate_excluded
example {n m : ℕ} (M : MeshData n m) (F : Finset (Fin n)) (h : 3 ≤ M.faceCount F) : ¬ M.Conforming := Controls.nonmanifold_excluded M F h
example : (decode RoeAggregation.cold).Admissible 2 ∧ (decode RoeAggregation.hot).Admissible 2 := RoeAggregation.states_admissible
example : CFDLean.Roe.roeFluxCoordinates 2 RoeAggregation.cold RoeAggregation.hot (![1,1,0] : Vector 3) ≠
    CFDLean.Roe.roeFluxCoordinates 2 RoeAggregation.cold RoeAggregation.hot (![1,0,0] : Vector 3) +
    CFDLean.Roe.roeFluxCoordinates 2 RoeAggregation.cold RoeAggregation.hot (![0,1,0] : Vector 3) := RoeAggregation.nonparallel_not_additive

end
end M3bChecks

namespace M4aChecks
noncomputable section
open CFDLean.Boundary

example : Kind.slipWall ≠ Kind.inviscidSymmetryTraction := by decide
example (γ : ℝ) (U V : Conservative 3) (T : Vector 3) :
    transfer γ .slipWall U V T = transfer γ .inviscidSymmetryTraction U V T := rfl
example (γ : ℝ) (U : Conservative 3) (T : Vector 3) :
    wallTransfer γ U T 0 = 0 ∧ wallTransfer γ U T 4 = 0 := ⟨wall_mass γ U T, wall_energy γ U T⟩
example (γ : ℝ) (U : Conservative 3) (T : Vector 3) (i : Fin 3) :
    (decode (wallTransfer γ U T)).momentum i = U.pressure γ * T i := wall_momentum γ U T i
example (γ : ℝ) (U : Conservative 3) : wallTransfer γ U 0 = 0 := wall_zero γ U
example (γ : ℝ) (U : Conservative 3) (S T : Vector 3) :
    wallTransfer γ U (S+T) = wallTransfer γ U S + wallTransfer γ U T := wall_add γ U S T
example (γ a : ℝ) (U : Conservative 3) (T : Vector 3) :
    wallTransfer γ U (a • T) = a • wallTransfer γ U T := wall_smul γ a U T
example (γ : ℝ) (U : Conservative 3) (T : Vector 3) :
    wallTransfer γ U (-T) = -wallTransfer γ U T := wall_reverse γ U T
example (γ : ℝ) (U : Conservative 3) (hU : U.Admissible γ) : 0 < U.pressure γ := wall_pressure_pos γ U hU
example (γ : ℝ) (U : Conservative 3) (T : Vector 3) :
    wallTransfer γ U T = encode (physicalFlux γ U T) ↔ dot U.momentum T = 0 := wall_eq_physical_iff γ U T
example (γ : ℝ) (U : Conservative 3) (T : Vector 3) (hρ : 0 < U.density) (hT : T ≠ 0) :
    wallTransfer γ U T = encode (physicalFlux γ U T) ↔
      dot (fun i => U.momentum i / U.density) (unitNormal T) = 0 := wall_eq_physical_iff_normalVelocity γ U T hρ hT
example (γ : ℝ) (U : Conservative 3) (T : Vector 3) :
    encode (CFDLean.Roe.numericalFlux γ U U T) = encode (physicalFlux γ U T) := prescribed_consistency γ U T
example (γ : ℝ) (U V : Conservative 3) : prescribedExteriorRoeTransfer γ U V 0 = 0 := prescribed_zero γ U V
example (γ a : ℝ) (U V : Conservative 3) (T : Vector 3) (ha : 0 ≤ a) :
    prescribedExteriorRoeTransfer γ U V (a • T) = a • prescribedExteriorRoeTransfer γ U V T := prescribed_scale γ a U V T ha
example (γ : ℝ) (U V : Conservative 3) (T : Vector 3) :
    encode (CFDLean.Roe.numericalFlux γ V U (-T)) = -encode (CFDLean.Roe.numericalFlux γ U V T) := prescribed_reverse γ U V T
example (γ : ℝ) (U V : Conservative 3) (T : Vector 3) (hγ : 1 < γ)
    (hU : U.Admissible γ) (hV : V.Admissible γ) (hT : T ≠ 0)
    (hup : CFDLean.Roe.soundSpeed γ (encode U) (encode V) ≤
      dot (CFDLean.Roe.averageVelocity (encode U) (encode V)) (unitNormal T)) :
    encode (CFDLean.Roe.numericalFlux γ U V T) = encode (physicalFlux γ U T) := prescribed_upwind_owner γ U V T hγ hU hV hT hup
example (γ : ℝ) (U V : Conservative 3) (T : Vector 3) (hγ : 1 < γ)
    (hU : U.Admissible γ) (hV : V.Admissible γ) (hT : T ≠ 0)
    (hup : dot (CFDLean.Roe.averageVelocity (encode U) (encode V)) (unitNormal T) ≤
      -CFDLean.Roe.soundSpeed γ (encode U) (encode V)) :
    encode (CFDLean.Roe.numericalFlux γ U V T) = encode (physicalFlux γ V T) := prescribed_upwind_exterior γ U V T hγ hU hV hT hup
example {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) (b c : M.Boundary)
    (hf : primalFace M b = primalFace M c) (hi : M.interfaces.owner b = M.interfaces.owner c) : b = c := boundary_record_unique M b c hf hi
example {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) (F : Finset (Fin n)) (i : Fin n) :
    (∃ b : M.Boundary, primalFace M b = F ∧ M.interfaces.owner b = i) ↔ M.faceCount F = 1 ∧ i ∈ F := boundary_record_range M F i
example {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (b c : M.Boundary) (h : primalFace M b = primalFace M c) :
    patchKind M k b = patchKind M k c ∧ patchExterior M V b = patchExterior M V c :=
  ⟨patchKind_coherent M k b c h, patchExterior_coherent M V b c h⟩
example {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (b : M.Boundary)
    (h : patchKind M k b = .slipWall) :
    patchTransfer M γ k V U b = wallTransfer γ (U (M.interfaces.owner b)) (M.boundaryArea b) := patchTransfer_wall M γ k V U b h
example {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (b : M.Boundary)
    (h : patchKind M k b = .inviscidSymmetryTraction) :
    patchTransfer M γ k V U b = wallTransfer γ (U (M.interfaces.owner b)) (M.boundaryArea b) := patchTransfer_symmetry M γ k V U b h
example {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (b : M.Boundary)
    (h : patchKind M k b = .prescribedExteriorRoe) :
    patchTransfer M γ k V U b = encode (CFDLean.Roe.numericalFlux γ (U (M.interfaces.owner b))
      (patchExterior M V b) (M.boundaryArea b)) := patchTransfer_prescribed M γ k V U b h

example : Controls.obliqueOwner.Admissible 2 := Controls.oblique_admissible
example : wallTransfer 2 Controls.obliqueOwner Controls.obliqueArea = ![0,9,12,0,0] := Controls.oblique_traction
example : wallTransfer 2 Controls.obliqueOwner Controls.obliqueArea = encode (physicalFlux 2 Controls.obliqueOwner Controls.obliqueArea) := Controls.oblique_physical
example : (Controls.moving 1 1).Admissible 2 := Controls.moving_admissible _ _ (by norm_num)
example : wallTransfer 2 (Controls.moving 1 1) (![0,0,-1/6] : Vector 3) =
    encode (physicalFlux 2 (Controls.moving 1 1) (![0,0,-1/6] : Vector 3)) := by
  apply (wall_eq_physical_iff _ _ _).mpr
  norm_num [dot_three, Controls.moving]
example : wallTransfer 2 (Controls.moving 1 1) Controls.axis ≠ encode (physicalFlux 2 (Controls.moving 1 1) Controls.axis) := Controls.normal_flow_incompatible
example : Controls.reflectedOwner.Admissible 2 ∧ Controls.reflectedExterior.Admissible 2 := by
  constructor <;> apply Controls.moving_admissible <;> norm_num
example : prescribedExteriorRoeTransfer 2 Controls.reflectedOwner Controls.reflectedExterior Controls.axis = ![0,19/4,0,0,0] := Controls.reflected_roe
example : prescribedExteriorRoeTransfer 2 Controls.reflectedOwner Controls.reflectedExterior Controls.axis ≠ wallTransfer 2 Controls.reflectedOwner Controls.axis := Controls.reflected_not_wall
example : wallTransfer 2 (Controls.moving 0 1) Controls.axis ≠
    pressureTransfer ((6*(Controls.moving 0 1).pressure 2+(Controls.moving 0 2).pressure 2+(Controls.moving 0 4).pressure 2)/8) Controls.axis := Controls.owner_sampling_differs
example : prescribedExteriorRoeTransfer 2 (Controls.moving 3 1) (Controls.moving 3 3) Controls.axis = ![3,10,0,0,39/2] := Controls.strict_outflow
example : prescribedExteriorRoeTransfer 2 (Controls.moving (-3) 1) (Controls.moving (-3) 3) Controls.axis = ![-3,12,0,0,-63/2] := Controls.strict_inflow
example : prescribedExteriorRoeTransfer 2 (Controls.moving 2 1) (Controls.moving 2 3) Controls.axis = ![2,5,0,0,8] := Controls.sonic_outflow
example : prescribedExteriorRoeTransfer 2 (Controls.moving (-2) 1) (Controls.moving (-2) 3) Controls.axis = ![-2,7,0,0,-16] := Controls.sonic_inflow
example : prescribedExteriorRoeTransfer 2 (Controls.moving 0 1) (Controls.moving 0 3) Controls.axis = ![-1/2,2,0,0,-2] := Controls.mismatching_exterior
example : Controls.standard.interfaces.owner Controls.wallPatch = Controls.standard.interfaces.owner Controls.openPatch ∧
    patchKind Controls.standard Controls.mixedKinds Controls.wallPatch = .slipWall ∧
    patchKind Controls.standard Controls.mixedKinds Controls.openPatch = .prescribedExteriorRoe := Controls.mixed_corner
example : patchTransfer Controls.standard 2 Controls.mixedKinds (fun _ => Controls.moving 0 1)
    (fun _ => Controls.moving 0 1) Controls.wallPatch = ![0,0,0,-1/6,0] := Controls.wall_patch_transfer
example : patchTransfer Controls.standard 2 Controls.mixedKinds (fun _ => Controls.moving 0 1)
    (fun _ => Controls.moving 0 1) Controls.openPatch = ![0,-1/6,0,0,0] := Controls.open_patch_transfer

end
end M4aChecks

namespace M4bChecks
noncomputable section
open CFDLean.Boundary

example {N E B : Type*} [Fintype N] [DecidableEq N] [Fintype E] [Fintype B]
    (m : CFDLean.Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind) (V : B → Conservative 3)
    (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) :
    (∑ i, stationaryResidual m γ k V U S T i) = ∑ b, transfer γ (k b) (U (m.owner b)) (V b) (T b) :=
  stationary_global_balance m γ k V U S T
example {N E B : Type*} [Fintype N] [DecidableEq N] [Fintype E] [Fintype B]
    (m : CFDLean.Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind) (V : B → Conservative 3)
    (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) :
    (∑ i, stationaryResidual m γ k V U S T i) =
      (∑ b, if k b = .prescribedExteriorRoe then encode (CFDLean.Roe.numericalFlux γ (U (m.owner b)) (V b) (T b)) else 0) +
      ∑ b, if k b = .prescribedExteriorRoe then 0 else wallTransfer γ (U (m.owner b)) (T b) := stationary_mixed_balance m γ k V U S T
example {N E B : Type*} [Fintype N] [DecidableEq N] [Fintype E] [Fintype B]
    (m : CFDLean.Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind) (V : B → Conservative 3)
    (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) :
    (∑ i, stationaryResidual m γ k V U S T i 0) =
      ∑ b, if k b = .prescribedExteriorRoe then prescribedExteriorRoeTransfer γ (U (m.owner b)) (V b) (T b) 0 else 0 := stationary_mass_balance m γ k V U S T
example {N E B : Type*} [Fintype N] [DecidableEq N] [Fintype E] [Fintype B]
    (m : CFDLean.Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind) (V : B → Conservative 3)
    (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) :
    (∑ i, stationaryResidual m γ k V U S T i 4) =
      ∑ b, if k b = .prescribedExteriorRoe then prescribedExteriorRoeTransfer γ (U (m.owner b)) (V b) (T b) 4 else 0 := stationary_energy_balance m γ k V U S T
example {N E B : Type*} [Fintype N] [DecidableEq N] [Fintype E] [Fintype B]
    (m : CFDLean.Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind) (V : B → Conservative 3)
    (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (j : Fin 3) :
    (∑ i, (decode (stationaryResidual m γ k V U S T i)).momentum j) =
      ∑ b, if k b = .prescribedExteriorRoe then
        (decode (prescribedExteriorRoeTransfer γ (U (m.owner b)) (V b) (T b))).momentum j else (U (m.owner b)).pressure γ * T b j := stationary_momentum_balance m γ k V U S T j

example {N E B N' E' B' : Type*} [DecidableEq N] [DecidableEq N'] [Fintype E] [Fintype E'] [Fintype B] [Fintype B']
    (m : CFDLean.Assembly.Interfaces N E B) (n : N ≃ N') (e : E ≃ E') (b : B ≃ B') (γ : ℝ)
    (k : B → Kind) (V : B → Conservative 3) (U : N → Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (i : N) :
    stationaryResidual (m.reindex n e b) γ (fun x => k (b.symm x)) (fun x => V (b.symm x))
      (fun x => U (n.symm x)) (fun x => S (e.symm x)) (fun x => T (b.symm x)) (n i) =
      stationaryResidual m γ k V U S T i := stationary_residual_reindex m n e b γ k V U S T i
example (γ : ℝ) (k : Kind) (U V : Conservative 3) (T : Vector 3)
    (hWall : k ≠ .prescribedExteriorRoe → dot U.momentum T = 0)
    (hMatch : k = .prescribedExteriorRoe → V = U) :
    transfer γ k U V T = encode (physicalFlux γ U T) := transfer_compatible γ k U V T hWall hMatch
example {N E B : Type*} [DecidableEq N] [Fintype E] [Fintype B]
    (m : CFDLean.Assembly.Interfaces N E B) (γ : ℝ) (k : B → Kind) (V : B → Conservative 3)
    (U : Conservative 3) (S : E → Vector 3) (T : B → Vector 3) (i : N)
    (hWall : ∀ b, k b ≠ .prescribedExteriorRoe → dot U.momentum (T b) = 0)
    (hMatch : ∀ b, k b = .prescribedExteriorRoe → V b = U) :
    stationaryResidual m γ k V (fun _ => U) S T i = encode (physicalFlux γ U (CFDLean.Assembly.metricDefect m S T i)) := stationary_common_defect m γ k V U S T i hWall hMatch
example {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) (i : Fin n) :
    meshResidual M γ k V U i = CFDLean.Assembly.residual M.interfaces
      (CFDLean.Assembly.roeTransfer M.interfaces γ U M.edgeArea) (patchTransfer M γ k V U) i := meshResidual_eq M γ k V U i
example {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) (γ : ℝ) (k : Finset (Fin n) → Kind)
    (V : Finset (Fin n) → Conservative 3) (U : Fin n → Conservative 3) :
    (∑ i, meshResidual M γ k V U i) = ∑ b, patchTransfer M γ k V U b := mesh_global_balance M γ k V U
example {n m : ℕ} (M : CFDLean.MedianDual.MeshData n m) (hM : M.Conforming) (γ : ℝ) (hγ : 1 < γ)
    (U : Conservative 3) (hU : U.Admissible γ) (k : Finset (Fin n) → Kind) (V : Finset (Fin n) → Conservative 3) (i : Fin n)
    (hWall : ∀ b : M.Boundary, patchKind M k b ≠ .prescribedExteriorRoe → dot U.momentum (M.boundaryArea b) = 0)
    (hMatch : ∀ b : M.Boundary, patchKind M k b = .prescribedExteriorRoe → patchExterior M V b = U) :
    meshResidual M γ k V (fun _ => U) i = 0 := mesh_constant_state M hM γ hγ U hU k V i hWall hMatch

example (q : ℝ) (i : Fin 4) : meshResidual AssemblyControls.standard 2 AssemblyControls.mixedKinds
    (fun _ => Controls.moving q 1) (fun _ => Controls.moving q 1) i = 0 := AssemblyControls.standard_mixed_common q i
example (V : Finset (Fin 4) → Conservative 3) (i : Fin 4) :
    meshResidual AssemblyControls.standard 2 (fun _ => .slipWall) V (fun _ => Controls.moving 0 1) i = 0 := AssemblyControls.standard_all_wall_rest V i
example (V : Finset (Fin 4) → Conservative 3) (i : Fin 4) :
    meshResidual CFDLean.MedianDual.Controls.oblique 2 (fun _ => .inviscidSymmetryTraction) V (fun _ => Controls.moving 0 1) i = 0 := AssemblyControls.oblique_all_symmetry_rest V i
example : AssemblyControls.normalState.Admissible 2 := AssemblyControls.normal_admissible
example : meshResidual AssemblyControls.standard 2 AssemblyControls.mixedKinds (fun _ => AssemblyControls.normalState)
    (fun _ => AssemblyControls.normalState) 0 = ![1/6,0,0,1/6,5/12] := AssemblyControls.incompatible_wall_residual
example : meshResidual AssemblyControls.standard 2 AssemblyControls.mixedKinds (fun _ => AssemblyControls.normalState)
    (fun _ => AssemblyControls.normalState) 0 ≠ 0 := by
  rw [AssemblyControls.incompatible_wall_residual]
  intro h
  have hh := congrFun h 0
  norm_num at hh
example (F : Finset (Fin 4)) : (AssemblyControls.mismatchingData F).Admissible 2 := AssemblyControls.mismatching_data_admissible F
example : meshResidual AssemblyControls.standard 2 AssemblyControls.mixedKinds AssemblyControls.mismatchingData
    (fun _ => Controls.moving 0 1) 0 = ![-1/12,-1/6,0,0,-1/3] := AssemblyControls.incompatible_exterior_residual
example : meshResidual AssemblyControls.standard 2 AssemblyControls.mixedKinds AssemblyControls.mismatchingData
    (fun _ => Controls.moving 0 1) 0 ≠ 0 := by
  rw [AssemblyControls.incompatible_exterior_residual]
  intro h
  have hh := congrFun h 0
  norm_num at hh
example (q : ℝ) (i : Fin 5) : meshResidual AssemblyControls.twoCells 2 AssemblyControls.twoKinds
    (fun _ => Controls.moving q 1) (fun _ => Controls.moving q 1) i = 0 := AssemblyControls.two_cell_common q i
example : AssemblyControls.twoCells.interfaces.owner AssemblyControls.twoWall = AssemblyControls.twoCells.interfaces.owner AssemblyControls.twoSymmetry ∧
    AssemblyControls.twoCells.interfaces.owner AssemblyControls.twoWall = AssemblyControls.twoCells.interfaces.owner AssemblyControls.twoOpen ∧
    patchKind AssemblyControls.twoCells AssemblyControls.twoKinds AssemblyControls.twoWall = .slipWall ∧
    patchKind AssemblyControls.twoCells AssemblyControls.twoKinds AssemblyControls.twoSymmetry = .inviscidSymmetryTraction ∧
    patchKind AssemblyControls.twoCells AssemblyControls.twoKinds AssemblyControls.twoOpen = .prescribedExteriorRoe := AssemblyControls.two_cell_corner
example (i : Fin 5) : 0 < AssemblyControls.twoCells.dualVolume i := by
  rw [CFDLean.MedianDual.Controls.two_cells_volume]
  split_ifs <;> norm_num
example : (∑ i, AssemblyControls.twoCells.dualVolume i) = 1/3 := CFDLean.MedianDual.Controls.two_cells_total_volume
example (i : Fin 5) : (AssemblyControls.varyingStates i).Admissible 2 := AssemblyControls.varying_admissible i
example (V : Finset (Fin 5) → Conservative 3) :
    (∑ i, meshResidual AssemblyControls.twoCells 2 (fun _ => .slipWall) V AssemblyControls.varyingStates i 0) = 0 := AssemblyControls.two_cell_all_wall_mass _ V
example (V : Finset (Fin 5) → Conservative 3) :
    (∑ i, meshResidual AssemblyControls.twoCells 2 (fun _ => .slipWall) V AssemblyControls.varyingStates i 4) = 0 := AssemblyControls.two_cell_all_wall_energy _ V
example :
    stationaryResidual (AssemblyControls.standard.interfaces.reindex (Equiv.swap 0 1)
      (Equiv.swap AssemblyControls.edge01 AssemblyControls.edge02) (Equiv.swap Controls.wallPatch Controls.openPatch)) 2
      (fun b => patchKind AssemblyControls.standard AssemblyControls.mixedKinds ((Equiv.swap Controls.wallPatch Controls.openPatch).symm b))
      (fun b => patchExterior AssemblyControls.standard AssemblyControls.mismatchingData ((Equiv.swap Controls.wallPatch Controls.openPatch).symm b))
      (fun _ => Controls.moving 0 1)
      (fun e => AssemblyControls.standard.edgeArea ((Equiv.swap AssemblyControls.edge01 AssemblyControls.edge02).symm e))
      (fun b => AssemblyControls.standard.boundaryArea ((Equiv.swap Controls.wallPatch Controls.openPatch).symm b)) 1 = ![-1/12,-1/6,0,0,-1/3] := AssemblyControls.transported_nonzero
example :
    (∑ i, stationaryResidual AssemblyControls.onePatchInterface 2 (fun _ => .slipWall) (fun _ => Controls.moving 0 3)
      (fun _ => Controls.moving 0 1) (fun _ => Controls.axis) (fun _ => Controls.axis) i) = ![0,1,0,0,0] := AssemblyControls.pressure_force_retained

end
end M4bChecks
