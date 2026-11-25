import CFDLean.Foundations.Coordinates
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod

noncomputable section
namespace CFDLean.PhysicalJacobian
open Coordinates
open scoped Topology

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

abbrev projection (i : Fin 5) : StateCoordinates →L[ℝ] ℝ := ContinuousLinearMap.proj i

def coordinatePressure (γ : ℝ) (x : StateCoordinates) : ℝ := (decode x).pressure γ

def velocity (x : StateCoordinates) : Vector 3 :=
  fun i => (decode x).momentum i / x 0

def enthalpy (γ : ℝ) (x : StateCoordinates) : ℝ := (x 4 + coordinatePressure γ x) / x 0

def normalMomentum (n : Vector 3) : StateCoordinates →L[ℝ] ℝ :=
  n 0 • projection 1 + n 1 • projection 2 + n 2 • projection 3

def pressureDifferential (γ : ℝ) (x : StateCoordinates) : StateCoordinates →L[ℝ] ℝ :=
  (γ - 1) • (projection 4 -
    (velocity x 0 • projection 1 + velocity x 1 • projection 2 + velocity x 2 • projection 3) +
    (squareSum (velocity x) / 2) • projection 0)

def normalIncrement (x : StateCoordinates) (n : Vector 3) : StateCoordinates →L[ℝ] ℝ :=
  normalMomentum n - dot (velocity x) n • projection 0

def jacobian (γ : ℝ) (x : StateCoordinates) (n : Vector 3) :
    StateCoordinates →L[ℝ] StateCoordinates :=
  let q := dot (velocity x) n
  let b := normalIncrement x n
  let dp := pressureDifferential γ x
  ContinuousLinearMap.pi ![normalMomentum n,
    q • projection 1 + velocity x 0 • b + n 0 • dp,
    q • projection 2 + velocity x 1 • b + n 1 • dp,
    q • projection 3 + velocity x 2 • b + n 2 • dp,
    q • (projection 4 + dp) + enthalpy γ x • b]

def coordinateFlux (γ : ℝ) (S : Vector 3) (x : StateCoordinates) : StateCoordinates :=
  encode (physicalFlux γ (decode x) S)

theorem pressure_formula (γ : ℝ) (x : StateCoordinates) :
    coordinatePressure γ x = (γ - 1) *
      (x 4 - (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) / (2 * x 0)) := by
  simp [coordinatePressure, Conservative.pressure, decode, squareSum_three]

theorem hasFDerivAt_pressure (γ : ℝ) (x : StateCoordinates) (hρ : x 0 ≠ 0) :
    HasFDerivAt (coordinatePressure γ) (pressureDifferential γ x) x := by
  have h0 := (projection 0).hasFDerivAt (x := x)
  have h1 := (projection 1).hasFDerivAt (x := x)
  have h2 := (projection 2).hasFDerivAt (x := x)
  have h3 := (projection 3).hasFDerivAt (x := x)
  have h4 := (projection 4).hasFDerivAt (x := x)
  have hi := (hasDerivAt_inv hρ).comp_hasFDerivAt x h0
  have hQ := ((h1.mul h1).add (h2.mul h2)).add (h3.mul h3)
  have hp := (h4.sub ((hQ.mul hi).mul_const (1 / 2 : ℝ))).const_mul (γ - 1)
  convert hp using 1
  · funext y
    rw [pressure_formula]
    simp only [projection, ContinuousLinearMap.proj_apply, Pi.sub_apply, Pi.add_apply,
      Pi.mul_apply, Function.comp_apply, div_eq_mul_inv, mul_inv_rev, pow_two]
    ring1
  · ext v
    simp [pressureDifferential, velocity, decode, projection, squareSum_three]
    field_simp [hρ]
    ring1

theorem hasFDerivAt_normalMomentum (n : Vector 3) (x : StateCoordinates) :
    HasFDerivAt (fun y => dot (decode y).momentum n) (normalMomentum n) x := by
  convert (normalMomentum n).hasFDerivAt (x := x) using 1
  funext y
  simp [normalMomentum, projection, decode, dot_three]
  ring1

theorem hasFDerivAt_normalVelocity (n : Vector 3) (x : StateCoordinates) (hρ : x 0 ≠ 0) :
    HasFDerivAt (fun y => dot (decode y).momentum n / y 0)
      ((1 / x 0) • normalIncrement x n) x := by
  have hi := (hasDerivAt_inv hρ).comp_hasFDerivAt x ((projection 0).hasFDerivAt (x := x))
  have h := (hasFDerivAt_normalMomentum n x).mul hi
  convert h using 1
  · funext v
    simp [decode, dot_three, div_eq_mul_inv]
  ext v
  simp [normalIncrement, normalMomentum, velocity, decode, projection, dot_three]
  field_simp [hρ]
  ring1

theorem hasFDerivAt_coordinateFlux (γ : ℝ) (n : Vector 3) (x : StateCoordinates)
    (hρ : x 0 ≠ 0) : HasFDerivAt (coordinateFlux γ n) (jacobian γ x n) x := by
  have hm := hasFDerivAt_normalMomentum n x
  have hq := hasFDerivAt_normalVelocity n x hρ
  have hp := hasFDerivAt_pressure γ x hρ
  have h1 := (projection 1).hasFDerivAt (x := x)
  have h2 := (projection 2).hasFDerivAt (x := x)
  have h3 := (projection 3).hasFDerivAt (x := x)
  have h4 := (projection 4).hasFDerivAt (x := x)
  have h := hasFDerivAt_pi.mpr (show ∀ i : Fin 5, HasFDerivAt
      (![fun y => dot (decode y).momentum n,
        fun y => y 1 * (dot (decode y).momentum n / y 0) + coordinatePressure γ y * n 0,
        fun y => y 2 * (dot (decode y).momentum n / y 0) + coordinatePressure γ y * n 1,
        fun y => y 3 * (dot (decode y).momentum n / y 0) + coordinatePressure γ y * n 2,
        fun y => (y 4 + coordinatePressure γ y) * (dot (decode y).momentum n / y 0)] i)
      (![normalMomentum n,
        x 1 • ((1 / x 0) • normalIncrement x n) +
          (dot (decode x).momentum n / x 0) • projection 1 + n 0 • pressureDifferential γ x,
        x 2 • ((1 / x 0) • normalIncrement x n) +
          (dot (decode x).momentum n / x 0) • projection 2 + n 1 • pressureDifferential γ x,
        x 3 • ((1 / x 0) • normalIncrement x n) +
          (dot (decode x).momentum n / x 0) • projection 3 + n 2 • pressureDifferential γ x,
        (x 4 + coordinatePressure γ x) • ((1 / x 0) • normalIncrement x n) +
          (dot (decode x).momentum n / x 0) • (projection 4 + pressureDifferential γ x)] i) x from by
        intro i
        fin_cases i
        · exact hm
        · exact (h1.mul hq).add (hp.mul_const (n 0))
        · exact (h2.mul hq).add (hp.mul_const (n 1))
        · exact (h3.mul hq).add (hp.mul_const (n 2))
        · exact (h4.add hp).mul hq)
  convert h using 1
  · funext y i
    fin_cases i <;> rfl
  · ext v i
    fin_cases i <;>
      simp [jacobian, normalIncrement, normalMomentum, velocity, enthalpy, decode,
        projection, dot_three, div_eq_mul_inv] <;> ring1

theorem jacobian_smul (γ : ℝ) (x : StateCoordinates) (n : Vector 3) (a : ℝ) :
    jacobian γ x (fun i => a * n i) = a • jacobian γ x n := by
  ext v i
  fin_cases i <;>
    simp [jacobian, normalIncrement, normalMomentum, dot_mul] <;> ring1

theorem hasFDerivAt_integratedFlux (γ : ℝ) (S : Vector 3) (x : StateCoordinates)
    (hρ : x 0 ≠ 0) (hS : S ≠ 0) :
    HasFDerivAt (coordinateFlux γ S) (area S • jacobian γ x (unitNormal S)) x := by
  have hj : jacobian γ x S = area S • jacobian γ x (unitNormal S) := by
    conv_lhs => rw [reconstruct_area S hS]
    exact jacobian_smul γ x (unitNormal S) (area S)
  rw [← hj]
  exact hasFDerivAt_coordinateFlux γ S x hρ

theorem isOpen_admissible (γ : ℝ) :
    IsOpen {x : StateCoordinates | (decode x).Admissible γ} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have h1 : {y : StateCoordinates | 0 < y 0} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx.1
  have h2 : {y | 0 < coordinatePressure γ y} ∈ 𝓝 x :=
    (hasFDerivAt_pressure γ x (ne_of_gt hx.1)).continuousAt.eventually (Ioi_mem_nhds hx.2)
  exact Filter.mem_of_superset (Filter.inter_mem h1 h2) (fun _ h => h)

set_option cleanup.letToHave false in
theorem jacobian_action (γ : ℝ) (U V : Conservative 3) (n : Vector 3) :
    let u := fun i => U.momentum i / U.density
    let q := dot u n
    let b := dot V.momentum n - q * V.density
    let dp := (γ - 1) * (V.energy - dot u V.momentum + squareSum u / 2 * V.density)
    let H := (U.energy + U.pressure γ) / U.density
    jacobian γ (encode U) n (encode V) = encode
      ⟨dot V.momentum n, fun i => q * V.momentum i + u i * b + dp * n i,
       q * (V.energy + dp) + H * b⟩ := by
  dsimp only
  simp only [jacobian, normalIncrement, normalMomentum, pressureDifferential, velocity,
    enthalpy, coordinatePressure, decode_encode]
  funext i
  fin_cases i <;>
    simp [projection, encode, decode, velocity,
      Conservative.pressure, dot_three, squareSum_three, div_eq_mul_inv, mul_inv_rev] <;> ring1

theorem coordinateFlux_zero (γ : ℝ) : coordinateFlux γ (0 : Vector 3) = fun _ => 0 := by
  funext x i
  change encode (physicalFlux γ (decode x) (fun _ => 0)) i = 0
  rw [physicalFlux_zero]
  fin_cases i <;> rfl

theorem hasFDerivAt_zeroArea (γ : ℝ) (x : StateCoordinates) :
    HasFDerivAt (𝕜 := ℝ) (coordinateFlux γ (0 : Vector 3)) 0 x := by
  rw [coordinateFlux_zero]
  exact hasFDerivAt_const (𝕜 := ℝ) (0 : StateCoordinates) x

end CFDLean.PhysicalJacobian
