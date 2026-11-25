import CFDLean.Physics.Euler.PhysicalJacobian
import Mathlib.Tactic.Linarith

noncomputable section
namespace CFDLean.Roe
open Coordinates PhysicalJacobian

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

def root (x : StateCoordinates) : ℝ := Real.sqrt (x 0)
def weight (x y : StateCoordinates) : ℝ := root x / (root x + root y)
def averageVelocity (x y : StateCoordinates) : Vector 3 :=
  fun i => weight x y * velocity x i + weight y x * velocity y i
def averageEnthalpy (γ : ℝ) (x y : StateCoordinates) : ℝ :=
  weight x y * enthalpy γ x + weight y x * enthalpy γ y
def soundSquare (γ : ℝ) (x y : StateCoordinates) : ℝ :=
  (γ - 1) * (averageEnthalpy γ x y - squareSum (averageVelocity x y) / 2)
def soundSpeed (γ : ℝ) (x y : StateCoordinates) : ℝ := Real.sqrt (soundSquare γ x y)
def endpointSoundSquare (γ : ℝ) (x : StateCoordinates) : ℝ :=
  γ * coordinatePressure γ x / x 0

theorem root_pos (x : StateCoordinates) (h : 0 < x 0) : 0 < root x := Real.sqrt_pos.mpr h

theorem root_sq (x : StateCoordinates) (h : 0 ≤ x 0) : root x ^ 2 = x 0 :=
  Real.sq_sqrt h

theorem root_sum_pos (x y : StateCoordinates) (hx : 0 < x 0) (hy : 0 < y 0) :
    0 < root x + root y := add_pos (root_pos x hx) (root_pos y hy)

theorem weight_pos (x y : StateCoordinates) (hx : 0 < x 0) (hy : 0 < y 0) :
    0 < weight x y := div_pos (root_pos x hx) (root_sum_pos x y hx hy)

theorem weight_sum (x y : StateCoordinates) (hx : 0 < x 0) (hy : 0 < y 0) :
    weight x y + weight y x = 1 := by
  unfold weight
  rw [add_comm (root y) (root x), ← add_div]
  exact div_self (ne_of_gt (root_sum_pos x y hx hy))

theorem weight_lt_one (x y : StateCoordinates) (hx : 0 < x 0) (hy : 0 < y 0) :
    weight x y < 1 := by
  have := weight_sum x y hx hy
  have := weight_pos y x hy hx
  linarith

theorem averages_swap (γ : ℝ) (x y : StateCoordinates) :
    averageVelocity y x = averageVelocity x y ∧
    averageEnthalpy γ y x = averageEnthalpy γ x y ∧ soundSquare γ y x = soundSquare γ x y := by
  have hv : averageVelocity y x = averageVelocity x y := by
    funext i
    exact add_comm _ _
  have hH : averageEnthalpy γ y x = averageEnthalpy γ x y := add_comm _ _
  exact ⟨hv, hH, by rw [soundSquare, hv, hH]; rfl⟩

theorem weighted_square (a b : ℝ) (v w : Vector 3) (h : a + b = 1) :
    squareSum (fun i => a * v i + b * w i) =
      a * squareSum v + b * squareSum w - a * b * squareSum (fun i => w i - v i) := by
  have hb : b = 1 - a := by linarith
  rw [hb]
  simp only [squareSum_three]
  ring1

theorem endpoint_thermal (γ : ℝ) (x : StateCoordinates) (hρ : x 0 ≠ 0) :
    (γ - 1) * (enthalpy γ x - squareSum (velocity x) / 2) = endpointSoundSquare γ x := by
  simp [enthalpy, endpointSoundSquare, pressure_formula, velocity, decode, squareSum_three]
  field_simp [hρ]
  ring1

theorem variance_identity (γ : ℝ) (x y : StateCoordinates)
    (hx : 0 < x 0) (hy : 0 < y 0) :
    soundSquare γ x y = weight x y * endpointSoundSquare γ x +
      weight y x * endpointSoundSquare γ y +
      (γ - 1) / 2 * weight x y * weight y x *
        squareSum (fun i => velocity y i - velocity x i) := by
  unfold soundSquare averageVelocity
  rw [weighted_square _ _ _ _ (weight_sum x y hx hy)]
  rw [← endpoint_thermal γ x (ne_of_gt hx), ← endpoint_thermal γ y (ne_of_gt hy)]
  unfold averageEnthalpy
  ring1

theorem soundSquare_pos (γ : ℝ) (x y : StateCoordinates) (hγ : 1 < γ)
    (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) :
    0 < soundSquare γ x y := by
  have hpx : 0 < endpointSoundSquare γ x :=
    div_pos (mul_pos (lt_trans zero_lt_one hγ) hx.2) hx.1
  have hpy : 0 < endpointSoundSquare γ y :=
    div_pos (mul_pos (lt_trans zero_lt_one hγ) hy.2) hy.1
  have hxy := weight_pos x y hx.1 hy.1
  have hyx := weight_pos y x hy.1 hx.1
  rw [variance_identity γ x y hx.1 hy.1]
  apply add_pos_of_pos_of_nonneg (add_pos (mul_pos hxy hpx) (mul_pos hyx hpy))
  exact mul_nonneg (le_of_lt (mul_pos (mul_pos (div_pos (sub_pos.mpr hγ) (by norm_num)) hxy) hyx))
    (squareSum_nonneg _)

theorem soundSpeed_pos (γ : ℝ) (x y : StateCoordinates) (hγ : 1 < γ)
    (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) :
    0 < soundSpeed γ x y := Real.sqrt_pos.mpr (soundSquare_pos γ x y hγ hx hy)

theorem soundSpeed_sq (γ : ℝ) (x y : StateCoordinates) (hγ : 1 < γ)
    (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) :
    soundSpeed γ x y ^ 2 = soundSquare γ x y :=
  Real.sq_sqrt (le_of_lt (soundSquare_pos γ x y hγ hx hy))

theorem velocity_continuousAt (x : StateCoordinates) (hx : x 0 ≠ 0) (i : Fin 3) :
    ContinuousAt (fun y => velocity y i) x := by
  fin_cases i <;> exact (continuous_apply _).continuousAt.div (continuous_apply 0).continuousAt hx

theorem enthalpy_continuousAt (γ : ℝ) (x : StateCoordinates) (hx : x 0 ≠ 0) :
    ContinuousAt (enthalpy γ) x :=
  ((continuous_apply 4).continuousAt.add (hasFDerivAt_pressure γ x hx).continuousAt).div
    (continuous_apply 0).continuousAt hx

theorem weight_continuousAt (p : StateCoordinates × StateCoordinates)
    (hx : 0 < p.1 0) (hy : 0 < p.2 0) :
    ContinuousAt (fun q : StateCoordinates × StateCoordinates => weight q.1 q.2) p := by
  have hl : Continuous (fun q : StateCoordinates × StateCoordinates => root q.1) :=
    Real.continuous_sqrt.comp ((continuous_apply 0).comp continuous_fst)
  have hr : Continuous (fun q : StateCoordinates × StateCoordinates => root q.2) :=
    Real.continuous_sqrt.comp ((continuous_apply 0).comp continuous_snd)
  exact hl.continuousAt.div (hl.add hr).continuousAt (ne_of_gt (root_sum_pos p.1 p.2 hx hy))

theorem averages_continuousAt (γ : ℝ) (p : StateCoordinates × StateCoordinates)
    (hx : 0 < p.1 0) (hy : 0 < p.2 0) :
    ContinuousAt (fun q : StateCoordinates × StateCoordinates =>
      (averageVelocity q.1 q.2, averageEnthalpy γ q.1 q.2)) p := by
  have hw := weight_continuousAt p hx hy
  have hw' : ContinuousAt (fun q : StateCoordinates × StateCoordinates => weight q.2 q.1) p :=
    (weight_continuousAt (p.2, p.1) hy hx).comp (f := fun q : StateCoordinates × StateCoordinates => (q.2, q.1)) (continuous_snd.prodMk continuous_fst).continuousAt
  have hv : ContinuousAt (fun q : StateCoordinates × StateCoordinates => averageVelocity q.1 q.2) p := by
    apply continuousAt_pi.mpr
    intro i
    exact (hw.mul ((velocity_continuousAt p.1 (ne_of_gt hx) i).comp (f := fun q : StateCoordinates × StateCoordinates => q.1) continuousAt_fst)).add
      (hw'.mul ((velocity_continuousAt p.2 (ne_of_gt hy) i).comp (f := fun q : StateCoordinates × StateCoordinates => q.2) continuousAt_snd))
  exact hv.prodMk ((hw.mul ((enthalpy_continuousAt γ p.1 (ne_of_gt hx)).comp (f := fun q : StateCoordinates × StateCoordinates => q.1) continuousAt_fst)).add
    (hw'.mul ((enthalpy_continuousAt γ p.2 (ne_of_gt hy)).comp (f := fun q : StateCoordinates × StateCoordinates => q.2) continuousAt_snd)))

theorem averages_diagonal (γ : ℝ) (x : StateCoordinates) (hx : 0 < x 0) :
    averageVelocity x x = velocity x ∧ averageEnthalpy γ x x = enthalpy γ x := by
  have hw := weight_sum x x hx hx
  constructor
  · funext i
    change weight x x * velocity x i + weight x x * velocity x i = velocity x i
    rw [← add_mul, hw, one_mul]
  · change weight x x * enthalpy γ x + weight x x * enthalpy γ x = enthalpy γ x
    rw [← add_mul, hw, one_mul]

end CFDLean.Roe
