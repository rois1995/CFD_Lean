import CFDLean.Exec.MusclRefinement
import CFDLean.Schemes.Burgers.RusanovLimiters
import CFDLean.Exec.LimiterKernel
import CFDLean.Exec.RealScalarSign

/-! Burgers E0c-R, E0c-T: the limiter kernel of `CFDLean.Exec.LimiterKernel`, instantiated at `ℝ`, computes the
mathematical MUSCL-Rusanov scheme of `CFDLean.Burgers.Rusanov` with the slope function of the chosen limiter on the
periodic grid `Fin n`. Conservation transfers for every limiter, the unlimited one included; the bounds and the
total-variation bound transfer for the five limiters, under `(4 + 2θ) · dt · max(|m|, |M|) ≤ dx`. -/
noncomputable section
namespace CFDLean.Exec

open _root_.CFDLean.Scalar Periodic Burgers
open scoped BigOperators

/-! ### The mathematical slope function of a limiter -/

/-- The slope function of the mathematical scheme: the unlimited central slope, or a limiter factor on top of it. -/
def Limiter.slopeFn : Limiter → ℝ → ℝ → ℝ
  | .none => FiniteVolume.centralSlope
  | .minmod => FiniteVolume.limitedSlope FiniteVolume.minmodFactor
  | .mc => FiniteVolume.limitedSlope FiniteVolume.mcFactor
  | .superbee => FiniteVolume.limitedSlope FiniteVolume.superbeeFactor
  | .vanLeer => FiniteVolume.limitedSlope FiniteVolume.vanLeerFactor
  | .vanAlbada => FiniteVolume.limitedSlope FiniteVolume.vanAlbadaFactor

/-- The certificate constant of a limiter (`0` for the unlimited slope, which has no certificate). -/
def Limiter.theta : Limiter → ℝ
  | .none => 0
  | .minmod => 1
  | .mc => 2
  | .superbee => 2
  | .vanLeer => 2
  | .vanAlbada => 5 / 4

theorem Limiter.isLimited_iff (L : Limiter) : L.isLimited = true ↔ L ≠ .none := by
  cases L <;> decide

/-! ### The comparison-free kernel slopes with real arithmetic -/

theorem minmod_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : FiniteVolume.minmod a b = min a b := by
  rw [FiniteVolume.minmod, ite_eq_left ⟨ha, hb⟩]

theorem minmod_of_neg {a b : ℝ} (ha : a < 0) (hb : b < 0) : FiniteVolume.minmod a b = max a b := by
  rw [FiniteVolume.minmod, ite_eq_right (fun h => (not_lt.2 ha.le) h.1), ite_eq_left ⟨ha, hb⟩]

theorem minmod_of_not_mul_pos {a b : ℝ} (h : ¬ 0 < a * b) : FiniteVolume.minmod a b = 0 := by
  rw [FiniteVolume.minmod, ite_eq_right (fun h' => h (mul_pos h'.1 h'.2)),
    ite_eq_right (fun h' => h (mul_pos_of_neg_of_neg h'.1 h'.2))]

theorem maxmodSame_eq (x y : ℝ) : Scalar.maxmodSame x y = max 0 (max x y) + min 0 (min x y) := by
  change max 0 (max x y) + Scalar.min 0 (Scalar.min x y) = _
  rw [min_eq, min_eq]

/-- On two nonnegative numbers `maxmodSame` is their maximum. -/
theorem maxmodSame_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : Scalar.maxmodSame x y = max x y := by
  rw [maxmodSame_eq, max_eq_right (le_max_of_le_left hx), min_eq_left (le_min hx hy), add_zero]

/-- On two nonpositive numbers `maxmodSame` is their minimum (the one of larger modulus). -/
theorem maxmodSame_of_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) : Scalar.maxmodSame x y = min x y := by
  rw [maxmodSame_eq, max_eq_left (max_le hx hy), min_eq_right (min_le_of_left_le hx), zero_add]

theorem isPos_eq (x : ℝ) : ScalarSign.isPos x = decide (0 < x) := rfl

/-- The kernel slope with real arithmetic is the slope function of the mathematical scheme. -/
theorem limiterSlope_eq (L : Limiter) (a b : ℝ) : limiterSlope L a b = L.slopeFn a b := by
  cases L
  · rfl
  · change Scalar.minmod a b = FiniteVolume.limitedSlope FiniteVolume.minmodFactor a b
    rw [minmod_eq, FiniteVolume.limitedSlope_minmodFactor]
  · change Scalar.minmod (Scalar.minmod (2 * a) (2 * b)) ((a + b) / 2) = FiniteVolume.limitedSlope _ a b
    rw [minmod_eq, minmod_eq, FiniteVolume.limitedSlope_mcFactor]
    by_cases h : 0 < a * b
    · rw [ite_eq_left h]
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [minmod_of_pos (a := 2 * a) (b := 2 * b) (by linarith) (by linarith),
          minmod_of_pos (lt_min (by linarith) (by linarith)) (by linarith), ite_eq_left ha, abs_of_pos ha,
          abs_of_pos hb, abs_of_pos (by linarith : 0 < a + b)]
        simp only [min_def]
        split_ifs <;> linarith
      · rw [minmod_of_neg (a := 2 * a) (b := 2 * b) (by linarith) (by linarith),
          minmod_of_neg (max_lt (by linarith) (by linarith)) (by linarith), ite_eq_right (not_lt.2 ha.le),
          abs_of_neg ha, abs_of_neg hb, abs_of_neg (by linarith : a + b < 0)]
        simp only [max_def, min_def]
        split_ifs <;> linarith
    · rw [ite_eq_right h, minmod_of_not_mul_pos (a := 2 * a) (b := 2 * b) (fun h' => h (by nlinarith)),
        minmod_of_not_mul_pos (by rw [zero_mul]; exact lt_irrefl 0)]
  · change Scalar.maxmodSame (Scalar.minmod (2 * a) b) (Scalar.minmod a (2 * b)) = FiniteVolume.limitedSlope _ a b
    rw [minmod_eq, minmod_eq, FiniteVolume.limitedSlope_superbeeFactor]
    by_cases h : 0 < a * b
    · rw [ite_eq_left h]
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [minmod_of_pos (by linarith) hb, minmod_of_pos ha (by linarith),
          maxmodSame_of_nonneg (le_min (by linarith) hb.le) (le_min ha.le (by linarith)), ite_eq_left ha,
          abs_of_pos ha, abs_of_pos hb, one_mul]
      · rw [minmod_of_neg (by linarith) hb, minmod_of_neg ha (by linarith),
          maxmodSame_of_nonpos (max_le (by linarith) hb.le) (max_le ha.le (by linarith)),
          ite_eq_right (not_lt.2 ha.le), abs_of_neg ha, abs_of_neg hb]
        simp only [max_def, min_def]
        split_ifs <;> linarith
    · rw [ite_eq_right h, minmod_of_not_mul_pos (fun h' => h (by nlinarith)),
        minmod_of_not_mul_pos (fun h' => h (by nlinarith)), maxmodSame_of_nonneg le_rfl le_rfl, max_self]
  · change (if ScalarSign.isPos (a * b) then 2 * (a * b) / (a + b) else 0) = FiniteVolume.limitedSlope _ a b
    rw [FiniteVolume.limitedSlope_vanLeerFactor]
    simp only [isPos_eq, decide_eq_true_eq]
  · change (if ScalarSign.isPos (a * b) then a * b * (a + b) / (a * a + b * b) else 0) =
      FiniteVolume.limitedSlope _ a b
    rw [FiniteVolume.limitedSlope_vanAlbadaFactor]
    simp only [isPos_eq, decide_eq_true_eq, sq]

/-! ### Certificates -/

/-- Every limiter (not the unlimited slope) is in the Sweby region of its constant `θ`. -/
theorem Limiter.slopeBounded (L : Limiter) (hL : L ≠ .none) : FiniteVolume.SlopeBounded L.theta L.slopeFn := by
  cases L
  · exact absurd rfl hL
  · exact FiniteVolume.slopeBounded_minmodFactor
  · exact FiniteVolume.slopeBounded_mcFactor
  · exact FiniteVolume.slopeBounded_superbeeFactor
  · exact FiniteVolume.slopeBounded_vanLeerFactor
  · exact FiniteVolume.slopeBounded_vanAlbadaFactor

theorem Limiter.theta_le_two (L : Limiter) : L.theta ≤ 2 := by
  cases L <;> norm_num [Limiter.theta]

/-! ### Reconstruction -/

theorem limSlopeAt_eq {n : ℕ} [NeZero n] (L : Limiter) {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u)
    (j : Fin a.size) : limSlopeAt L a j = FiniteVolume.slope (finGrid n) L.slopeFn u (Fin.cast h.1 j) := by
  simp only [limSlopeAt, h.get, prevIdx_cast, nextIdx_cast, limiterSlope_eq]
  rfl

theorem limFacePlus_eq {n : ℕ} [NeZero n] (L : Limiter) {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u)
    (j : Fin a.size) : limFacePlus L a j = FiniteVolume.leftState (finGrid n) L.slopeFn u (Fin.cast h.1 j) := by
  simp only [limFacePlus, h.get, limSlopeAt_eq L h]
  rfl

theorem limFaceMinus_eq {n : ℕ} [NeZero n] (L : Limiter) {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u)
    (j : Fin a.size) :
    limFaceMinus L a j = FiniteVolume.rightState (finGrid n) L.slopeFn u ((finGrid n).prev (Fin.cast h.1 j)) := by
  simp only [limFaceMinus, h.get, limSlopeAt_eq L h, FiniteVolume.rightState, Grid.next_prev]
  rfl

/-! ### Refinement of the one-step maps -/

/-- 4. The array limiter Euler step computes the MUSCL-Rusanov Euler map with the slope function of `L` on
`finGrid n`, for every limiter (the unlimited one included). -/
theorem limiterEulerStepArray_refines {n : ℕ} [NeZero n] (L : Limiter) (dx dt : ℝ) {a : Array ℝ}
    {u : Fin n → ℝ} (h : Represents a u) :
    Represents (limiterEulerStepArray L dx dt a) (Rusanov.musclEulerStep (finGrid n) dx dt L.slopeFn u) := by
  refine ⟨Array.size_ofFn.trans h.1, fun i => ?_⟩
  simp only [limiterEulerStepArray, Array.getElem_ofFn, h.get, limFacePlus_eq L h, limFaceMinus_eq L h,
    nextIdx_cast, prevIdx_cast, Grid.prev_next, rusanov_eq]
  rfl

/-- 4. The array limiter SSPRK2 step computes the MUSCL-Rusanov SSPRK2 map with the slope function of `L`. -/
theorem limiterSsprk2StepArray_refines {n : ℕ} [NeZero n] (L : Limiter) (dx dt : ℝ) {a : Array ℝ}
    {u : Fin n → ℝ} (h : Represents a u) :
    Represents (limiterSsprk2StepArray L dx dt a) (Rusanov.musclSsprk2Step (finGrid n) dx dt L.slopeFn u) :=
  axpby_refines _ _ h (limiterEulerStepArray_refines L dx dt (limiterEulerStepArray_refines L dx dt h))

/-- 4. The array limiter SSPRK3 step computes the MUSCL-Rusanov SSPRK3 map with the slope function of `L`. -/
theorem limiterSsprk3StepArray_refines {n : ℕ} [NeZero n] (L : Limiter) (dx dt : ℝ) {a : Array ℝ}
    {u : Fin n → ℝ} (h : Represents a u) :
    Represents (limiterSsprk3StepArray L dx dt a) (Rusanov.musclSsprk3Step (finGrid n) dx dt L.slopeFn u) :=
  axpby_refines _ _ h (limiterEulerStepArray_refines L dx dt
    (axpby_refines _ _ h (limiterEulerStepArray_refines L dx dt (limiterEulerStepArray_refines L dx dt h))))

/-! ### Sizes -/

theorem limiterEulerStepArray_size (L : Limiter) (dx dt : ℝ) (a : Array ℝ) :
    (limiterEulerStepArray L dx dt a).size = a.size := by
  simp [limiterEulerStepArray]

theorem limiterSsprk2StepArray_size (L : Limiter) (dx dt : ℝ) (a : Array ℝ) :
    (limiterSsprk2StepArray L dx dt a).size = a.size := by
  simp [limiterSsprk2StepArray, axpby_size, limiterEulerStepArray_size]

theorem limiterSsprk3StepArray_size (L : Limiter) (dx dt : ℝ) (a : Array ℝ) :
    (limiterSsprk3StepArray L dx dt a).size = a.size := by
  simp [limiterSsprk3StepArray, axpby_size, limiterEulerStepArray_size]

/-! ### Refinement on every periodic grid -/

theorem limiterEulerStepArray_refinedBy (L : Limiter) (dx dt : ℝ) :
    RefinedBy (limiterEulerStepArray L dx dt) (fun n _ => Rusanov.musclEulerStep (finGrid n) dx dt L.slopeFn) :=
  fun _ _ _ _ h => limiterEulerStepArray_refines L dx dt h

theorem limiterSsprk2StepArray_refinedBy (L : Limiter) (dx dt : ℝ) :
    RefinedBy (limiterSsprk2StepArray L dx dt) (fun n _ => Rusanov.musclSsprk2Step (finGrid n) dx dt L.slopeFn) :=
  fun _ _ _ _ h => limiterSsprk2StepArray_refines L dx dt h

theorem limiterSsprk3StepArray_refinedBy (L : Limiter) (dx dt : ℝ) :
    RefinedBy (limiterSsprk3StepArray L dx dt) (fun n _ => Rusanov.musclSsprk3Step (finGrid n) dx dt L.slopeFn) :=
  fun _ _ _ _ h => limiterSsprk3StepArray_refines L dx dt h

/-! ### 5. Transfer corollaries -/

/-- 5. `k` kernel limiter Euler steps (in `ℝ`) keep the sum of the entries when `dx ≠ 0`, for every limiter. -/
theorem run_limiterEulerStepArray_sum (L : Limiter) (dx dt : ℝ) (hdx : dx ≠ 0) (a : Array ℝ) (k : ℕ) :
    sumArray (run (limiterEulerStepArray L dx dt) k a) = sumArray a :=
  run_sumArray (limiterEulerStepArray_size L dx dt) (limiterEulerStepArray_refinedBy L dx dt)
    (fun _ _ u => Rusanov.musclEulerStep_sum _ dx dt _ hdx u) a k

/-- 5. `k` kernel limiter SSPRK3 steps (in `ℝ`) keep the sum of the entries when `dx ≠ 0`, for every limiter. -/
theorem run_limiterSsprk3StepArray_sum (L : Limiter) (dx dt : ℝ) (hdx : dx ≠ 0) (a : Array ℝ) (k : ℕ) :
    sumArray (run (limiterSsprk3StepArray L dx dt) k a) = sumArray a :=
  run_sumArray (limiterSsprk3StepArray_size L dx dt) (limiterSsprk3StepArray_refinedBy L dx dt)
    (fun _ _ u => Rusanov.musclSsprk3Step_sum _ dx dt _ hdx u) a k

/-- 5. After `k` kernel limiter Euler steps (in `ℝ`) every entry stays in the initial bounds `[m, M]`. -/
theorem run_limiterEulerStepArray_bounds (L : Limiter) (hL : L ≠ .none) (dx dt m M : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : (4 + 2 * L.theta) * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a)
    (k : ℕ) : EntriesBetween m M (run (limiterEulerStepArray L dx dt) k a) :=
  run_entriesBetween (limiterEulerStepArray_size L dx dt) (limiterEulerStepArray_refinedBy L dx dt)
    (fun _ _ u k hu => (Rusanov.musclEulerStep_iterate_stable_bounded _ dx dt m M _ _ (L.slopeBounded hL)
      L.theta_le_two hdx hdt hcfl u hu k).1) hb k

/-- 5. After `k` kernel limiter SSPRK3 steps (in `ℝ`) every entry stays in the initial bounds `[m, M]`. -/
theorem run_limiterSsprk3StepArray_bounds (L : Limiter) (hL : L ≠ .none) (dx dt m M : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : (4 + 2 * L.theta) * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a)
    (k : ℕ) : EntriesBetween m M (run (limiterSsprk3StepArray L dx dt) k a) :=
  run_entriesBetween (limiterSsprk3StepArray_size L dx dt) (limiterSsprk3StepArray_refinedBy L dx dt)
    (fun _ _ u k hu => (Rusanov.musclSsprk3Step_iterate_stable_bounded _ dx dt m M _ _ (L.slopeBounded hL)
      L.theta_le_two hdx hdt hcfl u hu k).1) hb k

/-- 5. `k` kernel limiter Euler steps (in `ℝ`) do not increase the periodic total variation of the entries. -/
theorem run_limiterEulerStepArray_totalVariation_le (L : Limiter) (hL : L ≠ .none) (dx dt m M : ℝ)
    (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : (4 + 2 * L.theta) * (dt * max |m| |M|) ≤ dx) (a : Array ℝ)
    (hb : EntriesBetween m M a) (k : ℕ) :
    totalVariationArray (run (limiterEulerStepArray L dx dt) k a) ≤ totalVariationArray a :=
  run_totalVariationArray_le (limiterEulerStepArray_size L dx dt) (limiterEulerStepArray_refinedBy L dx dt)
    (fun _ _ u k hu => (Rusanov.musclEulerStep_iterate_stable_bounded _ dx dt m M _ _ (L.slopeBounded hL)
      L.theta_le_two hdx hdt hcfl u hu k).2) hb k

/-- 5. `k` kernel limiter SSPRK3 steps (in `ℝ`) do not increase the periodic total variation of the entries. -/
theorem run_limiterSsprk3StepArray_totalVariation_le (L : Limiter) (hL : L ≠ .none) (dx dt m M : ℝ)
    (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : (4 + 2 * L.theta) * (dt * max |m| |M|) ≤ dx) (a : Array ℝ)
    (hb : EntriesBetween m M a) (k : ℕ) :
    totalVariationArray (run (limiterSsprk3StepArray L dx dt) k a) ≤ totalVariationArray a :=
  run_totalVariationArray_le (limiterSsprk3StepArray_size L dx dt) (limiterSsprk3StepArray_refinedBy L dx dt)
    (fun _ _ u k hu => (Rusanov.musclSsprk3Step_iterate_stable_bounded _ dx dt m M _ _ (L.slopeBounded hL)
      L.theta_le_two hdx hdt hcfl u hu k).2) hb k

/-! ### 6. Consistency with the minmod kernel of `CFDLean.Exec.MusclKernel`, for every arithmetic -/

section Consistency

variable {α : Type} [Scalar α] [ScalarSign α]

theorem limiterEulerStepArray_minmod (dx dt : α) (a : Array α) :
    limiterEulerStepArray .minmod dx dt a = musclEulerStepArray dx dt a := rfl

theorem limiterSsprk2StepArray_minmod (dx dt : α) (a : Array α) :
    limiterSsprk2StepArray .minmod dx dt a = musclSsprk2StepArray dx dt a := rfl

theorem limiterSsprk3StepArray_minmod (dx dt : α) (a : Array α) :
    limiterSsprk3StepArray .minmod dx dt a = musclSsprk3StepArray dx dt a := rfl

end Consistency

end CFDLean.Exec
