import CFDLean.Exec.Refinement
import CFDLean.Schemes.Burgers.RusanovMuscl
import CFDLean.Exec.MusclKernel

/-! Burgers E0b-R, E0b-T: the MUSCL array kernel of `CFDLean.Exec.MusclKernel`, instantiated at `ℝ`, computes the
mathematical MUSCL-minmod-Rusanov scheme of `CFDLean.Burgers.Rusanov` on the periodic grid `Fin n`. The stability and
conservation theorems of the scheme then transfer to the arrays the kernel produces. -/
noncomputable section
namespace CFDLean.Exec

open _root_.CFDLean.Scalar Periodic Burgers
open scoped BigOperators

/-! ### The comparison-free minmod -/

theorem min_eq (a b : ℝ) : Scalar.min a b = min a b := by
  change -max (-a) (-b) = min a b
  rw [max_neg_neg, neg_neg]

theorem minmod_eq (a b : ℝ) : Scalar.minmod a b = FiniteVolume.minmod a b := by
  change max 0 (Scalar.min a b) + Scalar.min 0 (max a b) = _
  rw [min_eq, min_eq]
  unfold FiniteVolume.minmod
  split_ifs with h1 h2
  · rw [max_eq_right (le_min h1.1.le h1.2.le), min_eq_left (le_max_of_le_left h1.1.le), add_zero]
  · rw [max_eq_left (min_le_of_left_le h2.1.le), min_eq_right (max_le h2.1.le h2.2.le), zero_add]
  · have h3 : min a b ≤ 0 := min_le_iff.2 (by by_contra h; push Not at h; exact h1 h)
    have h4 : 0 ≤ max a b := le_max_iff.2 (by by_contra h; push Not at h; exact h2 h)
    rw [max_eq_left h3, min_eq_left h4, add_zero]

/-! ### Periodic indices -/

theorem nextIdx_cast {m n : ℕ} [NeZero n] (hs : m = n) (j : Fin m) :
    Fin.cast hs (nextIdx j) = (finGrid n).next (Fin.cast hs j) := by
  ext
  simp [nextIdx, finGrid_next_val, hs]

theorem prevIdx_cast {m n : ℕ} [NeZero n] (hs : m = n) (j : Fin m) :
    Fin.cast hs (prevIdx j) = (finGrid n).prev (Fin.cast hs j) := by
  ext
  simp [prevIdx, finGrid_prev_val, hs]

/-! ### Reconstruction -/

/-- Entry lookup with a `Fin a.size` index. -/
theorem Represents.get {n : ℕ} {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u) (j : Fin a.size) :
    a[j] = u (Fin.cast h.1 j) :=
  h.getElem_eq _ _ _ rfl

theorem slopeAt_eq {n : ℕ} [NeZero n] {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u) (j : Fin a.size) :
    slopeAt a j = FiniteVolume.slope (finGrid n) FiniteVolume.minmod u (Fin.cast h.1 j) := by
  simp only [slopeAt, h.get, prevIdx_cast, nextIdx_cast, minmod_eq]
  rfl

theorem facePlus_eq {n : ℕ} [NeZero n] {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u) (j : Fin a.size) :
    facePlus a j = FiniteVolume.leftState (finGrid n) FiniteVolume.minmod u (Fin.cast h.1 j) := by
  simp only [facePlus, h.get, slopeAt_eq h]
  rfl

theorem faceMinus_eq {n : ℕ} [NeZero n] {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u) (j : Fin a.size) :
    faceMinus a j = FiniteVolume.rightState (finGrid n) FiniteVolume.minmod u ((finGrid n).prev (Fin.cast h.1 j)) := by
  simp only [faceMinus, h.get, slopeAt_eq h, FiniteVolume.rightState, Grid.next_prev]
  rfl

/-! ### Refinement of the one-step maps -/

/-- 1. The array MUSCL Euler step computes the MUSCL-minmod-Rusanov Euler map on `finGrid n`. -/
theorem musclEulerStepArray_refines {n : ℕ} [NeZero n] (dx dt : ℝ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) :
    Represents (musclEulerStepArray dx dt a) (Rusanov.musclEulerStep (finGrid n) dx dt FiniteVolume.minmod u) := by
  refine ⟨Array.size_ofFn.trans h.1, fun i => ?_⟩
  simp only [musclEulerStepArray, Array.getElem_ofFn, h.get, facePlus_eq h, faceMinus_eq h, nextIdx_cast,
    prevIdx_cast, Grid.prev_next, rusanov_eq]
  rfl

/-- 2a. The array MUSCL SSPRK2 step computes the MUSCL-minmod-Rusanov SSPRK2 map on `finGrid n`. -/
theorem musclSsprk2StepArray_refines {n : ℕ} [NeZero n] (dx dt : ℝ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) :
    Represents (musclSsprk2StepArray dx dt a) (Rusanov.musclSsprk2Step (finGrid n) dx dt FiniteVolume.minmod u) :=
  axpby_refines _ _ h (musclEulerStepArray_refines dx dt (musclEulerStepArray_refines dx dt h))

/-- 2b. The array MUSCL SSPRK3 step computes the MUSCL-minmod-Rusanov SSPRK3 map on `finGrid n`. -/
theorem musclSsprk3StepArray_refines {n : ℕ} [NeZero n] (dx dt : ℝ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) :
    Represents (musclSsprk3StepArray dx dt a) (Rusanov.musclSsprk3Step (finGrid n) dx dt FiniteVolume.minmod u) :=
  axpby_refines _ _ h (musclEulerStepArray_refines dx dt
    (axpby_refines _ _ h (musclEulerStepArray_refines dx dt (musclEulerStepArray_refines dx dt h))))

/-! ### Sizes -/

theorem musclEulerStepArray_size (dx dt : ℝ) (a : Array ℝ) : (musclEulerStepArray dx dt a).size = a.size := by
  simp [musclEulerStepArray]

theorem musclSsprk2StepArray_size (dx dt : ℝ) (a : Array ℝ) : (musclSsprk2StepArray dx dt a).size = a.size := by
  simp [musclSsprk2StepArray, axpby_size, musclEulerStepArray_size]

theorem musclSsprk3StepArray_size (dx dt : ℝ) (a : Array ℝ) : (musclSsprk3StepArray dx dt a).size = a.size := by
  simp [musclSsprk3StepArray, axpby_size, musclEulerStepArray_size]

/-! ### Transfer corollaries -/

theorem musclEulerStepArray_refinedBy (dx dt : ℝ) :
    RefinedBy (musclEulerStepArray dx dt)
      (fun n _ => Rusanov.musclEulerStep (finGrid n) dx dt FiniteVolume.minmod) :=
  fun _ _ _ _ h => musclEulerStepArray_refines dx dt h

theorem musclSsprk3StepArray_refinedBy (dx dt : ℝ) :
    RefinedBy (musclSsprk3StepArray dx dt)
      (fun n _ => Rusanov.musclSsprk3Step (finGrid n) dx dt FiniteVolume.minmod) :=
  fun _ _ _ _ h => musclSsprk3StepArray_refines dx dt h

/-- 3a. After `k` kernel MUSCL Euler steps (in `ℝ`) every entry stays in the initial bounds `[m, M]`. -/
theorem run_musclEulerStepArray_bounds (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    EntriesBetween m M (run (musclEulerStepArray dx dt) k a) :=
  run_entriesBetween (musclEulerStepArray_size dx dt) (musclEulerStepArray_refinedBy dx dt)
    (fun _ _ u k hu => (Rusanov.musclEulerStep_iterate_stable _ dx dt m M _ FiniteVolume.minmod_minmodBounded
      hdx hdt hcfl u hu k).1) hb k

/-- 3b. After `k` kernel MUSCL SSPRK3 steps (in `ℝ`) every entry stays in the initial bounds `[m, M]`. -/
theorem run_musclSsprk3StepArray_bounds (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    EntriesBetween m M (run (musclSsprk3StepArray dx dt) k a) :=
  run_entriesBetween (musclSsprk3StepArray_size dx dt) (musclSsprk3StepArray_refinedBy dx dt)
    (fun _ _ u k hu => (Rusanov.musclSsprk3Step_iterate_stable _ dx dt m M _ FiniteVolume.minmod_minmodBounded
      hdx hdt hcfl u hu k).1) hb k

/-- 3c. `k` kernel MUSCL Euler steps (in `ℝ`) keep the sum of the entries when `dx ≠ 0`. -/
theorem run_musclEulerStepArray_sum (dx dt : ℝ) (hdx : dx ≠ 0) (a : Array ℝ) (k : ℕ) :
    sumArray (run (musclEulerStepArray dx dt) k a) = sumArray a :=
  run_sumArray (musclEulerStepArray_size dx dt) (musclEulerStepArray_refinedBy dx dt)
    (fun _ _ u => Rusanov.musclEulerStep_sum _ dx dt _ hdx u) a k

/-- 3c. `k` kernel MUSCL SSPRK3 steps (in `ℝ`) keep the sum of the entries when `dx ≠ 0`. -/
theorem run_musclSsprk3StepArray_sum (dx dt : ℝ) (hdx : dx ≠ 0) (a : Array ℝ) (k : ℕ) :
    sumArray (run (musclSsprk3StepArray dx dt) k a) = sumArray a :=
  run_sumArray (musclSsprk3StepArray_size dx dt) (musclSsprk3StepArray_refinedBy dx dt)
    (fun _ _ u => Rusanov.musclSsprk3Step_sum _ dx dt _ hdx u) a k

/-- 3d. `k` kernel MUSCL Euler steps (in `ℝ`) do not increase the periodic total variation of the entries. -/
theorem run_musclEulerStepArray_totalVariation_le (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    totalVariationArray (run (musclEulerStepArray dx dt) k a) ≤ totalVariationArray a :=
  run_totalVariationArray_le (musclEulerStepArray_size dx dt) (musclEulerStepArray_refinedBy dx dt)
    (fun _ _ u k hu => (Rusanov.musclEulerStep_iterate_stable _ dx dt m M _ FiniteVolume.minmod_minmodBounded
      hdx hdt hcfl u hu k).2) hb k

/-- 3d. `k` kernel MUSCL SSPRK3 steps (in `ℝ`) do not increase the periodic total variation of the entries. -/
theorem run_musclSsprk3StepArray_totalVariation_le (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    totalVariationArray (run (musclSsprk3StepArray dx dt) k a) ≤ totalVariationArray a :=
  run_totalVariationArray_le (musclSsprk3StepArray_size dx dt) (musclSsprk3StepArray_refinedBy dx dt)
    (fun _ _ u k hu => (Rusanov.musclSsprk3Step_iterate_stable _ dx dt m M _ FiniteVolume.minmod_minmodBounded
      hdx hdt hcfl u hu k).2) hb k

end CFDLean.Exec
