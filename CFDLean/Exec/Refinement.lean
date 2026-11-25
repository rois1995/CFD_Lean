import CFDLean.Schemes.Burgers.RusanovSSP
import CFDLean.Exec.RealScalar

/-! Burgers E0-R, E0-S, E0-N, E0-D, E0-T: the array kernel of `CFDLean.Exec.Kernel`, instantiated at `ℝ`, computes the mathematical Rusanov scheme of
`CFDLean.Burgers.Rusanov` on the periodic grid `Fin n`. The stability and conservation theorems of the scheme then
transfer to the arrays the kernel produces. -/
noncomputable section
namespace CFDLean.Exec

open _root_.CFDLean.Scalar Periodic Burgers
open scoped BigOperators

theorem rusanov_eq (uL uR : ℝ) : Scalar.rusanov uL uR = Rusanov.eval uL uR := by
  simp only [Scalar.rusanov, Scalar.burgersFlux, Rusanov.eval, Rusanov.waveSpeed, physicalFlux]
  change (uL * uL / 2 + uR * uR / 2) / 2 - max |uL| |uR| / 2 * (uR - uL) = _
  ring

/-! ### The periodic grid on `Fin n` -/

/-- The periodic grid on `Fin n`: the next cell of `i` is `i + 1` (mod `n`). -/
def finGrid (n : ℕ) [NeZero n] : Grid (Fin n) := ⟨Equiv.addRight 1⟩

theorem finGrid_next_val {n : ℕ} [NeZero n] (i : Fin n) : ((finGrid n).next i).val = (i.val + 1) % n := by
  simp [finGrid, Fin.val_add]

theorem finGrid_prev_val {n : ℕ} [NeZero n] (i : Fin n) : ((finGrid n).prev i).val = (i.val + n - 1) % n := by
  have e : (finGrid n).prev i = i - 1 := by simp [finGrid, Grid.prev, sub_eq_add_neg]
  rw [e, Fin.val_sub, Fin.val_one']
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h1 : n = 1 := by have := NeZero.pos n; omega
    subst h1
    simp
  · rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
    congr 1
    omega

/-! ### Representation of a cell function by an array -/

/-- `a` stores the cell values of `u : Fin n → ℝ`: same size, same entries. -/
def Represents {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) : Prop :=
  ∃ h : a.size = n, ∀ i : Fin n, a[i.val]'(h ▸ i.isLt) = u i

theorem represents_iff_eq_ofFn {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) : Represents a u ↔ a = Array.ofFn u := by
  constructor
  · rintro ⟨hs, hu⟩
    refine Array.ext (by simp [hs]) fun k hk _ => ?_
    simpa using hu ⟨k, hs ▸ hk⟩
  · rintro rfl
    exact ⟨Array.size_ofFn, fun i => by simp⟩

theorem represents_ofFn {n : ℕ} (u : Fin n → ℝ) : Represents (Array.ofFn u) u :=
  (represents_iff_eq_ofFn _ u).2 rfl

/-- Every array represents the function of its own entries. -/
theorem represents_self (a : Array ℝ) : Represents a (fun i : Fin a.size => a[i]) := ⟨rfl, fun _ => rfl⟩

/-- Entry lookup with the index given up to equality. -/
theorem Represents.getElem_eq {n : ℕ} {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u) (k : ℕ)
    (hk : k < a.size) (j : Fin n) (hkj : k = j.val) : a[k] = u j := by
  obtain ⟨_, hu⟩ := h
  subst hkj
  exact hu j

/-! ### Refinement of the one-step maps -/

/-- 1. The array Euler step computes the Rusanov Euler map on `finGrid n`. -/
theorem eulerStepArray_refines {n : ℕ} [NeZero n] (dx dt : ℝ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) : Represents (eulerStepArray dx dt a) (Rusanov.eulerStep (finGrid n) dx dt u) := by
  have hs : a.size = n := h.1
  refine ⟨Array.size_ofFn.trans hs, fun i => ?_⟩
  simp only [eulerStepArray, Array.getElem_ofFn, Fin.getElem_fin]
  rw [h.getElem_eq _ _ i rfl, h.getElem_eq _ _ ((finGrid n).next i) (by rw [finGrid_next_val, hs]),
    h.getElem_eq _ _ ((finGrid n).prev i) (by rw [finGrid_prev_val, hs])]
  simp only [Rusanov.eulerStep, Time.ForwardEuler.step, FiniteVolume.rhs, FiniteVolume.interfaceFlux,
    Grid.next_prev, rusanov_eq]
  rfl

/-- 2. The array linear combination computes the pointwise linear combination. -/
theorem axpby_refines {n : ℕ} (a b : ℝ) {x y : Array ℝ} {u v : Fin n → ℝ} (hx : Represents x u)
    (hy : Represents y v) : Represents (axpby a x b y) (a • u + b • v) := by
  obtain ⟨hxs, hxu⟩ := hx
  obtain ⟨hys, hyv⟩ := hy
  refine ⟨by simp [axpby, hxs, hys], fun i => ?_⟩
  simp only [axpby, Array.getElem_zipWith, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxu, hyv]

/-- 3a. The array SSPRK2 step computes the Rusanov SSPRK2 map on `finGrid n`. -/
theorem ssprk2StepArray_refines {n : ℕ} [NeZero n] (dx dt : ℝ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) : Represents (ssprk2StepArray dx dt a) (Rusanov.ssprk2Step (finGrid n) dx dt u) :=
  axpby_refines _ _ h (eulerStepArray_refines dx dt (eulerStepArray_refines dx dt h))

/-- 3b. The array SSPRK3 step computes the Rusanov SSPRK3 map on `finGrid n`. -/
theorem ssprk3StepArray_refines {n : ℕ} [NeZero n] (dx dt : ℝ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) : Represents (ssprk3StepArray dx dt a) (Rusanov.ssprk3Step (finGrid n) dx dt u) :=
  axpby_refines _ _ h (eulerStepArray_refines dx dt
    (axpby_refines _ _ h (eulerStepArray_refines dx dt (eulerStepArray_refines dx dt h))))

/-- 4. Running a step that refines `T` for `k` steps refines `T^[k]`. -/
theorem run_refines {n : ℕ} {step : Array ℝ → Array ℝ} {T : (Fin n → ℝ) → Fin n → ℝ}
    (hT : ∀ a u, Represents a u → Represents (step a) (T u)) (k : ℕ) {a : Array ℝ} {u : Fin n → ℝ}
    (h : Represents a u) : Represents (run step k a) (T^[k] u) := by
  induction k generalizing a u with
  | zero => exact h
  | succ k ih => exact ih (hT a u h)

/-! ### Sizes -/

theorem run_size {step : Array ℝ → Array ℝ} (hstep : ∀ a, (step a).size = a.size) (k : ℕ) (a : Array ℝ) :
    (run step k a).size = a.size := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => exact (ih (step a)).trans (hstep a)

theorem eulerStepArray_size (dx dt : ℝ) (a : Array ℝ) : (eulerStepArray dx dt a).size = a.size := by
  simp [eulerStepArray]

theorem axpby_size (a b : ℝ) (x y : Array ℝ) : (axpby a x b y).size = min x.size y.size := by
  simp [axpby]

theorem ssprk3StepArray_size (dx dt : ℝ) (a : Array ℝ) : (ssprk3StepArray dx dt a).size = a.size := by
  simp [ssprk3StepArray, axpby_size, eulerStepArray_size]

/-! ### Diagnostics against their specifications -/

theorem sumArray_eq {n : ℕ} {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u) : sumArray a = ∑ i, u i := by
  rw [(represents_iff_eq_ofFn a u).1 h, sumArray, ← Array.sum_toList, Array.toList_ofFn, List.sum_ofFn]

theorem totalVariationArray_eq {n : ℕ} [NeZero n] {a : Array ℝ} {u : Fin n → ℝ} (h : Represents a u) :
    totalVariationArray a = FiniteVolume.totalVariation (finGrid n) u := by
  have hs : a.size = n := h.1
  unfold totalVariationArray FiniteVolume.totalVariation
  refine sumArray_eq ⟨Array.size_ofFn.trans hs, fun i => ?_⟩
  simp only [Array.getElem_ofFn, Fin.getElem_fin]
  rw [h.getElem_eq _ _ i rfl, h.getElem_eq _ _ ((finGrid n).next i) (by rw [finGrid_next_val, hs])]
  rfl

/-! ### 5. Transfer corollaries -/

/-- Every entry of the array lies in `[m, M]`. -/
def EntriesBetween (m M : ℝ) (a : Array ℝ) : Prop := ∀ (i : ℕ) (hi : i < a.size), m ≤ a[i] ∧ a[i] ≤ M

/-- The cell function of an array whose entries lie in `[m, M]` is a bounded state. -/
theorem self_mem_boundedStates {m M : ℝ} {a : Array ℝ} (hb : EntriesBetween m M a) :
    (fun i : Fin a.size => a[i]) ∈ FiniteVolume.boundedStates m M :=
  fun j => hb j.val j.isLt

/-- A scheme on every periodic grid `Fin n` (`n ≠ 0`) that the kernel step `step` refines. -/
def RefinedBy (step : Array ℝ → Array ℝ) (T : ∀ n [NeZero n], (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ n [NeZero n] a (u : Fin n → ℝ), Represents a u → Represents (step a) (T n u)

/-- Generic transfer of the bounds: if the refined scheme keeps `[m, M]` for every number of steps, so does `run`. -/
theorem run_entriesBetween {step : Array ℝ → Array ℝ} {T : ∀ n [NeZero n], (Fin n → ℝ) → Fin n → ℝ}
    (hstep : ∀ a, (step a).size = a.size) (hT : RefinedBy step T) {m M : ℝ}
    (hTb : ∀ n [NeZero n] (u : Fin n → ℝ) k, u ∈ FiniteVolume.boundedStates m M →
      (T n)^[k] u ∈ FiniteVolume.boundedStates m M)
    {a : Array ℝ} (hb : EntriesBetween m M a) (k : ℕ) : EntriesBetween m M (run step k a) := by
  intro i hi
  have hs := run_size hstep k a
  have : NeZero a.size := ⟨by omega⟩
  rw [(run_refines (hT a.size) k (represents_self a)).getElem_eq i hi ⟨i, by omega⟩ rfl]
  exact hTb a.size _ k (self_mem_boundedStates hb) ⟨i, by omega⟩

/-- Generic transfer of conservation: if the refined scheme keeps `∑ i, u i`, `run` keeps `sumArray`. -/
theorem run_sumArray {step : Array ℝ → Array ℝ} {T : ∀ n [NeZero n], (Fin n → ℝ) → Fin n → ℝ}
    (hstep : ∀ a, (step a).size = a.size) (hT : RefinedBy step T)
    (hTs : ∀ n [NeZero n] (u : Fin n → ℝ), ∑ i, T n u i = ∑ i, u i) (a : Array ℝ) (k : ℕ) :
    sumArray (run step k a) = sumArray a := by
  rcases Nat.eq_zero_or_pos a.size with h0 | hpos
  · rw [Array.eq_empty_of_size_eq_zero ((run_size hstep k a).trans h0), Array.eq_empty_of_size_eq_zero h0]
  · have : NeZero a.size := ⟨by omega⟩
    rw [sumArray_eq (run_refines (hT a.size) k (represents_self a)), sumArray_eq (represents_self a)]
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hTs, ih]

/-- Generic transfer of the total-variation bound for bounded initial data. -/
theorem run_totalVariationArray_le {step : Array ℝ → Array ℝ}
    {T : ∀ n [NeZero n], (Fin n → ℝ) → Fin n → ℝ}
    (hstep : ∀ a, (step a).size = a.size) (hT : RefinedBy step T) {m M : ℝ}
    (hTv : ∀ n [NeZero n] (u : Fin n → ℝ) k, u ∈ FiniteVolume.boundedStates m M →
      FiniteVolume.totalVariation (finGrid n) ((T n)^[k] u) ≤ FiniteVolume.totalVariation (finGrid n) u)
    {a : Array ℝ} (hb : EntriesBetween m M a) (k : ℕ) :
    totalVariationArray (run step k a) ≤ totalVariationArray a := by
  rcases Nat.eq_zero_or_pos a.size with h0 | hpos
  · rw [Array.eq_empty_of_size_eq_zero ((run_size hstep k a).trans h0), Array.eq_empty_of_size_eq_zero h0]
  · have : NeZero a.size := ⟨by omega⟩
    rw [totalVariationArray_eq (run_refines (hT a.size) k (represents_self a)),
      totalVariationArray_eq (represents_self a)]
    exact hTv a.size _ k (self_mem_boundedStates hb)

theorem eulerStepArray_refinedBy (dx dt : ℝ) :
    RefinedBy (eulerStepArray dx dt) (fun n _ => Rusanov.eulerStep (finGrid n) dx dt) :=
  fun _ _ _ _ h => eulerStepArray_refines dx dt h

theorem ssprk3StepArray_refinedBy (dx dt : ℝ) :
    RefinedBy (ssprk3StepArray dx dt) (fun n _ => Rusanov.ssprk3Step (finGrid n) dx dt) :=
  fun _ _ _ _ h => ssprk3StepArray_refines dx dt h

/-- 5a. After `k` kernel Euler steps (in `ℝ`) every entry stays in the initial bounds `[m, M]`. -/
theorem run_eulerStepArray_bounds (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    EntriesBetween m M (run (eulerStepArray dx dt) k a) :=
  run_entriesBetween (eulerStepArray_size dx dt) (eulerStepArray_refinedBy dx dt)
    (fun _ _ u k hu => (Rusanov.eulerStep_iterate_stable _ dx dt m M hdx hdt hcfl u hu k).1) hb k

/-- 5b. After `k` kernel SSPRK3 steps (in `ℝ`) every entry stays in the initial bounds `[m, M]`. -/
theorem run_ssprk3StepArray_bounds (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    EntriesBetween m M (run (ssprk3StepArray dx dt) k a) :=
  run_entriesBetween (ssprk3StepArray_size dx dt) (ssprk3StepArray_refinedBy dx dt)
    (fun _ _ u k hu => (Rusanov.ssprk3Step_iterate_stable _ dx dt m M hdx hdt hcfl u hu k).1) hb k

/-- 5c (optional). `k` kernel Euler steps (in `ℝ`) keep the sum of the entries when `dx ≠ 0`. -/
theorem run_eulerStepArray_sum (dx dt : ℝ) (hdx : dx ≠ 0) (a : Array ℝ) (k : ℕ) :
    sumArray (run (eulerStepArray dx dt) k a) = sumArray a :=
  run_sumArray (eulerStepArray_size dx dt) (eulerStepArray_refinedBy dx dt)
    (fun _ _ u => Rusanov.eulerStep_sum _ dx dt hdx u) a k

/-- 5c (optional). `k` kernel SSPRK3 steps (in `ℝ`) keep the sum of the entries when `dx ≠ 0`. -/
theorem run_ssprk3StepArray_sum (dx dt : ℝ) (hdx : dx ≠ 0) (a : Array ℝ) (k : ℕ) :
    sumArray (run (ssprk3StepArray dx dt) k a) = sumArray a :=
  run_sumArray (ssprk3StepArray_size dx dt) (ssprk3StepArray_refinedBy dx dt)
    (fun _ _ u => Rusanov.ssprk3Step_sum _ dx dt hdx u) a k

/-- 5d (optional). `k` kernel Euler steps (in `ℝ`) do not increase the periodic total variation of the entries. -/
theorem run_eulerStepArray_totalVariation_le (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    totalVariationArray (run (eulerStepArray dx dt) k a) ≤ totalVariationArray a :=
  run_totalVariationArray_le (eulerStepArray_size dx dt) (eulerStepArray_refinedBy dx dt)
    (fun _ _ u k hu => (Rusanov.eulerStep_iterate_stable _ dx dt m M hdx hdt hcfl u hu k).2) hb k

/-- 5d (optional). `k` kernel SSPRK3 steps (in `ℝ`) do not increase the periodic total variation of the entries. -/
theorem run_ssprk3StepArray_totalVariation_le (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 2 * (dt * max |m| |M|) ≤ dx) (a : Array ℝ) (hb : EntriesBetween m M a) (k : ℕ) :
    totalVariationArray (run (ssprk3StepArray dx dt) k a) ≤ totalVariationArray a :=
  run_totalVariationArray_le (ssprk3StepArray_size dx dt) (ssprk3StepArray_refinedBy dx dt)
    (fun _ _ u k hu => (Rusanov.ssprk3Step_iterate_stable _ dx dt m M hdx hdt hcfl u hu k).2) hb k

end CFDLean.Exec
