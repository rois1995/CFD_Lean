import CFDLean.Time.ForwardEuler
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

/-! Burgers B2-R, B2-C, B2-N, B2-L: strong-stability-preserving Runge-Kutta steps in Shu-Osher form over a one-step
map `E : V → V` on a real vector space, and the generic composition results. An SSP step is a convex combination of
`E` steps, so it keeps every convex set that `E` keeps and does not increase any convex functional that `E` does not
increase. Nothing here mentions a flux, a grid or Burgers. -/
noncomputable section
namespace CFDLean.Time.SSP

section Iterate

variable {V : Type*}

/-- B2-N: a one-step map that keeps a set keeps it for every number of steps. -/
theorem iterate_mem (T : V → V) (S : Set V) (hT : ∀ u ∈ S, T u ∈ S) (u : V) (hu : u ∈ S) (n : ℕ) :
    T^[n] u ∈ S := by
  induction n with
  | zero => simpa using hu
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hT _ ih

/-- B2-N: a functional that one step does not increase on an invariant set is not increased by `n` steps. -/
theorem iterate_le (T : V → V) (S : Set V) (Φ : V → ℝ) (hT : ∀ u ∈ S, T u ∈ S)
    (hΦT : ∀ u ∈ S, Φ (T u) ≤ Φ u) (u : V) (hu : u ∈ S) (n : ℕ) : Φ (T^[n] u) ≤ Φ u := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (hΦT _ (iterate_mem T S hT u hu k)).trans ih

end Iterate

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- B2-R: two-stage SSP Runge-Kutta step over a one-step map `E`: `½ u + ½ E(E u)`. -/
def ssprk2 (E : V → V) (u : V) : V := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • E (E u)

/-- B2-R: three-stage SSP Runge-Kutta step over a one-step map `E`: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

/-- B2-R: SSPRK2 of a Forward-Euler map is Heun's method. -/
theorem ssprk2_forwardEuler {I : Type*} (dt : ℝ) (L : (I → ℝ) → I → ℝ) (u : I → ℝ) (i : I) :
    ssprk2 (ForwardEuler.step dt L) u i = u i + dt / 2 * (L u i + L (ForwardEuler.step dt L u) i) := by
  have h2 : ForwardEuler.step dt L (ForwardEuler.step dt L u) i =
      ForwardEuler.step dt L u i + dt * L (ForwardEuler.step dt L u) i := rfl
  have h1 : ForwardEuler.step dt L u i = u i + dt * L u i := rfl
  simp only [ssprk2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2, h1]
  ring

/-- B2-C: SSPRK2 keeps every convex set that `E` keeps. -/
theorem ssprk2_mem (E : V → V) (S : Set V) (hS : Convex ℝ S) (hE : ∀ u ∈ S, E u ∈ S) (u : V) (hu : u ∈ S) :
    ssprk2 E u ∈ S :=
  hS hu (hE _ (hE u hu)) (by norm_num) (by norm_num) (by norm_num)

/-- B2-C: SSPRK3 keeps every convex set that `E` keeps. -/
theorem ssprk3_mem (E : V → V) (S : Set V) (hS : Convex ℝ S) (hE : ∀ u ∈ S, E u ∈ S) (u : V) (hu : u ∈ S) :
    ssprk3 E u ∈ S :=
  hS hu (hE _ (hS hu (hE _ (hE u hu)) (by norm_num) (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num)

/-- B2-C: SSPRK2 does not increase a functional that is convex on an invariant set and not increased by `E`. -/
theorem ssprk2_le (E : V → V) (S : Set V) (Φ : V → ℝ) (hΦ : ConvexOn ℝ S Φ) (hE : ∀ u ∈ S, E u ∈ S)
    (hΦE : ∀ u ∈ S, Φ (E u) ≤ Φ u) (u : V) (hu : u ∈ S) : Φ (ssprk2 E u) ≤ Φ u := by
  have h1 := hE u hu
  have h2 := hE _ h1
  have h := hΦ.2 hu h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have a := hΦE u hu
  have b := hΦE _ h1
  simp only [smul_eq_mul] at h
  unfold ssprk2
  linarith

/-- B2-C: SSPRK3 does not increase a functional that is convex on an invariant set and not increased by `E`. -/
theorem ssprk3_le (E : V → V) (S : Set V) (Φ : V → ℝ) (hΦ : ConvexOn ℝ S Φ) (hE : ∀ u ∈ S, E u ∈ S)
    (hΦE : ∀ u ∈ S, Φ (E u) ≤ Φ u) (u : V) (hu : u ∈ S) : Φ (ssprk3 E u) ≤ Φ u := by
  have h1 := hE u hu
  have h2 := hE _ h1
  have hw : (3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u) ∈ S :=
    hΦ.1 hu h2 (by norm_num) (by norm_num) (by norm_num)
  have h3 := hE _ hw
  have c1 := hΦ.2 hu h2 (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
  have c2 := hΦ.2 hu h3 (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num)
  have a := hΦE u hu
  have b := hΦE _ h1
  have c := hΦE _ hw
  simp only [smul_eq_mul] at c1 c2
  unfold ssprk3
  linarith

/-- B2-L: a fixed point of `E` is a fixed point of SSPRK2. -/
theorem ssprk2_fixed (E : V → V) (c : V) (hc : E c = c) : ssprk2 E c = c := by
  rw [ssprk2, hc, hc, ← add_smul]
  norm_num

/-- B2-L: a fixed point of `E` is a fixed point of SSPRK3. -/
theorem ssprk3_fixed (E : V → V) (c : V) (hc : E c = c) : ssprk3 E c = c := by
  have h : (3 / 4 : ℝ) • c + (1 / 4 : ℝ) • c = c := by
    rw [← add_smul]
    norm_num
  rw [ssprk3, hc, hc, h, hc, ← add_smul]
  norm_num

/-- B2-L: a linear functional that `E` keeps is kept by SSPRK2. -/
theorem ssprk2_linear (E : V → V) (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ∀ u, ℓ (E u) = ℓ u) (u : V) :
    ℓ (ssprk2 E u) = ℓ u := by
  simp only [ssprk2, map_add, map_smul, hℓ, smul_eq_mul]
  ring

/-- B2-L: a linear functional that `E` keeps is kept by SSPRK3. -/
theorem ssprk3_linear (E : V → V) (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ∀ u, ℓ (E u) = ℓ u) (u : V) :
    ℓ (ssprk3 E u) = ℓ u := by
  simp only [ssprk3, map_add, map_smul, hℓ, smul_eq_mul]
  ring

end CFDLean.Time.SSP
