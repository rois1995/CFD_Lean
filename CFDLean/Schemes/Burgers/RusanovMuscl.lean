import CFDLean.Discrete.Periodic.Muscl
import CFDLean.Schemes.Burgers.RusanovSSP

/-! Burgers B3-K (Rusanov part) and B3-S: the Burgers Rusanov flux is Lipschitz on bounded states with constant
`2 max(|m|, |M|)` in each argument. With a limiter in the minmod region and `6 · dt · max(|m|, |M|) ≤ dx` the
MUSCL-Rusanov scheme with Forward Euler, SSPRK2 or SSPRK3 keeps the bounds of the initial state and does not increase
the total variation for every number of steps. All stability results are compositions of the generic MUSCL theorems
with the SSP results of `CFDLean.Time.SSP`. -/
noncomputable section
namespace CFDLean.Burgers.Rusanov

open Scalar Periodic Scalar.FiniteVolume
open scoped BigOperators

variable {I : Type*}

theorem waveSpeed_abs_le (A a b : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ A) : |waveSpeed a b| ≤ A := by
  unfold waveSpeed
  rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg a))]
  exact max_le ha hb

/-- B3-K: the Rusanov flux is `2A`-Lipschitz in the left state on states with `|·| ≤ A`. -/
theorem eval_lipschitz_left (A a a' b : ℝ) (ha : |a| ≤ A) (ha' : |a'| ≤ A) (hb : |b| ≤ A) :
    |eval a b - eval a' b| ≤ 2 * A * |a - a'| := by
  have e : eval a b - eval a' b = (a - a') * (a + a') / 4 + waveSpeed a b * (a - a') / 2 +
      (waveSpeed a' b - waveSpeed a b) * (b - a') / 2 := by
    simp only [eval, physicalFlux]
    ring
  have hs : |waveSpeed a' b - waveSpeed a b| ≤ |a - a'| := by
    unfold waveSpeed
    rw [abs_sub_comm a a']
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_abs_sub_abs_le_abs_sub a' a)
  have hw := waveSpeed_abs_le A a b ha hb
  have h1 : |a + a'| ≤ 2 * A := (abs_add_le _ _).trans (by linarith)
  have h2 : |b - a'| ≤ 2 * A := (abs_sub_le b 0 a').trans (by simp only [sub_zero, zero_sub, abs_neg]; linarith)
  have t1 : |(a - a') * (a + a') / 4| ≤ |a - a'| * (2 * A) / 4 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    gcongr
  have t2 : |waveSpeed a b * (a - a') / 2| ≤ A * |a - a'| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
  have t3 : |(waveSpeed a' b - waveSpeed a b) * (b - a') / 2| ≤ |a - a'| * (2 * A) / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
  rw [e]
  refine (abs_add_three _ _ _).trans ?_
  linarith

/-- B3-K: the Rusanov flux is `2A`-Lipschitz in the right state on states with `|·| ≤ A`. -/
theorem eval_lipschitz_right (A a b b' : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ A) (hb' : |b'| ≤ A) :
    |eval a b - eval a b'| ≤ 2 * A * |b - b'| := by
  have e : eval a b - eval a b' = (b - b') * (b + b') / 4 - waveSpeed a b * (b - b') / 2 +
      (waveSpeed a b' - waveSpeed a b) * (b' - a) / 2 := by
    simp only [eval, physicalFlux]
    ring
  have hs : |waveSpeed a b' - waveSpeed a b| ≤ |b - b'| := by
    unfold waveSpeed
    rw [max_comm |a| |b'|, max_comm |a| |b|, abs_sub_comm b b']
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_abs_sub_abs_le_abs_sub b' b)
  have hw := waveSpeed_abs_le A a b ha hb
  have h1 : |b + b'| ≤ 2 * A := (abs_add_le _ _).trans (by linarith)
  have h2 : |b' - a| ≤ 2 * A := (abs_sub_le b' 0 a).trans (by simp only [sub_zero, zero_sub, abs_neg]; linarith)
  have t1 : |(b - b') * (b + b') / 4| ≤ |b - b'| * (2 * A) / 4 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    gcongr
  have t2 : |-(waveSpeed a b * (b - b') / 2)| ≤ A * |b - b'| / 2 := by
    rw [abs_neg, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
  have t3 : |(waveSpeed a b' - waveSpeed a b) * (b' - a) / 2| ≤ |b - b'| * (2 * A) / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
  rw [e, sub_eq_add_neg]
  refine (abs_add_three _ _ _).trans ?_
  linarith

theorem abs_le_max_of_bounds (m M x : ℝ) (hx : m ≤ x ∧ x ≤ M) : |x| ≤ max |m| |M| := by
  have h1 := neg_abs_le m
  have h2 := le_max_left |m| |M|
  have h3 := le_abs_self M
  have h4 := le_max_right |m| |M|
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- B3-K: Lipschitz certificate of the Burgers Rusanov flux on states between `m` and `M`. -/
theorem lipschitzOnBounds (m M : ℝ) :
    LipschitzOnBounds numericalFlux m M (2 * max |m| |M|) (2 * max |m| |M|) :=
  ⟨fun a a' b h1 h2 h3 h4 h5 h6 => eval_lipschitz_left _ a a' b (abs_le_max_of_bounds m M a ⟨h1, h2⟩)
      (abs_le_max_of_bounds m M a' ⟨h3, h4⟩) (abs_le_max_of_bounds m M b ⟨h5, h6⟩),
    fun a b b' h1 h2 h3 h4 h5 h6 => eval_lipschitz_right _ a b b' (abs_le_max_of_bounds m M a ⟨h1, h2⟩)
      (abs_le_max_of_bounds m M b ⟨h3, h4⟩) (abs_le_max_of_bounds m M b' ⟨h5, h6⟩)⟩

/-- The MUSCL-Rusanov Forward-Euler map with limiter `φ`. -/
def musclEulerStep (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) : (I → ℝ) → I → ℝ :=
  Time.ForwardEuler.step dt (musclRhs g dx numericalFlux φ)

theorem cfl_of_six (dx dt m M : ℝ) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) :
    dt * (3 / 2 * (2 * max |m| |M| + 2 * max |m| |M|)) ≤ dx := by
  linarith

/-- B3-S: under `6 · dt · max(|m|, |M|) ≤ dx` the MUSCL-Rusanov Forward-Euler step keeps the bounds. -/
theorem musclEulerStep_mem (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    musclEulerStep g dx dt φ u ∈ boundedStates m M :=
  muscl_step_mem g numericalFlux φ hφ monotone m M _ _ (lipschitzOnBounds m M) dx dt hdx hdt
    (cfl_of_six dx dt m M hcfl) u hu

/-- B3-S: under `6 · dt · max(|m|, |M|) ≤ dx` the MUSCL-Rusanov Forward-Euler step does not increase the total
variation. -/
theorem musclEulerStep_totalVariation_le [Fintype I] (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : MinmodBounded φ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) :
    totalVariation g (musclEulerStep g dx dt φ u) ≤ totalVariation g u :=
  muscl_step_totalVariation_le g numericalFlux φ hφ monotone m M _ _ (lipschitzOnBounds m M) dx dt hdx hdt
    (cfl_of_six dx dt m M hcfl) u hu

/-- B3-S with the minmod limiter. -/
theorem musclEulerStep_minmod_mem (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    musclEulerStep g dx dt minmod u ∈ boundedStates m M :=
  musclEulerStep_mem g dx dt m M minmod minmod_minmodBounded hdx hdt hcfl u hu

/-- B3-S with the minmod limiter. -/
theorem musclEulerStep_minmod_totalVariation_le [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    totalVariation g (musclEulerStep g dx dt minmod u) ≤ totalVariation g u :=
  musclEulerStep_totalVariation_le g dx dt m M minmod minmod_minmodBounded hdx hdt hcfl u hu

/-! ### B3-S: multi-step stability -/

/-- One SSPRK2 step of the MUSCL-Rusanov scheme. -/
def musclSsprk2Step (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) : (I → ℝ) → I → ℝ :=
  Time.SSP.ssprk2 (musclEulerStep g dx dt φ)

/-- One SSPRK3 step of the MUSCL-Rusanov scheme. -/
def musclSsprk3Step (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) : (I → ℝ) → I → ℝ :=
  Time.SSP.ssprk3 (musclEulerStep g dx dt φ)

/-- B3-S: bounds and total variation after `n` MUSCL-Rusanov Forward-Euler steps. -/
theorem musclEulerStep_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : MinmodBounded φ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclEulerStep g dx dt φ)^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclEulerStep g dx dt φ)^[n] u) ≤ totalVariation g u :=
  ⟨Time.SSP.iterate_mem _ _ (musclEulerStep_mem g dx dt m M φ hφ hdx hdt hcfl) u hu n,
    Time.SSP.iterate_le _ _ _ (musclEulerStep_mem g dx dt m M φ hφ hdx hdt hcfl)
      (musclEulerStep_totalVariation_le g dx dt m M φ hφ hdx hdt hcfl) u hu n⟩

/-- B3-S: bounds and total variation after `n` MUSCL-Rusanov SSPRK2 steps. -/
theorem musclSsprk2Step_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : MinmodBounded φ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk2Step g dx dt φ)^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk2Step g dx dt φ)^[n] u) ≤ totalVariation g u := by
  have hE := musclEulerStep_mem g dx dt m M φ hφ hdx hdt hcfl
  have hS := boundedStates_convex (I := I) m M
  have hT : ∀ v ∈ boundedStates m M, musclSsprk2Step g dx dt φ v ∈ boundedStates m M :=
    fun v hv => Time.SSP.ssprk2_mem _ _ hS hE v hv
  exact ⟨Time.SSP.iterate_mem _ _ hT u hu n, Time.SSP.iterate_le _ _ _ hT
    (fun v hv => Time.SSP.ssprk2_le _ _ _ (totalVariation_convexOn g _ hS) hE
      (musclEulerStep_totalVariation_le g dx dt m M φ hφ hdx hdt hcfl) v hv) u hu n⟩

/-- B3-S: bounds and total variation after `n` MUSCL-Rusanov SSPRK3 steps. -/
theorem musclSsprk3Step_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : MinmodBounded φ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk3Step g dx dt φ)^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk3Step g dx dt φ)^[n] u) ≤ totalVariation g u := by
  have hE := musclEulerStep_mem g dx dt m M φ hφ hdx hdt hcfl
  have hS := boundedStates_convex (I := I) m M
  have hT : ∀ v ∈ boundedStates m M, musclSsprk3Step g dx dt φ v ∈ boundedStates m M :=
    fun v hv => Time.SSP.ssprk3_mem _ _ hS hE v hv
  exact ⟨Time.SSP.iterate_mem _ _ hT u hu n, Time.SSP.iterate_le _ _ _ hT
    (fun v hv => Time.SSP.ssprk3_le _ _ _ (totalVariation_convexOn g _ hS) hE
      (musclEulerStep_totalVariation_le g dx dt m M φ hφ hdx hdt hcfl) v hv) u hu n⟩

/-- B3-S with the minmod limiter: bounds and total variation after `n` SSPRK3 steps. -/
theorem musclSsprk3Step_minmod_iterate_stable [Fintype I] (g : Grid I) (dx dt m M : ℝ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (hcfl : 6 * (dt * max |m| |M|) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) (n : ℕ) :
    (musclSsprk3Step g dx dt minmod)^[n] u ∈ boundedStates m M ∧
      totalVariation g ((musclSsprk3Step g dx dt minmod)^[n] u) ≤ totalVariation g u :=
  musclSsprk3Step_iterate_stable g dx dt m M minmod minmod_minmodBounded hdx hdt hcfl u hu n

/-- The MUSCL-Rusanov Euler map keeps the total sum. -/
theorem musclEulerStep_sum [Fintype I] (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) (hdx : dx ≠ 0) (u : I → ℝ) :
    ∑ i, musclEulerStep g dx dt φ u i = ∑ i, u i :=
  Time.ForwardEuler.step_sum dt _ u (musclRhs_sum_zero g dx hdx numericalFlux φ u)

/-- The MUSCL-Rusanov Euler map keeps constant states. -/
theorem musclEulerStep_constant (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) (c : ℝ) :
    musclEulerStep g dx dt φ (fun _ => c) = fun _ => c :=
  Time.ForwardEuler.step_constant dt _ c (funext fun i => musclRhs_constant g dx numericalFlux φ c i)

/-- B3-S: one MUSCL-Rusanov SSPRK2 step keeps the total sum. -/
theorem musclSsprk2Step_sum [Fintype I] (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) (hdx : dx ≠ 0) (u : I → ℝ) :
    ∑ i, musclSsprk2Step g dx dt φ u i = ∑ i, u i := by
  have h := Time.SSP.ssprk2_linear (musclEulerStep g dx dt φ) totalSum
    (fun v => by simp only [totalSum_apply, musclEulerStep_sum g dx dt φ hdx v]) u
  simp only [totalSum_apply] at h
  exact h

/-- B3-S: one MUSCL-Rusanov SSPRK3 step keeps the total sum. -/
theorem musclSsprk3Step_sum [Fintype I] (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) (hdx : dx ≠ 0) (u : I → ℝ) :
    ∑ i, musclSsprk3Step g dx dt φ u i = ∑ i, u i := by
  have h := Time.SSP.ssprk3_linear (musclEulerStep g dx dt φ) totalSum
    (fun v => by simp only [totalSum_apply, musclEulerStep_sum g dx dt φ hdx v]) u
  simp only [totalSum_apply] at h
  exact h

/-- B3-S: one MUSCL-Rusanov SSPRK2 step keeps constant states. -/
theorem musclSsprk2Step_constant (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) (c : ℝ) :
    musclSsprk2Step g dx dt φ (fun _ => c) = fun _ => c :=
  Time.SSP.ssprk2_fixed _ _ (musclEulerStep_constant g dx dt φ c)

/-- B3-S: one MUSCL-Rusanov SSPRK3 step keeps constant states. -/
theorem musclSsprk3Step_constant (g : Grid I) (dx dt : ℝ) (φ : ℝ → ℝ → ℝ) (c : ℝ) :
    musclSsprk3Step g dx dt φ (fun _ => c) = fun _ => c :=
  Time.SSP.ssprk3_fixed _ _ (musclEulerStep_constant g dx dt φ c)

end CFDLean.Burgers.Rusanov
