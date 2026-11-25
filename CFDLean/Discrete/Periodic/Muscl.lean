import CFDLean.Discrete.Periodic.Convexity
import CFDLean.Discrete.Periodic.FiniteVolume
import CFDLean.Schemes.Scalar.Monotone
import CFDLean.Schemes.Scalar.Lipschitz
import CFDLean.Time.ForwardEuler
import Mathlib.Tactic

/-! Burgers B3-L, B3-R, B3-I, B3-T: second-order MUSCL reconstruction on a periodic grid with a slope limiter in the
minmod region, for any two-point flux. The Forward-Euler step of the scheme is in Harten's incremental form with
bounded nonnegative coefficients when the flux is monotone and Lipschitz on the bounded states. So under a CFL
hypothesis it keeps the bounds of the old state and does not increase the total variation (the generic lemmas of
`CFDLean.Discrete.Periodic.TotalVariation`). -/
noncomputable section
namespace CFDLean.Scalar.FiniteVolume

open Periodic
open scoped BigOperators

variable {I : Type*}

/-- Limiter certificate (minmod region): the slope has the sign of both differences and is not larger than either. -/
def MinmodBounded (φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b, 0 ≤ φ a b * a ∧ 0 ≤ φ a b * b ∧ |φ a b| ≤ |a| ∧ |φ a b| ≤ |b|

def minmod (a b : ℝ) : ℝ :=
  if 0 < a ∧ 0 < b then min a b else if a < 0 ∧ b < 0 then max a b else 0

def slope (g : Grid I) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  φ (u i - u (g.prev i)) (u (g.next i) - u i)

def leftState (g : Grid I) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ := u i + slope g φ u i / 2

def rightState (g : Grid I) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  u (g.next i) - slope g φ u (g.next i) / 2

def musclFlux (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  nf.eval (leftState g φ u i) (rightState g φ u i)

def musclRhs (g : Grid I) (dx : ℝ) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  -(musclFlux g nf φ u i - musclFlux g nf φ u (g.prev i)) / dx

/-! ### Limiters -/

/-- B3-L: the minmod limiter is in the minmod region. -/
theorem minmod_minmodBounded : MinmodBounded minmod := by
  intro a b
  unfold minmod
  split_ifs with h1 h2
  · have h := lt_min h1.1 h1.2
    rw [abs_of_pos h, abs_of_pos h1.1, abs_of_pos h1.2]
    exact ⟨mul_nonneg h.le h1.1.le, mul_nonneg h.le h1.2.le, min_le_left a b, min_le_right a b⟩
  · have h := max_lt h2.1 h2.2
    rw [abs_of_neg h, abs_of_neg h2.1, abs_of_neg h2.2]
    refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩ <;> linarith [le_max_left a b, le_max_right a b]
  · simp

/-- B3-R: the zero limiter is in the minmod region. -/
theorem zero_minmodBounded : MinmodBounded (fun _ _ => 0) := fun _ _ => by simp

/-- B3-R: with the zero limiter the MUSCL right-hand side is the first-order one. -/
theorem musclRhs_zero (g : Grid I) (dx : ℝ) (nf : NumericalFlux) (u : I → ℝ) (i : I) :
    musclRhs g dx nf (fun _ _ => 0) u i = rhs g dx nf u i := by
  simp [musclRhs, musclFlux, leftState, rightState, slope, rhs, interfaceFlux]

/-! ### Conservation and constant states -/

/-- B3-R: the MUSCL right-hand side sums to zero, for every flux and every limiter. -/
theorem musclRhs_sum_zero [Fintype I] (g : Grid I) (dx : ℝ) (_hdx : dx ≠ 0) (nf : NumericalFlux)
    (φ : ℝ → ℝ → ℝ) (u : I → ℝ) : ∑ i, musclRhs g dx nf φ u i = 0 := by
  simp only [musclRhs, ← Finset.sum_div, Finset.sum_neg_distrib]
  rw [Finset.sum_sub_distrib, g.sum_prev (musclFlux g nf φ u)]
  simp

/-- B3-R: the MUSCL right-hand side vanishes on constant states. No hypothesis on the limiter or on the flux. -/
theorem musclRhs_constant (g : Grid I) (dx : ℝ) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (c : ℝ) (i : I) :
    musclRhs g dx nf φ (fun _ => c) i = 0 := by
  simp [musclRhs, musclFlux, leftState, rightState, slope]

/-! ### Reconstructed states -/

/-- A half slope with the sign of both neighbouring differences, not larger than either, keeps the bounds. -/
theorem half_slope_mem (m M v vl vr s : ℝ) (h1 : 0 ≤ s * (v - vl)) (h2 : 0 ≤ s * (vr - v)) (h3 : |s| ≤ |v - vl|)
    (h4 : |s| ≤ |vr - v|) (hv : m ≤ v ∧ v ≤ M) (hvl : m ≤ vl ∧ vl ≤ M) (hvr : m ≤ vr ∧ vr ≤ M) :
    (m ≤ v + s / 2 ∧ v + s / 2 ≤ M) ∧ (m ≤ v - s / 2 ∧ v - s / 2 ≤ M) := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have e1 : v - vl ≤ 0 := by nlinarith
    have e2 : vr - v ≤ 0 := by nlinarith
    rw [abs_of_neg hs, abs_of_nonpos e1] at h3
    rw [abs_of_neg hs, abs_of_nonpos e2] at h4
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · subst hs
    simp only [zero_div, add_zero, sub_zero]
    exact ⟨hv, hv⟩
  · have e1 : 0 ≤ v - vl := by nlinarith
    have e2 : 0 ≤ vr - v := by nlinarith
    rw [abs_of_pos hs, abs_of_nonneg e1] at h3
    rw [abs_of_pos hs, abs_of_nonneg e2] at h4
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- B3-R: the reconstructed left state of an interface stays in the bounds. -/
theorem leftState_mem (g : Grid I) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ) (m M : ℝ) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) (i : I) : m ≤ leftState g φ u i ∧ leftState g φ u i ≤ M := by
  have h := hφ (u i - u (g.prev i)) (u (g.next i) - u i)
  exact (half_slope_mem m M _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2 (hu i) (hu _) (hu _)).1

/-- B3-R: the reconstructed right state of an interface stays in the bounds. -/
theorem rightState_mem (g : Grid I) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ) (m M : ℝ) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) (i : I) : m ≤ rightState g φ u i ∧ rightState g φ u i ≤ M := by
  have h := hφ (u (g.next i) - u (g.prev (g.next i))) (u (g.next (g.next i)) - u (g.next i))
  exact (half_slope_mem m M _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2 (hu _) (hu _) (hu _)).2

/-! ### Incremental form -/

/-- `d + s₁/2 - s₂/2` with two slopes of the sign of `d`, not larger than `d`: same sign as `d`, at most `3/2 |d|`. -/
theorem slope_combo (d s1 s2 : ℝ) (h1 : 0 ≤ s1 * d) (h1' : |s1| ≤ |d|) (h2 : 0 ≤ s2 * d) (h2' : |s2| ≤ |d|) :
    0 ≤ (d + s1 / 2 - s2 / 2) * d ∧ |d + s1 / 2 - s2 / 2| ≤ 3 / 2 * |d| := by
  rcases lt_trichotomy d 0 with hd | hd | hd
  · have e1 : s1 ≤ 0 := by nlinarith
    have e2 : s2 ≤ 0 := by nlinarith
    rw [abs_of_neg hd, abs_of_nonpos e1] at h1'
    rw [abs_of_neg hd, abs_of_nonpos e2] at h2'
    rw [abs_of_neg hd, abs_le]
    have h : d + s1 / 2 - s2 / 2 ≤ 0 := by linarith
    exact ⟨by nlinarith, by linarith, by linarith⟩
  · subst hd
    simp only [abs_zero, abs_nonpos_iff] at h1' h2'
    simp [h1', h2']
  · have e1 : 0 ≤ s1 := by nlinarith
    have e2 : 0 ≤ s2 := by nlinarith
    rw [abs_of_pos hd, abs_of_nonneg e1] at h1'
    rw [abs_of_pos hd, abs_of_nonneg e2] at h2'
    rw [abs_of_pos hd, abs_le]
    have h : 0 ≤ d + s1 / 2 - s2 / 2 := by linarith
    exact ⟨by nlinarith, by linarith, by linarith⟩

/-- Sign transfer: `x` has the sign of `r`, `r` has the sign of `d`, and `x = 0` when `r = 0`; so `x` has the sign
of `d`. -/
theorem sign_transfer (x r d K : ℝ) (hxr : 0 ≤ x * r) (hrd : 0 ≤ r * d) (hx : |x| ≤ K * |r|) : 0 ≤ x * d := by
  by_cases hr : r = 0
  · subst hr
    simp only [abs_zero, mul_zero, abs_nonpos_iff] at hx
    simp [hx]
  · have hr2 : 0 < r ^ 2 := by positivity
    by_contra h
    have h' : x * d * r ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hr2
    nlinarith [mul_nonneg hxr hrd]

/-- B3-I (iv): a quotient `x / d` with the sign and the size bound of an increment. -/
theorem exists_ratio (x d c : ℝ) (hxd : 0 ≤ x * d) (hx : |x| ≤ c * |d|) (hc : 0 ≤ c) :
    ∃ q, 0 ≤ q ∧ q ≤ c ∧ q * d = x := by
  by_cases hd : d = 0
  · subst hd
    simp only [abs_zero, mul_zero, abs_nonpos_iff] at hx
    exact ⟨0, le_rfl, hc, by simp [hx]⟩
  · have hd2 : 0 < |d| := abs_pos.mpr hd
    refine ⟨x / d, ?_, ?_, div_mul_cancel₀ x hd⟩
    · have e : x / d = x * d / d ^ 2 := by field_simp
      rw [e]
      exact div_nonneg hxd (sq_nonneg d)
    · calc x / d ≤ |x / d| := le_abs_self _
        _ = |x| / |d| := abs_div x d
        _ ≤ c := by rw [div_le_iff₀ hd2]; exact hx

/-- B3-I (i): the jump of the right states across a cell has the sign of `Δ_i` and is at most `3/2 |Δ_i|`. -/
theorem rightState_sub (g : Grid I) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ) (u : I → ℝ) (i : I) :
    0 ≤ (rightState g φ u i - rightState g φ u (g.prev i)) * (u (g.next i) - u i) ∧
      |rightState g φ u i - rightState g φ u (g.prev i)| ≤ 3 / 2 * |u (g.next i) - u i| := by
  have e : rightState g φ u i - rightState g φ u (g.prev i) = (u (g.next i) - u i) +
      φ (u i - u (g.prev i)) (u (g.next i) - u i) / 2 -
      φ (u (g.next i) - u i) (u (g.next (g.next i)) - u (g.next i)) / 2 := by
    simp only [rightState, slope, g.next_prev, g.prev_next]
    ring
  have h1 := hφ (u i - u (g.prev i)) (u (g.next i) - u i)
  have h2 := hφ (u (g.next i) - u i) (u (g.next (g.next i)) - u (g.next i))
  rw [e]
  exact slope_combo _ _ _ h1.2.1 h1.2.2.2 h2.1 h2.2.2.1

/-- B3-I (ii): the jump of the left states across an interface has the sign of `Δ_{i-1}` and is at most
`3/2 |Δ_{i-1}|`. -/
theorem leftState_sub (g : Grid I) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ) (u : I → ℝ) (i : I) :
    0 ≤ (leftState g φ u i - leftState g φ u (g.prev i)) * (u i - u (g.prev i)) ∧
      |leftState g φ u i - leftState g φ u (g.prev i)| ≤ 3 / 2 * |u i - u (g.prev i)| := by
  have e : leftState g φ u i - leftState g φ u (g.prev i) = (u i - u (g.prev i)) +
      φ (u i - u (g.prev i)) (u (g.next i) - u i) / 2 -
      φ (u (g.prev i) - u (g.prev (g.prev i))) (u i - u (g.prev i)) / 2 := by
    simp only [leftState, slope, g.next_prev]
    ring
  have h1 := hφ (u i - u (g.prev i)) (u (g.next i) - u i)
  have h2 := hφ (u (g.prev i) - u (g.prev (g.prev i))) (u i - u (g.prev i))
  rw [e]
  exact slope_combo _ _ _ h1.1 h1.2.2.1 h2.2.1 h2.2.2.2

/-- B3-I (iii): the flux increment in the right state, `-A_i`, has the sign of `Δ_i` and is at most
`3/2 KR |Δ_i|`. -/
theorem flux_right_increment (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ)
    (hmono : MonotoneFlux nf) (m M KL KR : ℝ) (hlip : LipschitzOnBounds nf m M KL KR) (hKR : 0 ≤ KR)
    (u : I → ℝ) (hu : u ∈ boundedStates m M) (i : I) :
    0 ≤ -(nf.eval (leftState g φ u i) (rightState g φ u i) -
        nf.eval (leftState g φ u i) (rightState g φ u (g.prev i))) * (u (g.next i) - u i) ∧
      |-(nf.eval (leftState g φ u i) (rightState g φ u i) -
        nf.eval (leftState g φ u i) (rightState g φ u (g.prev i)))| ≤ 3 / 2 * KR * |u (g.next i) - u i| := by
  have hr := rightState_sub g φ hφ u i
  have hL := leftState_mem g φ hφ m M u hu i
  have hR := rightState_mem g φ hφ m M u hu i
  have hR' := rightState_mem g φ hφ m M u hu (g.prev i)
  have hlipA := hlip.2 _ _ _ hL.1 hL.2 hR.1 hR.2 hR'.1 hR'.2
  rw [← abs_neg] at hlipA
  have hsign : 0 ≤ -(nf.eval (leftState g φ u i) (rightState g φ u i) -
      nf.eval (leftState g φ u i) (rightState g φ u (g.prev i))) *
      (rightState g φ u i - rightState g φ u (g.prev i)) := by
    rcases le_total (rightState g φ u (g.prev i)) (rightState g φ u i) with h | h
    · have := hmono.2 (leftState g φ u i) _ _ h
      nlinarith
    · have := hmono.2 (leftState g φ u i) _ _ h
      nlinarith
  refine ⟨sign_transfer _ _ _ KR hsign hr.1 hlipA, ?_⟩
  have := mul_le_mul_of_nonneg_left hr.2 hKR
  linarith

/-- B3-I (iii): the flux increment in the left state, `B_i`, has the sign of `Δ_{i-1}` and is at most
`3/2 KL |Δ_{i-1}|`. -/
theorem flux_left_increment (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ)
    (hmono : MonotoneFlux nf) (m M KL KR : ℝ) (hlip : LipschitzOnBounds nf m M KL KR) (hKL : 0 ≤ KL)
    (u : I → ℝ) (hu : u ∈ boundedStates m M) (i : I) :
    0 ≤ (nf.eval (leftState g φ u i) (rightState g φ u (g.prev i)) -
        nf.eval (leftState g φ u (g.prev i)) (rightState g φ u (g.prev i))) * (u i - u (g.prev i)) ∧
      |nf.eval (leftState g φ u i) (rightState g φ u (g.prev i)) -
        nf.eval (leftState g φ u (g.prev i)) (rightState g φ u (g.prev i))| ≤
        3 / 2 * KL * |u i - u (g.prev i)| := by
  have hl := leftState_sub g φ hφ u i
  have hL := leftState_mem g φ hφ m M u hu i
  have hL' := leftState_mem g φ hφ m M u hu (g.prev i)
  have hR' := rightState_mem g φ hφ m M u hu (g.prev i)
  have hlipB := hlip.1 _ _ _ hL.1 hL.2 hL'.1 hL'.2 hR'.1 hR'.2
  have hsign : 0 ≤ (nf.eval (leftState g φ u i) (rightState g φ u (g.prev i)) -
      nf.eval (leftState g φ u (g.prev i)) (rightState g φ u (g.prev i))) *
      (leftState g φ u i - leftState g φ u (g.prev i)) := by
    rcases le_total (leftState g φ u (g.prev i)) (leftState g φ u i) with h | h
    · have := hmono.1 _ _ (rightState g φ u (g.prev i)) h
      nlinarith
    · have := hmono.1 _ _ (rightState g φ u (g.prev i)) h
      nlinarith
  refine ⟨sign_transfer _ _ _ KL hsign hl.1 hlipB, ?_⟩
  have := mul_le_mul_of_nonneg_left hl.2 hKL
  linarith

/-- B3-I: the MUSCL Forward-Euler step is in incremental form with nonnegative coefficients bounded by
`dt/dx · 3/2 · KR` and `dt/dx · 3/2 · KL`. -/
theorem muscl_incremental (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (hφ : MinmodBounded φ)
    (hmono : MonotoneFlux nf) (m M KL KR : ℝ) (hlip : LipschitzOnBounds nf m M KL KR) (hKL : 0 ≤ KL)
    (hKR : 0 ≤ KR) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    ∃ C D : I → ℝ,
      (∀ i, 0 ≤ C i ∧ C i ≤ dt / dx * (3 / 2 * KR)) ∧
      (∀ i, 0 ≤ D i ∧ D i ≤ dt / dx * (3 / 2 * KL)) ∧
      Time.ForwardEuler.step dt (musclRhs g dx nf φ) u = incrementalUpdate g C D u := by
  have hA : ∀ i, ∃ q, 0 ≤ q ∧ q ≤ 3 / 2 * KR ∧ q * (u (g.next i) - u i) =
      -(nf.eval (leftState g φ u i) (rightState g φ u i) -
        nf.eval (leftState g φ u i) (rightState g φ u (g.prev i))) := by
    intro i
    have h := flux_right_increment g nf φ hφ hmono m M KL KR hlip hKR u hu i
    exact exists_ratio _ _ _ h.1 h.2 (by positivity)
  have hB : ∀ j, ∃ q, 0 ≤ q ∧ q ≤ 3 / 2 * KL ∧ q * (u (g.next j) - u j) =
      nf.eval (leftState g φ u (g.next j)) (rightState g φ u j) -
        nf.eval (leftState g φ u j) (rightState g φ u j) := by
    intro j
    have h := flux_left_increment g nf φ hφ hmono m M KL KR hlip hKL u hu (g.next j)
    simp only [g.prev_next] at h
    exact exists_ratio _ _ _ h.1 h.2 (by positivity)
  choose qA hqA using hA
  choose qB hqB using hB
  have hr : 0 ≤ dt / dx := div_nonneg hdt hdx.le
  refine ⟨fun i => dt / dx * qA i, fun j => dt / dx * qB j,
    fun i => ⟨mul_nonneg hr (hqA i).1, mul_le_mul_of_nonneg_left (hqA i).2.1 hr⟩,
    fun j => ⟨mul_nonneg hr (hqB j).1, mul_le_mul_of_nonneg_left (hqB j).2.1 hr⟩, funext fun i => ?_⟩
  have a := (hqA i).2.2
  have b := (hqB (g.prev i)).2.2
  simp only [g.next_prev] at b
  simp only [Time.ForwardEuler.step, musclRhs, musclFlux, incrementalUpdate]
  linear_combination (-(dt / dx)) * a + (dt / dx) * b

/-- B3-I needs `0 ≤ KL` and `0 ≤ KR`: on the degenerate interval `m = M = 0` the certificate holds with
`KL = KR = -1`, and then no coefficient `C i` with `0 ≤ C i ≤ dt / dx · 3/2 · KR` exists (one cell, zero flux,
zero limiter, `u = 0`, `dx = dt = 1`). -/
theorem muscl_incremental_false_without_nonneg :
    ¬ (∀ (I : Type) (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ), MinmodBounded φ → MonotoneFlux nf →
      ∀ m M KL KR : ℝ, LipschitzOnBounds nf m M KL KR → ∀ dx dt : ℝ, 0 < dx → 0 ≤ dt → ∀ u : I → ℝ,
      u ∈ boundedStates m M → ∃ C D : I → ℝ, (∀ i, 0 ≤ C i ∧ C i ≤ dt / dx * (3 / 2 * KR)) ∧
        (∀ i, 0 ≤ D i ∧ D i ≤ dt / dx * (3 / 2 * KL)) ∧
        Time.ForwardEuler.step dt (musclRhs g dx nf φ) u = incrementalUpdate g C D u) := by
  intro h
  obtain ⟨C, _, hC, _, _⟩ := h Unit ⟨Equiv.refl _⟩ ⟨fun _ _ => 0⟩ (fun _ _ => 0) zero_minmodBounded
    ⟨fun _ _ _ _ => le_rfl, fun _ _ _ _ => le_rfl⟩ 0 0 (-1) (-1)
    ⟨fun a a' _ h1 h2 h3 h4 _ _ => by rw [le_antisymm h2 h1, le_antisymm h4 h3]; simp,
      fun _ b b' _ _ h3 h4 h5 h6 => by rw [le_antisymm h4 h3, le_antisymm h6 h5]; simp⟩
    1 1 one_pos zero_le_one (fun _ => 0) (fun _ => ⟨le_rfl, le_rfl⟩)
  have h1 := hC ()
  norm_num at h1
  linarith [h1.1, h1.2]

/-! ### One Forward-Euler MUSCL step -/

/-- On a degenerate interval `M ≤ m` a bounded state is constant, so the MUSCL step leaves it unchanged. -/
theorem muscl_step_eq_self_of_le (g : Grid I) (dx : ℝ) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (dt m M : ℝ)
    (u : I → ℝ) (hu : u ∈ boundedStates m M) (hMm : M ≤ m) : Time.ForwardEuler.step dt (musclRhs g dx nf φ) u = u := by
  have hc : u = fun _ => m := funext fun j => le_antisymm (by linarith [(hu j).2]) (hu j).1
  subst hc
  funext i
  simp [Time.ForwardEuler.step, musclRhs_constant]

theorem coeff_sum_le_one (dx dt KL KR c d : ℝ) (hdx : 0 < dx) (hcfl : dt * (3 / 2 * (KL + KR)) ≤ dx)
    (hc : c ≤ dt / dx * (3 / 2 * KR)) (hd : d ≤ dt / dx * (3 / 2 * KL)) : c + d ≤ 1 := by
  have e : dt / dx * (3 / 2 * KR) + dt / dx * (3 / 2 * KL) = dt * (3 / 2 * (KL + KR)) / dx := by ring
  have h : dt * (3 / 2 * (KL + KR)) / dx ≤ 1 := by rw [div_le_one hdx]; exact hcfl
  linarith

/-- B3-T: under `dt · 3/2 · (KL + KR) ≤ dx` one Forward-Euler MUSCL step does not increase the total variation. -/
theorem muscl_step_totalVariation_le [Fintype I] (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ)
    (hφ : MinmodBounded φ) (hmono : MonotoneFlux nf) (m M KL KR : ℝ) (hlip : LipschitzOnBounds nf m M KL KR)
    (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : dt * (3 / 2 * (KL + KR)) ≤ dx) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) :
    totalVariation g (Time.ForwardEuler.step dt (musclRhs g dx nf φ) u) ≤ totalVariation g u := by
  rcases lt_or_ge m M with hmM | hMm
  · obtain ⟨hKL, hKR⟩ := hlip.nonneg hmM
    obtain ⟨C, D, hC, hD, e⟩ := muscl_incremental g nf φ hφ hmono m M KL KR hlip hKL hKR dx dt hdx hdt u hu
    rw [e]
    exact incrementalUpdate_totalVariation_le g C D u (fun i => (hC i).1) (fun i => (hD i).1)
      (fun i => coeff_sum_le_one dx dt KL KR _ _ hdx hcfl (hC i).2 (hD i).2)
  · rw [muscl_step_eq_self_of_le g dx nf φ dt m M u hu hMm]

/-- B3-T: under `dt · 3/2 · (KL + KR) ≤ dx` one Forward-Euler MUSCL step keeps the bounds. -/
theorem muscl_step_mem (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ)
    (hφ : MinmodBounded φ) (hmono : MonotoneFlux nf) (m M KL KR : ℝ) (hlip : LipschitzOnBounds nf m M KL KR)
    (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (hcfl : dt * (3 / 2 * (KL + KR)) ≤ dx) (u : I → ℝ)
    (hu : u ∈ boundedStates m M) :
    Time.ForwardEuler.step dt (musclRhs g dx nf φ) u ∈ boundedStates m M := by
  rcases lt_or_ge m M with hmM | hMm
  · obtain ⟨hKL, hKR⟩ := hlip.nonneg hmM
    obtain ⟨C, D, hC, hD, e⟩ := muscl_incremental g nf φ hφ hmono m M KL KR hlip hKL hKR dx dt hdx hdt u hu
    rw [e]
    intro i
    exact incrementalUpdate_bounds g C D u m M i (hC i).1 (hD _).1
      (coeff_sum_le_one dx dt KL KR _ _ hdx hcfl (hC i).2 (hD _).2) (fun j => (hu j).1) (fun j => (hu j).2)
  · rw [muscl_step_eq_self_of_le g dx nf φ dt m M u hu hMm]
    exact hu

end CFDLean.Scalar.FiniteVolume
