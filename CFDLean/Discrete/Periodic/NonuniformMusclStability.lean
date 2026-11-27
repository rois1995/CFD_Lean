import CFDLean.Discrete.Periodic.Limiters
import CFDLean.Discrete.Periodic.NonuniformMuscl

/-! FVN-R and FVN-M: the scalar MUSCL step of `NonuniformMuscl` on a non-uniform periodic 1D mesh, with a limiter
`φ` that is `SlopeBounded θ` and a mesh with mesh ratio `θ`.

At face `i` put `p i = w i / (w i + w (next i))` and `q i = w (next i) / (w i + w (next i))`, and
`Δ i = u (next i) - u i`. The rescaled differences turn the slope rules into

```text
|s i / 2|        ≤ θ · p i · |Δ i|   (forward difference of cell i)
|s (next i) / 2| ≤ θ · q i · |Δ i|   (backward difference of cell next i)
```

with the sign of `Δ i`. The mesh ratio gives `θ p i ≤ 1` and `θ q i ≤ 1`, so the face states stay in the bounds
(FVN-R), and the jumps of the right and left states across face `i` are `Δ i` times a factor in
`[1 − θ q i, 1 + θ p i]` and `[1 − θ p i, 1 + θ q i]`. The step is then in Harten's incremental form with
`C i ≤ (dt / w i) KR (1 + θ p i)` and `D i ≤ (dt / w (next i)) KL (1 + θ q i)`, and the generic lemmas
`incrementalUpdate_bounds` and `incrementalUpdate_totalVariation_le` give FVN-M. On a degenerate interval
`hi ≤ lo` the state is constant and the step is the identity. -/
noncomputable section
namespace CFDLean.FV1D.Nonuniform

open Periodic
open CFDLean.Scalar (NumericalFlux MonotoneFlux LipschitzOnBounds)
open CFDLean.Scalar.FiniteVolume (SlopeBounded boundedStates totalVariation incrementalUpdate incrementalUpdate_bounds
  incrementalUpdate_totalVariation_le half_slope_mem_two sign_transfer exists_ratio)

variable {I : Type*}

/-! ### Mesh ratio -/

/-- Under the mesh ratio `θ`, `θ p i ≤ 1` with `p i = w i / (w i + w (next i))`. -/
theorem meshRatio_p_le_one (m : Mesh1D I) (θ : ℝ) (hr : m.MeshRatio θ) (i : I) :
    θ * (m.width i / (m.width i + m.width (m.grid.next i))) ≤ 1 := by
  have hw := m.width_pos i
  have hs : 0 < m.width i + m.width (m.grid.next i) := add_pos hw (m.width_pos _)
  rw [← mul_div_assoc, div_le_one hs]
  rcases le_total 0 θ with hθ | hθ
  · exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ).trans (hr i)
  · nlinarith [m.width_pos (m.grid.next i)]

/-- Under the mesh ratio `θ`, `θ q i ≤ 1` with `q i = w (next i) / (w i + w (next i))`. -/
theorem meshRatio_q_le_one (m : Mesh1D I) (θ : ℝ) (hr : m.MeshRatio θ) (i : I) :
    θ * (m.width (m.grid.next i) / (m.width i + m.width (m.grid.next i))) ≤ 1 := by
  have hw := m.width_pos (m.grid.next i)
  have hs : 0 < m.width i + m.width (m.grid.next i) := add_pos (m.width_pos i) hw
  rw [← mul_div_assoc, div_le_one hs]
  rcases le_total 0 θ with hθ | hθ
  · exact (mul_le_mul_of_nonneg_left (le_max_right _ _) hθ).trans (hr i)
  · nlinarith [m.width_pos i]

/-! ### Slope bounds -/

/-- A slope with the sign of `c · d` and at most `θ |c · d|`, `0 < c`, has the sign of `d` and is at most
`θ c |d|`. -/
private theorem scaled_bound (θ s c d : ℝ) (hc : 0 < c) (h1 : 0 ≤ s * (c * d)) (h2 : |s| ≤ θ * |c * d|) :
    0 ≤ s * d ∧ |s| ≤ θ * c * |d| := by
  refine ⟨?_, ?_⟩
  · have e : s * (c * d) = c * (s * d) := by ring
    rw [e] at h1
    exact (mul_nonneg_iff_of_pos_left hc).mp h1
  · rw [abs_mul, abs_of_pos hc, ← mul_assoc] at h2
    exact h2

/-- `w / ((w' + w'') / 2) = 2 · (w / (w' + w''))`. -/
private theorem width_div_spacing (w a : ℝ) : w / (a / 2) = 2 * (w / a) := by
  rw [div_div_eq_mul_div]
  ring

/-- Forward difference of cell `i`: the slope has the sign of `Δ i` and `|s i| ≤ 2 θ p i |Δ i|`. -/
private theorem slope_fwd_bound (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (u : I → ℝ)
    (i : I) :
    0 ≤ slope m φ u i * (u (m.grid.next i) - u i) ∧
      |slope m φ u i| ≤ 2 * (θ * (m.width i / (m.width i + m.width (m.grid.next i)))) *
        |u (m.grid.next i) - u i| := by
  have hc : 0 < m.width i / m.spacing i :=
    div_pos (m.width_pos i) (div_pos (add_pos (m.width_pos i) (m.width_pos _)) two_pos)
  have h : 0 ≤ slope m φ u i * fwdDiff m u i ∧ |slope m φ u i| ≤ θ * |fwdDiff m u i| :=
    ⟨(hφ _ _).2.1, (hφ _ _).2.2.2⟩
  simp only [fwdDiff, smul_eq_mul] at h
  have hb := scaled_bound θ _ _ _ hc h.1 h.2
  rw [Mesh1D.spacing, width_div_spacing] at hb
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  ring

/-- Backward difference of cell `next i`: the slope has the sign of `Δ i` and `|s (next i)| ≤ 2 θ q i |Δ i|`. -/
private theorem slope_back_bound (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (u : I → ℝ)
    (i : I) :
    0 ≤ slope m φ u (m.grid.next i) * (u (m.grid.next i) - u i) ∧
      |slope m φ u (m.grid.next i)| ≤ 2 * (θ * (m.width (m.grid.next i) / (m.width i + m.width (m.grid.next i)))) *
        |u (m.grid.next i) - u i| := by
  have hc : 0 < m.width (m.grid.next i) / m.spacing i :=
    div_pos (m.width_pos _) (div_pos (add_pos (m.width_pos i) (m.width_pos _)) two_pos)
  have h : 0 ≤ slope m φ u (m.grid.next i) * backDiff m u (m.grid.next i) ∧
      |slope m φ u (m.grid.next i)| ≤ θ * |backDiff m u (m.grid.next i)| :=
    ⟨(hφ _ _).1, (hφ _ _).2.2.1⟩
  simp only [backDiff, smul_eq_mul, m.grid.prev_next] at h
  have hb := scaled_bound θ _ _ _ hc h.1 h.2
  rw [Mesh1D.spacing, width_div_spacing] at hb
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  ring

/-! ### FVN-R: reconstruction bounds -/

/-- `|s| ≤ 2 α |d|` with `α ≤ 1` gives `|s| ≤ 2 |d|`. -/
private theorem two_bound (s d α : ℝ) (h : |s| ≤ 2 * α * |d|) (hα : α ≤ 1) : |s| ≤ 2 * |d| :=
  h.trans (by nlinarith [abs_nonneg d])

/-- FVN-R: the left state at face `i` stays in the bounds. -/
theorem leftState_mem (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ)
    (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (i : I) :
    lo ≤ leftState m φ u i ∧ leftState m φ u i ≤ hi := by
  have hf := slope_fwd_bound m φ θ hφ u i
  have hb := slope_back_bound m φ θ hφ u (m.grid.prev i)
  have hq := meshRatio_q_le_one m θ hr (m.grid.prev i)
  simp only [m.grid.next_prev] at hb hq
  have e : leftState m φ u i = u i + slope m φ u i / 2 := by
    rw [leftState, smul_eq_mul]
    ring
  rw [e]
  exact (half_slope_mem_two lo hi _ _ _ _ hb.1 hf.1 (two_bound _ _ _ hb.2 hq)
    (two_bound _ _ _ hf.2 (meshRatio_p_le_one m θ hr i)) (hu i) (hu _) (hu _)).1

/-- FVN-R: the right state at face `i` stays in the bounds. -/
theorem rightState_mem (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ)
    (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (i : I) :
    lo ≤ rightState m φ u i ∧ rightState m φ u i ≤ hi := by
  have hb := slope_back_bound m φ θ hφ u i
  have hf := slope_fwd_bound m φ θ hφ u (m.grid.next i)
  have e : rightState m φ u i = u (m.grid.next i) - slope m φ u (m.grid.next i) / 2 := by
    rw [rightState, smul_eq_mul]
    ring
  rw [e]
  exact (half_slope_mem_two lo hi _ _ _ _ hb.1 hf.1
    (two_bound _ _ _ hb.2 (meshRatio_q_le_one m θ hr i))
    (two_bound _ _ _ hf.2 (meshRatio_p_le_one m θ hr _)) (hu _) (hu i) (hu _)).2

/-! ### Jumps of the face states -/

/-- `d + a - b` with `a`, `b` of the sign of `d`, `|a| ≤ α |d|`, `|b| ≤ β |d|` and `β ≤ 1`: same sign as `d`, at
most `(1 + α) |d|`. -/
private theorem combo_bound (d a b α β : ℝ) (ha : 0 ≤ a * d) (ha' : |a| ≤ α * |d|) (hb : 0 ≤ b * d)
    (hb' : |b| ≤ β * |d|) (hβ : β ≤ 1) :
    0 ≤ (d + a - b) * d ∧ |d + a - b| ≤ (1 + α) * |d| := by
  rcases lt_trichotomy d 0 with hd | hd | hd
  · have e1 : a ≤ 0 := by nlinarith
    have e2 : b ≤ 0 := by nlinarith
    rw [abs_of_neg hd, abs_of_nonpos e1] at ha'
    rw [abs_of_neg hd, abs_of_nonpos e2] at hb'
    have hβd : β * -d ≤ -d := by nlinarith
    have h : d + a - b ≤ 0 := by linarith
    rw [abs_of_neg hd, abs_le]
    exact ⟨by nlinarith, by linarith, by linarith⟩
  · subst hd
    simp only [abs_zero, mul_zero, abs_nonpos_iff] at ha' hb'
    simp [ha', hb']
  · have e1 : 0 ≤ a := by nlinarith
    have e2 : 0 ≤ b := by nlinarith
    rw [abs_of_pos hd, abs_of_nonneg e1] at ha'
    rw [abs_of_pos hd, abs_of_nonneg e2] at hb'
    have hβd : β * d ≤ d := by nlinarith
    have h : 0 ≤ d + a - b := by linarith
    rw [abs_of_pos hd, abs_le]
    exact ⟨by nlinarith, by linarith, by linarith⟩

/-- The jump of the right states from face `prev i` to face `i` (reconstructed in cells `i` and `next i`) has the
sign of `Δ i` and is at most `(1 + θ p i) |Δ i|`. -/
private theorem rightState_sub_bound (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (u : I → ℝ) (i : I) :
    0 ≤ (rightState m φ u i - rightState m φ u (m.grid.prev i)) * (u (m.grid.next i) - u i) ∧
      |rightState m φ u i - rightState m φ u (m.grid.prev i)| ≤
        (1 + θ * (m.width i / (m.width i + m.width (m.grid.next i)))) * |u (m.grid.next i) - u i| := by
  have hf := slope_fwd_bound m φ θ hφ u i
  have hb := slope_back_bound m φ θ hφ u i
  have e : rightState m φ u i - rightState m φ u (m.grid.prev i) = (u (m.grid.next i) - u i) +
      slope m φ u i / 2 - slope m φ u (m.grid.next i) / 2 := by
    simp only [rightState, smul_eq_mul, m.grid.next_prev]
    ring
  rw [e]
  refine combo_bound _ _ _ _ _ (by nlinarith [hf.1]) ?_ (by nlinarith [hb.1]) ?_ (meshRatio_q_le_one m θ hr i)
  · rw [abs_div, abs_two]
    linarith [hf.2]
  · rw [abs_div, abs_two]
    linarith [hb.2]

/-- The jump of the left states from face `i` to face `next i` (reconstructed in cells `i` and `next i`) has the
sign of `Δ i` and is at most `(1 + θ q i) |Δ i|`. -/
private theorem leftState_sub_bound (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (u : I → ℝ) (i : I) :
    0 ≤ (leftState m φ u (m.grid.next i) - leftState m φ u i) * (u (m.grid.next i) - u i) ∧
      |leftState m φ u (m.grid.next i) - leftState m φ u i| ≤
        (1 + θ * (m.width (m.grid.next i) / (m.width i + m.width (m.grid.next i)))) *
          |u (m.grid.next i) - u i| := by
  have hf := slope_fwd_bound m φ θ hφ u i
  have hb := slope_back_bound m φ θ hφ u i
  have e : leftState m φ u (m.grid.next i) - leftState m φ u i = (u (m.grid.next i) - u i) +
      slope m φ u (m.grid.next i) / 2 - slope m φ u i / 2 := by
    simp only [leftState, smul_eq_mul]
    ring
  rw [e]
  refine combo_bound _ _ _ _ _ (by nlinarith [hb.1]) ?_ (by nlinarith [hf.1]) ?_ (meshRatio_p_le_one m θ hr i)
  · rw [abs_div, abs_two]
    linarith [hb.2]
  · rw [abs_div, abs_two]
    linarith [hf.2]

/-! ### Flux increments and incremental form -/

/-- The flux increment in the right state at face `i` has the sign of `Δ i` and is at most
`KR (1 + θ p i) |Δ i|`. -/
private theorem flux_right_increment_bound (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (nf : NumericalFlux)
    (hmono : MonotoneFlux nf) (KL KR : ℝ) (hlip : LipschitzOnBounds nf lo hi KL KR) (hKR : 0 ≤ KR) (i : I) :
    0 ≤ -(nf.eval (leftState m φ u i) (rightState m φ u i) -
        nf.eval (leftState m φ u i) (rightState m φ u (m.grid.prev i))) * (u (m.grid.next i) - u i) ∧
      |-(nf.eval (leftState m φ u i) (rightState m φ u i) -
        nf.eval (leftState m φ u i) (rightState m φ u (m.grid.prev i)))| ≤
        KR * (1 + θ * (m.width i / (m.width i + m.width (m.grid.next i)))) * |u (m.grid.next i) - u i| := by
  have hj := rightState_sub_bound m φ θ hφ hr u i
  have hL := leftState_mem m φ θ hφ hr lo hi u hu i
  have hR := rightState_mem m φ θ hφ hr lo hi u hu i
  have hR' := rightState_mem m φ θ hφ hr lo hi u hu (m.grid.prev i)
  have hlipA := hlip.2 _ _ _ hL.1 hL.2 hR.1 hR.2 hR'.1 hR'.2
  rw [← abs_neg] at hlipA
  have hsign : 0 ≤ -(nf.eval (leftState m φ u i) (rightState m φ u i) -
      nf.eval (leftState m φ u i) (rightState m φ u (m.grid.prev i))) *
      (rightState m φ u i - rightState m φ u (m.grid.prev i)) := by
    rcases le_total (rightState m φ u (m.grid.prev i)) (rightState m φ u i) with h | h
    · have := hmono.2 (leftState m φ u i) _ _ h
      nlinarith
    · have := hmono.2 (leftState m φ u i) _ _ h
      nlinarith
  refine ⟨sign_transfer _ _ _ KR hsign hj.1 hlipA, ?_⟩
  have := mul_le_mul_of_nonneg_left hj.2 hKR
  linarith

/-- The flux increment in the left state at face `i` (from `left i` to `left (next i)` with the right state of
face `i`) has the sign of `Δ i` and is at most `KL (1 + θ q i) |Δ i|`. -/
private theorem flux_left_increment_bound (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (nf : NumericalFlux)
    (hmono : MonotoneFlux nf) (KL KR : ℝ) (hlip : LipschitzOnBounds nf lo hi KL KR) (hKL : 0 ≤ KL) (i : I) :
    0 ≤ (nf.eval (leftState m φ u (m.grid.next i)) (rightState m φ u i) -
        nf.eval (leftState m φ u i) (rightState m φ u i)) * (u (m.grid.next i) - u i) ∧
      |nf.eval (leftState m φ u (m.grid.next i)) (rightState m φ u i) -
        nf.eval (leftState m φ u i) (rightState m φ u i)| ≤
        KL * (1 + θ * (m.width (m.grid.next i) / (m.width i + m.width (m.grid.next i)))) *
          |u (m.grid.next i) - u i| := by
  have hj := leftState_sub_bound m φ θ hφ hr u i
  have hL := leftState_mem m φ θ hφ hr lo hi u hu (m.grid.next i)
  have hL' := leftState_mem m φ θ hφ hr lo hi u hu i
  have hR := rightState_mem m φ θ hφ hr lo hi u hu i
  have hlipB := hlip.1 _ _ _ hL.1 hL.2 hL'.1 hL'.2 hR.1 hR.2
  have hsign : 0 ≤ (nf.eval (leftState m φ u (m.grid.next i)) (rightState m φ u i) -
      nf.eval (leftState m φ u i) (rightState m φ u i)) *
      (leftState m φ u (m.grid.next i) - leftState m φ u i) := by
    rcases le_total (leftState m φ u i) (leftState m φ u (m.grid.next i)) with h | h
    · have := hmono.1 _ _ (rightState m φ u i) h
      nlinarith
    · have := hmono.1 _ _ (rightState m φ u i) h
      nlinarith
  refine ⟨sign_transfer _ _ _ KL hsign hj.1 hlipB, ?_⟩
  have := mul_le_mul_of_nonneg_left hj.2 hKL
  linarith

/-- FVN-M, incremental form: the scalar MUSCL step is a Harten incremental update with
`0 ≤ C i ≤ (dt / w i) KR (1 + θ p i)` and `0 ≤ D i ≤ (dt / w (next i)) KL (1 + θ q i)`, where
`p i = w i / (w i + w (next i))` and `q i = w (next i) / (w i + w (next i))`. -/
theorem musclStep_incremental (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (nf : NumericalFlux)
    (hmono : MonotoneFlux nf) (KL KR : ℝ) (hlip : LipschitzOnBounds nf lo hi KL KR) (hKL : 0 ≤ KL)
    (hKR : 0 ≤ KR) (dt : ℝ) (hdt : 0 ≤ dt) :
    ∃ C D : I → ℝ,
      (∀ i, 0 ≤ C i ∧
        C i ≤ dt / m.width i * KR * (1 + θ * (m.width i / (m.width i + m.width (m.grid.next i))))) ∧
      (∀ i, 0 ≤ D i ∧ D i ≤ dt / m.width (m.grid.next i) * KL *
        (1 + θ * (m.width (m.grid.next i) / (m.width i + m.width (m.grid.next i))))) ∧
      musclStep m nf.eval φ dt u = incrementalUpdate m.grid C D u := by
  have hθ := hφ.nonneg
  have hA : ∀ i, ∃ c, 0 ≤ c ∧ c ≤ KR * (1 + θ * (m.width i / (m.width i + m.width (m.grid.next i)))) ∧
      c * (u (m.grid.next i) - u i) = -(nf.eval (leftState m φ u i) (rightState m φ u i) -
        nf.eval (leftState m φ u i) (rightState m φ u (m.grid.prev i))) := by
    intro i
    have h := flux_right_increment_bound m φ θ hφ hr lo hi u hu nf hmono KL KR hlip hKR i
    have hp : 0 ≤ m.width i / (m.width i + m.width (m.grid.next i)) :=
      div_nonneg (m.width_pos i).le (add_pos (m.width_pos i) (m.width_pos _)).le
    exact exists_ratio _ _ _ h.1 h.2 (mul_nonneg hKR (by nlinarith))
  have hB : ∀ i, ∃ c, 0 ≤ c ∧
      c ≤ KL * (1 + θ * (m.width (m.grid.next i) / (m.width i + m.width (m.grid.next i)))) ∧
      c * (u (m.grid.next i) - u i) = nf.eval (leftState m φ u (m.grid.next i)) (rightState m φ u i) -
        nf.eval (leftState m φ u i) (rightState m φ u i) := by
    intro i
    have h := flux_left_increment_bound m φ θ hφ hr lo hi u hu nf hmono KL KR hlip hKL i
    have hq : 0 ≤ m.width (m.grid.next i) / (m.width i + m.width (m.grid.next i)) :=
      div_nonneg (m.width_pos _).le (add_pos (m.width_pos i) (m.width_pos _)).le
    exact exists_ratio _ _ _ h.1 h.2 (mul_nonneg hKL (by nlinarith))
  choose cA hcA using hA
  choose cB hcB using hB
  have hdw : ∀ i, 0 ≤ dt / m.width i := fun i => div_nonneg hdt (m.width_pos i).le
  refine ⟨fun i => dt / m.width i * cA i, fun i => dt / m.width (m.grid.next i) * cB i,
    fun i => ⟨mul_nonneg (hdw i) (hcA i).1, (mul_le_mul_of_nonneg_left (hcA i).2.1 (hdw i)).trans_eq (by ring)⟩,
    fun i => ⟨mul_nonneg (hdw _) (hcB i).1, (mul_le_mul_of_nonneg_left (hcB i).2.1 (hdw _)).trans_eq (by ring)⟩,
    funext fun i => ?_⟩
  have a := (hcA i).2.2
  have b := (hcB (m.grid.prev i)).2.2
  simp only [m.grid.next_prev] at b
  simp only [musclStep, update, incrementalUpdate, smul_eq_mul, m.grid.next_prev]
  linear_combination (-(dt / m.width i)) * a + (dt / m.width i) * b

/-! ### FVN-M: one step -/

/-- On a degenerate interval `hi ≤ lo` a bounded state is constant, so the MUSCL step leaves it unchanged
(`φ 0 0 = 0` follows from `SlopeBounded θ φ`). -/
private theorem musclStep_eq_self_of_le (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (hhl : hi ≤ lo) (nf : NumericalFlux) (dt : ℝ) :
    musclStep m nf.eval φ dt u = u := by
  have hc : u = fun _ => lo := funext fun j => le_antisymm (by linarith [(hu j).2]) (hu j).1
  have h0 : φ 0 0 = 0 := by
    have h := (hφ 0 0).2.2.1
    rw [abs_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  subst hc
  exact musclStep_constant m nf.eval φ dt lo h0

/-- Coefficient sum at cell `i` for the bounds CFL condition. -/
private theorem cell_coeff_sum (w a b dt KL KR θ : ℝ) (hw : 0 < w) (ha : 0 < a) (hb : 0 < b) :
    dt / w * KR * (1 + θ * (w / a)) + dt / w * KL * (1 + θ * (w / b)) =
      dt * ((KL + KR) / w + θ * (KR / a + KL / b)) := by
  field_simp
  ring

/-- Coefficient sum at face `i` for the total-variation CFL condition. -/
private theorem face_coeff_sum (w w' dt KL KR θ : ℝ) (hw : 0 < w) (hw' : 0 < w') :
    dt / w * KR * (1 + θ * (w / (w + w'))) + dt / w' * KL * (1 + θ * (w' / (w + w'))) =
      dt * (KR / w + KL / w' + θ * (KL + KR) / (w + w')) := by
  have hs : 0 < w + w' := add_pos hw hw'
  field_simp
  ring

/-- FVN-M (a): under the cell CFL condition one scalar MUSCL step keeps the bounds `[lo, hi]`. -/
theorem musclStep_mem (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hr : m.MeshRatio θ)
    (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (nf : NumericalFlux) (hmono : MonotoneFlux nf)
    (KL KR : ℝ) (hlip : LipschitzOnBounds nf lo hi KL KR) (dt : ℝ) (hdt : 0 ≤ dt)
    (hcfl : ∀ i, dt * ((KL + KR) / m.width i + θ * (KR / (m.width i + m.width (m.grid.next i)) +
      KL / (m.width (m.grid.prev i) + m.width i))) ≤ 1) :
    musclStep m nf.eval φ dt u ∈ boundedStates lo hi := by
  rcases lt_or_ge lo hi with hlh | hhl
  · obtain ⟨hKL, hKR⟩ := hlip.nonneg hlh
    obtain ⟨C, D, hC, hD, e⟩ := musclStep_incremental m φ θ hφ hr lo hi u hu nf hmono KL KR hlip hKL hKR dt hdt
    rw [e]
    intro i
    have hD' := (hD (m.grid.prev i)).2
    simp only [m.grid.next_prev] at hD'
    have hsum := cell_coeff_sum (m.width i) (m.width i + m.width (m.grid.next i))
      (m.width (m.grid.prev i) + m.width i) dt KL KR θ (m.width_pos i)
      (add_pos (m.width_pos i) (m.width_pos _)) (add_pos (m.width_pos _) (m.width_pos i))
    exact incrementalUpdate_bounds m.grid C D u lo hi i (hC i).1 (hD _).1
      (by linarith [(hC i).2, hcfl i]) (fun j => (hu j).1) (fun j => (hu j).2)
  · rw [musclStep_eq_self_of_le m φ θ hφ lo hi u hu hhl nf dt]
    exact hu

/-- FVN-M (b): under the face CFL condition one scalar MUSCL step does not increase the total variation. -/
theorem musclStep_totalVariation_le [Fintype I] (m : Mesh1D I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ)
    (hr : m.MeshRatio θ) (lo hi : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates lo hi) (nf : NumericalFlux)
    (hmono : MonotoneFlux nf) (KL KR : ℝ) (hlip : LipschitzOnBounds nf lo hi KL KR) (dt : ℝ) (hdt : 0 ≤ dt)
    (hcfl : ∀ i, dt * (KR / m.width i + KL / m.width (m.grid.next i) +
      θ * (KL + KR) / (m.width i + m.width (m.grid.next i))) ≤ 1) :
    totalVariation m.grid (musclStep m nf.eval φ dt u) ≤ totalVariation m.grid u := by
  rcases lt_or_ge lo hi with hlh | hhl
  · obtain ⟨hKL, hKR⟩ := hlip.nonneg hlh
    obtain ⟨C, D, hC, hD, e⟩ := musclStep_incremental m φ θ hφ hr lo hi u hu nf hmono KL KR hlip hKL hKR dt hdt
    rw [e]
    refine incrementalUpdate_totalVariation_le m.grid C D u (fun i => (hC i).1) (fun i => (hD i).1) fun i => ?_
    have hsum := face_coeff_sum (m.width i) (m.width (m.grid.next i)) dt KL KR θ (m.width_pos i)
      (m.width_pos _)
    linarith [(hC i).2, (hD i).2, hcfl i]
  · rw [musclStep_eq_self_of_le m φ θ hφ lo hi u hu hhl nf dt]

end CFDLean.FV1D.Nonuniform
