import CFDLean.Discrete.Periodic.Muscl

/-! Burgers B3b-U, B3b-C, B3b-L, B3b-I, B3b-T: MUSCL reconstruction that is unlimited by default, with a limiter as a
factor on top. The unlimited slope is the central difference `(a + b)/2` of the backward difference `a` and the
forward difference `b`; a limiter factor `ψ(a, b)` multiplies it. The certificate `SlopeBounded θ` (Sweby region)
generalizes the minmod region of B3 (`θ = 1`). The limiters minmod, MC, superbee, van Leer and van Albada are given as
factors, with their classical slope forms, ranges and certificates. For a `θ`-bounded slope with `θ ≤ 2` the
Forward-Euler MUSCL step is in Harten's incremental form with coefficients bounded by `(dt/dx)(1 + θ/2) K`. -/
noncomputable section
namespace CFDLean.Scalar.FiniteVolume

open Periodic

variable {I : Type*}

/-! ### Unlimited slope, limiter factors, certificate -/

/-- Unlimited slope: the central difference `(a + b) / 2` of the backward difference `a` and the forward
difference `b`. -/
def centralSlope (a b : ℝ) : ℝ := (a + b) / 2

/-- A limiter factor on top of the unlimited slope. -/
def limitedSlope (ψ : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ := ψ a b * centralSlope a b

/-- No limiter: factor one. -/
def noLimiter : ℝ → ℝ → ℝ := fun _ _ => 1

/-- Limiter certificate with constant `θ` (Sweby region): the slope has the sign of both differences and is at most
`θ` times either. `θ = 1` is `MinmodBounded`. -/
def SlopeBounded (θ : ℝ) (φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b, 0 ≤ φ a b * a ∧ 0 ≤ φ a b * b ∧ |φ a b| ≤ θ * |a| ∧ |φ a b| ≤ θ * |b|

def minmodFactor (a b : ℝ) : ℝ := if 0 < a * b then 2 * min |a| |b| / (|a| + |b|) else 0

def mcFactor (a b : ℝ) : ℝ := if 0 < a * b then min 1 (4 * min |a| |b| / (|a| + |b|)) else 0

def superbeeFactor (a b : ℝ) : ℝ :=
  if 0 < a * b then 2 * max (min (2 * |a|) |b|) (min |a| (2 * |b|)) / (|a| + |b|) else 0

def vanLeerFactor (a b : ℝ) : ℝ := if 0 < a * b then 4 * (a * b) / (a + b) ^ 2 else 0

def vanAlbadaFactor (a b : ℝ) : ℝ := if 0 < a * b then 2 * (a * b) / (a ^ 2 + b ^ 2) else 0

theorem limitedSlope_noLimiter : limitedSlope noLimiter = centralSlope := by
  funext a b
  simp [limitedSlope, noLimiter]

theorem minmodBounded_iff_slopeBounded_one (φ : ℝ → ℝ → ℝ) : MinmodBounded φ ↔ SlopeBounded 1 φ := by
  simp only [MinmodBounded, SlopeBounded, one_mul]

theorem SlopeBounded.mono {θ θ' : ℝ} {φ : ℝ → ℝ → ℝ} (h : SlopeBounded θ φ) (hθ : θ ≤ θ') :
    SlopeBounded θ' φ := by
  intro a b
  obtain ⟨h1, h2, h3, h4⟩ := h a b
  exact ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_right hθ (abs_nonneg a)),
    h4.trans (mul_le_mul_of_nonneg_right hθ (abs_nonneg b))⟩

/-- The certificate constant is automatically nonnegative. -/
theorem SlopeBounded.nonneg {θ : ℝ} {φ : ℝ → ℝ → ℝ} (h : SlopeBounded θ φ) : 0 ≤ θ := by
  have h1 := (h 1 1).2.2.1
  rw [abs_one, mul_one] at h1
  exact (abs_nonneg _).trans h1

/-- The unlimited slope satisfies no certificate (`a = 1`, `b = 0`). -/
theorem not_slopeBounded_centralSlope (θ : ℝ) : ¬ SlopeBounded θ centralSlope := by
  intro h
  have h1 := (h 1 0).2.2.2
  norm_num [centralSlope] at h1

/-! ### Same strict sign -/

theorem add_eq_sign_mul_of_mul_pos {a b : ℝ} (h : 0 < a * b) :
    a + b = (if 0 < a then 1 else -1) * (|a| + |b|) := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ite_eq_left ha, abs_of_pos ha, abs_of_pos hb, one_mul]
  · rw [ite_eq_right (not_lt.mpr ha.le), abs_of_neg ha, abs_of_neg hb]
    ring

theorem abs_add_of_mul_pos {a b : ℝ} (h : 0 < a * b) : |a + b| = |a| + |b| := by
  rw [add_eq_sign_mul_of_mul_pos h, abs_mul, abs_of_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b))]
  split_ifs <;> simp

theorem abs_pos_both_of_mul_pos {a b : ℝ} (h : 0 < a * b) : 0 < |a| ∧ 0 < |b| :=
  ⟨abs_pos.mpr (left_ne_zero_of_mul h.ne'), abs_pos.mpr (right_ne_zero_of_mul h.ne')⟩

theorem mul_eq_abs_mul_abs_of_mul_pos {a b : ℝ} (h : 0 < a * b) : a * b = |a| * |b| := by
  rw [← abs_mul, abs_of_pos h]

/-- In the same-sign case a limited slope is the sign times `ψ · (|a| + |b|) / 2`. -/
theorem limitedSlope_eq_sign_mul (ψ : ℝ → ℝ → ℝ) {a b : ℝ} (h : 0 < a * b) :
    limitedSlope ψ a b = (if 0 < a then 1 else -1) * (ψ a b * ((|a| + |b|) / 2)) := by
  rw [limitedSlope, centralSlope, add_eq_sign_mul_of_mul_pos h]
  ring

/-! ### Classical forms -/

theorem minmodFactor_mul {a b : ℝ} (h : 0 < a * b) : minmodFactor a b * ((|a| + |b|) / 2) = min |a| |b| := by
  obtain ⟨ha, hb⟩ := abs_pos_both_of_mul_pos h
  rw [minmodFactor, ite_eq_left h]
  field_simp

theorem mcFactor_mul {a b : ℝ} (h : 0 < a * b) :
    mcFactor a b * ((|a| + |b|) / 2) = min ((|a| + |b|) / 2) (min (2 * |a|) (2 * |b|)) := by
  obtain ⟨ha, hb⟩ := abs_pos_both_of_mul_pos h
  rw [mcFactor, ite_eq_left h, min_mul_of_nonneg _ _ (by positivity), one_mul, ← mul_min_of_nonneg _ _ zero_le_two]
  congr 1
  field_simp
  ring

theorem superbeeFactor_mul {a b : ℝ} (h : 0 < a * b) :
    superbeeFactor a b * ((|a| + |b|) / 2) = max (min (2 * |a|) |b|) (min |a| (2 * |b|)) := by
  obtain ⟨ha, hb⟩ := abs_pos_both_of_mul_pos h
  rw [superbeeFactor, ite_eq_left h]
  field_simp

/-- The minmod factor gives the minmod slope. -/
theorem limitedSlope_minmodFactor : limitedSlope minmodFactor = minmod := by
  funext a b
  by_cases h : 0 < a * b
  · rw [limitedSlope_eq_sign_mul _ h, minmodFactor_mul h]
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ite_eq_left ha, abs_of_pos ha, abs_of_pos hb, one_mul, minmod, ite_eq_left ⟨ha, hb⟩]
    · rw [ite_eq_right (not_lt.mpr ha.le), abs_of_neg ha, abs_of_neg hb, minmod,
        ite_eq_right (fun h' => (not_lt.mpr ha.le) h'.1), ite_eq_left ⟨ha, hb⟩, min_neg_neg]
      ring
  · rw [limitedSlope, minmodFactor, ite_eq_right h, zero_mul, minmod, ite_eq_right (fun h' => h (mul_pos h'.1 h'.2)),
      ite_eq_right (fun h' => h (mul_pos_of_neg_of_neg h'.1 h'.2))]

/-- MC: the minmod of `(a + b)/2`, `2a`, `2b`. -/
theorem limitedSlope_mcFactor (a b : ℝ) : limitedSlope mcFactor a b =
    if 0 < a * b then (if 0 < a then 1 else -1) * min (|a + b| / 2) (min (2 * |a|) (2 * |b|)) else 0 := by
  by_cases h : 0 < a * b
  · rw [ite_eq_left h, limitedSlope_eq_sign_mul _ h, mcFactor_mul h, abs_add_of_mul_pos h]
  · rw [ite_eq_right h, limitedSlope, mcFactor, ite_eq_right h, zero_mul]

theorem limitedSlope_superbeeFactor (a b : ℝ) : limitedSlope superbeeFactor a b =
    if 0 < a * b then (if 0 < a then 1 else -1) * max (min (2 * |a|) |b|) (min |a| (2 * |b|)) else 0 := by
  by_cases h : 0 < a * b
  · rw [ite_eq_left h, limitedSlope_eq_sign_mul _ h, superbeeFactor_mul h]
  · rw [ite_eq_right h, limitedSlope, superbeeFactor, ite_eq_right h, zero_mul]

/-- van Leer: the harmonic mean of `a` and `b`. -/
theorem limitedSlope_vanLeerFactor (a b : ℝ) : limitedSlope vanLeerFactor a b =
    if 0 < a * b then 2 * (a * b) / (a + b) else 0 := by
  split_ifs with h
  · have hab : a + b ≠ 0 := by
      rw [add_eq_sign_mul_of_mul_pos h]
      have := abs_pos_both_of_mul_pos h
      split_ifs <;> intro h' <;> linarith
    rw [limitedSlope, vanLeerFactor, ite_eq_left h, centralSlope]
    field_simp
    ring
  · rw [limitedSlope, vanLeerFactor, ite_eq_right h, zero_mul]

theorem limitedSlope_vanAlbadaFactor (a b : ℝ) : limitedSlope vanAlbadaFactor a b =
    if 0 < a * b then a * b * (a + b) / (a ^ 2 + b ^ 2) else 0 := by
  split_ifs with h
  · have hab : a ^ 2 + b ^ 2 ≠ 0 := by
      have : a ≠ 0 := left_ne_zero_of_mul h.ne'
      positivity
    rw [limitedSlope, vanAlbadaFactor, ite_eq_left h, centralSlope]
    field_simp
  · rw [limitedSlope, vanAlbadaFactor, ite_eq_right h, zero_mul]

/-! ### Factor ranges and symmetry -/

theorem minmodFactor_mem (a b : ℝ) : 0 ≤ minmodFactor a b ∧ minmodFactor a b ≤ 1 := by
  unfold minmodFactor
  split_ifs with h
  · obtain ⟨ha, hb⟩ := abs_pos_both_of_mul_pos h
    rw [div_le_one (by positivity)]
    exact ⟨by positivity, by linarith [min_le_left |a| |b|, min_le_right |a| |b|]⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem mcFactor_mem (a b : ℝ) : 0 ≤ mcFactor a b ∧ mcFactor a b ≤ 1 := by
  unfold mcFactor
  split_ifs
  · exact ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- Superbee may enlarge the unlimited slope, by at most `4/3` (sharp: `|b| = 2 |a|`). -/
theorem superbeeFactor_mem (a b : ℝ) : 0 ≤ superbeeFactor a b ∧ superbeeFactor a b ≤ 4 / 3 := by
  unfold superbeeFactor
  split_ifs with h
  · obtain ⟨ha, hb⟩ := abs_pos_both_of_mul_pos h
    rw [div_le_iff₀ (by positivity)]
    refine ⟨by positivity, ?_⟩
    have h1 := min_le_left (2 * |a|) |b|
    have h2 := min_le_right (2 * |a|) |b|
    have h3 := min_le_left |a| (2 * |b|)
    have h4 := min_le_right |a| (2 * |b|)
    have := max_le (a := min (2 * |a|) |b|) (b := min |a| (2 * |b|)) (c := 2 / 3 * (|a| + |b|))
      (by linarith) (by linarith)
    linarith
  · exact ⟨le_rfl, by norm_num⟩

theorem vanLeerFactor_mem (a b : ℝ) : 0 ≤ vanLeerFactor a b ∧ vanLeerFactor a b ≤ 1 := by
  unfold vanLeerFactor
  split_ifs with h
  · have hab : 0 < (a + b) ^ 2 := by
      have : a + b ≠ 0 := by
        rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> intro h' <;> linarith
      positivity
    rw [div_le_one hab]
    exact ⟨div_nonneg (by linarith) hab.le, by nlinarith [sq_nonneg (a - b)]⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem vanAlbadaFactor_mem (a b : ℝ) : 0 ≤ vanAlbadaFactor a b ∧ vanAlbadaFactor a b ≤ 1 := by
  unfold vanAlbadaFactor
  split_ifs with h
  · have hab : 0 < a ^ 2 + b ^ 2 := by
      have : a ≠ 0 := left_ne_zero_of_mul h.ne'
      positivity
    rw [div_le_one hab]
    exact ⟨div_nonneg (by linarith) hab.le, by nlinarith [sq_nonneg (a - b)]⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem minmodFactor_comm (a b : ℝ) : minmodFactor a b = minmodFactor b a := by
  simp only [minmodFactor, mul_comm b a, min_comm |b| |a|, add_comm |b| |a|]

theorem mcFactor_comm (a b : ℝ) : mcFactor a b = mcFactor b a := by
  simp only [mcFactor, mul_comm b a, min_comm |b| |a|, add_comm |b| |a|]

theorem superbeeFactor_comm (a b : ℝ) : superbeeFactor a b = superbeeFactor b a := by
  simp only [superbeeFactor, mul_comm b a, min_comm (2 * |b|) |a|, min_comm |b| (2 * |a|), add_comm |b| |a|,
    max_comm (min |a| (2 * |b|))]

theorem vanLeerFactor_comm (a b : ℝ) : vanLeerFactor a b = vanLeerFactor b a := by
  simp only [vanLeerFactor, mul_comm b a, add_comm b a]

theorem vanAlbadaFactor_comm (a b : ℝ) : vanAlbadaFactor a b = vanAlbadaFactor b a := by
  simp only [vanAlbadaFactor, mul_comm b a, add_comm (b ^ 2) (a ^ 2)]

/-! ### Certificates -/

/-- A symmetric nonnegative factor, zero unless `a` and `b` have the same strict sign, with
`ψ · (|a| + |b|)/2 ≤ θ |a|`, gives a limited slope in the region `θ`. -/
theorem slopeBounded_limitedSlope {θ : ℝ} {ψ : ℝ → ℝ → ℝ} (hθ : 0 ≤ θ) (hsymm : ∀ a b, ψ a b = ψ b a)
    (h0 : ∀ a b, ¬ 0 < a * b → ψ a b = 0)
    (hψ : ∀ a b, 0 < a * b → 0 ≤ ψ a b ∧ ψ a b * ((|a| + |b|) / 2) ≤ θ * |a|) :
    SlopeBounded θ (limitedSlope ψ) := by
  intro a b
  by_cases h : 0 < a * b
  · obtain ⟨hp, ha⟩ := hψ a b h
    have hb : ψ a b * ((|a| + |b|) / 2) ≤ θ * |b| := by
      rw [hsymm, add_comm]
      exact (hψ b a (by rwa [mul_comm])).2
    have habs : |limitedSlope ψ a b| = ψ a b * ((|a| + |b|) / 2) := by
      rw [limitedSlope, centralSlope, abs_mul, abs_of_nonneg hp, abs_div, abs_add_of_mul_pos h, abs_two]
    have e : limitedSlope ψ a b = ψ a b * (a + b) / 2 := by
      rw [limitedSlope, centralSlope]
      ring
    have s1 := mul_nonneg hp (by nlinarith [sq_nonneg a] : 0 ≤ (a + b) * a)
    have s2 := mul_nonneg hp (by nlinarith [sq_nonneg b] : 0 ≤ (a + b) * b)
    refine ⟨?_, ?_, habs ▸ ha, habs ▸ hb⟩ <;> rw [e] <;> linarith
  · simp only [limitedSlope, h0 a b h, zero_mul, abs_zero]
    exact ⟨le_rfl, le_rfl, mul_nonneg hθ (abs_nonneg a), mul_nonneg hθ (abs_nonneg b)⟩

theorem slopeBounded_minmodFactor : SlopeBounded 1 (limitedSlope minmodFactor) := by
  rw [limitedSlope_minmodFactor, ← minmodBounded_iff_slopeBounded_one]
  exact minmod_minmodBounded

theorem slopeBounded_mcFactor : SlopeBounded 2 (limitedSlope mcFactor) :=
  slopeBounded_limitedSlope zero_le_two mcFactor_comm (fun _ _ h => ite_eq_right h) fun _ _ h =>
    ⟨(mcFactor_mem _ _).1, by rw [mcFactor_mul h]; exact (min_le_right _ _).trans (min_le_left _ _)⟩

theorem slopeBounded_superbeeFactor : SlopeBounded 2 (limitedSlope superbeeFactor) :=
  slopeBounded_limitedSlope zero_le_two superbeeFactor_comm (fun _ _ h => ite_eq_right h) fun a b h =>
    ⟨(superbeeFactor_mem _ _).1, by
      rw [superbeeFactor_mul h]
      exact max_le (min_le_left _ _) ((min_le_left _ _).trans (by linarith [abs_nonneg a]))⟩

theorem slopeBounded_vanLeerFactor : SlopeBounded 2 (limitedSlope vanLeerFactor) :=
  slopeBounded_limitedSlope zero_le_two vanLeerFactor_comm (fun _ _ h => ite_eq_right h) fun a b h => by
    refine ⟨(vanLeerFactor_mem _ _).1, ?_⟩
    obtain ⟨ha, hb⟩ := abs_pos_both_of_mul_pos h
    rw [vanLeerFactor, ite_eq_left h, mul_eq_abs_mul_abs_of_mul_pos h, ← sq_abs (a + b), abs_add_of_mul_pos h,
      div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos (mul_pos ha ha) (add_pos ha hb)]

/-- van Albada: `(r² + r)/(r² + 1) ≤ 5/4`, since `5x² - 4xy + y² = (2x - y)² + x²`. -/
theorem slopeBounded_vanAlbadaFactor : SlopeBounded (5 / 4) (limitedSlope vanAlbadaFactor) :=
  slopeBounded_limitedSlope (by norm_num) vanAlbadaFactor_comm (fun _ _ h => ite_eq_right h) fun a b h => by
    refine ⟨(vanAlbadaFactor_mem _ _).1, ?_⟩
    obtain ⟨ha, hb⟩ := abs_pos_both_of_mul_pos h
    rw [vanAlbadaFactor, ite_eq_left h, mul_eq_abs_mul_abs_of_mul_pos h, ← sq_abs a, ← sq_abs b,
      div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg ha.le (sq_nonneg (2 * |a| - |b|)), pow_pos ha 3]

/-! ### Reconstructed states -/

/-- A half slope with the sign of both neighbouring differences, at most twice either, keeps the bounds. -/
theorem half_slope_mem_two (m M v vl vr s : ℝ) (h1 : 0 ≤ s * (v - vl)) (h2 : 0 ≤ s * (vr - v))
    (h3 : |s| ≤ 2 * |v - vl|) (h4 : |s| ≤ 2 * |vr - v|) (hv : m ≤ v ∧ v ≤ M) (hvl : m ≤ vl ∧ vl ≤ M)
    (hvr : m ≤ vr ∧ vr ≤ M) : (m ≤ v + s / 2 ∧ v + s / 2 ≤ M) ∧ (m ≤ v - s / 2 ∧ v - s / 2 ≤ M) := by
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

/-- B3b: with a limiter in the region `θ ≤ 2` the reconstructed left state stays in the bounds. -/
theorem leftState_mem_bounded (g : Grid I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (m M : ℝ)
    (u : I → ℝ) (hu : u ∈ boundedStates m M) (i : I) : m ≤ leftState g φ u i ∧ leftState g φ u i ≤ M := by
  have h := hφ.mono hθ2 (u i - u (g.prev i)) (u (g.next i) - u i)
  exact (half_slope_mem_two m M _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2 (hu i) (hu _) (hu _)).1

/-- B3b: with a limiter in the region `θ ≤ 2` the reconstructed right state stays in the bounds. -/
theorem rightState_mem_bounded (g : Grid I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2)
    (m M : ℝ) (u : I → ℝ) (hu : u ∈ boundedStates m M) (i : I) :
    m ≤ rightState g φ u i ∧ rightState g φ u i ≤ M := by
  have h := hφ.mono hθ2 (u (g.next i) - u (g.prev (g.next i))) (u (g.next (g.next i)) - u (g.next i))
  exact (half_slope_mem_two m M _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2 (hu _) (hu _) (hu _)).2

/-! ### Incremental form -/

/-- `d + s₁/2 - s₂/2` with two slopes of the sign of `d`, at most `θ |d|`, `θ ≤ 2`: same sign as `d`, at most
`(1 + θ/2) |d|`. -/
theorem slope_combo_bounded (θ d s1 s2 : ℝ) (hθ2 : θ ≤ 2) (h1 : 0 ≤ s1 * d) (h1' : |s1| ≤ θ * |d|)
    (h2 : 0 ≤ s2 * d) (h2' : |s2| ≤ θ * |d|) :
    0 ≤ (d + s1 / 2 - s2 / 2) * d ∧ |d + s1 / 2 - s2 / 2| ≤ (1 + θ / 2) * |d| := by
  rcases lt_trichotomy d 0 with hd | hd | hd
  · have e1 : s1 ≤ 0 := by nlinarith
    have e2 : s2 ≤ 0 := by nlinarith
    rw [abs_of_neg hd, abs_of_nonpos e1] at h1'
    rw [abs_of_neg hd, abs_of_nonpos e2] at h2'
    have hθd := mul_nonneg (sub_nonneg.mpr hθ2) (neg_nonneg.mpr hd.le)
    rw [abs_of_neg hd, abs_le]
    have h : d + s1 / 2 - s2 / 2 ≤ 0 := by linarith
    exact ⟨by nlinarith, by linarith, by linarith⟩
  · subst hd
    simp only [abs_zero, mul_zero, abs_nonpos_iff] at h1' h2'
    simp [h1', h2']
  · have e1 : 0 ≤ s1 := by nlinarith
    have e2 : 0 ≤ s2 := by nlinarith
    rw [abs_of_pos hd, abs_of_nonneg e1] at h1'
    rw [abs_of_pos hd, abs_of_nonneg e2] at h2'
    have hθd := mul_nonneg (sub_nonneg.mpr hθ2) hd.le
    rw [abs_of_pos hd, abs_le]
    have h : 0 ≤ d + s1 / 2 - s2 / 2 := by linarith
    exact ⟨by nlinarith, by linarith, by linarith⟩

/-- B3b: the jump of the right states across a cell has the sign of `Δ_i` and is at most `(1 + θ/2) |Δ_i|`. -/
theorem rightState_sub_bounded (g : Grid I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2)
    (u : I → ℝ) (i : I) :
    0 ≤ (rightState g φ u i - rightState g φ u (g.prev i)) * (u (g.next i) - u i) ∧
      |rightState g φ u i - rightState g φ u (g.prev i)| ≤ (1 + θ / 2) * |u (g.next i) - u i| := by
  have e : rightState g φ u i - rightState g φ u (g.prev i) = (u (g.next i) - u i) +
      φ (u i - u (g.prev i)) (u (g.next i) - u i) / 2 -
      φ (u (g.next i) - u i) (u (g.next (g.next i)) - u (g.next i)) / 2 := by
    simp only [rightState, slope, g.next_prev, g.prev_next]
    ring
  have h1 := hφ (u i - u (g.prev i)) (u (g.next i) - u i)
  have h2 := hφ (u (g.next i) - u i) (u (g.next (g.next i)) - u (g.next i))
  rw [e]
  exact slope_combo_bounded θ _ _ _ hθ2 h1.2.1 h1.2.2.2 h2.1 h2.2.2.1

/-- B3b: the jump of the left states across an interface has the sign of `Δ_{i-1}` and is at most
`(1 + θ/2) |Δ_{i-1}|`. -/
theorem leftState_sub_bounded (g : Grid I) (φ : ℝ → ℝ → ℝ) (θ : ℝ) (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2)
    (u : I → ℝ) (i : I) :
    0 ≤ (leftState g φ u i - leftState g φ u (g.prev i)) * (u i - u (g.prev i)) ∧
      |leftState g φ u i - leftState g φ u (g.prev i)| ≤ (1 + θ / 2) * |u i - u (g.prev i)| := by
  have e : leftState g φ u i - leftState g φ u (g.prev i) = (u i - u (g.prev i)) +
      φ (u i - u (g.prev i)) (u (g.next i) - u i) / 2 -
      φ (u (g.prev i) - u (g.prev (g.prev i))) (u i - u (g.prev i)) / 2 := by
    simp only [leftState, slope, g.next_prev]
    ring
  have h1 := hφ (u i - u (g.prev i)) (u (g.next i) - u i)
  have h2 := hφ (u (g.prev i) - u (g.prev (g.prev i))) (u i - u (g.prev i))
  rw [e]
  exact slope_combo_bounded θ _ _ _ hθ2 h1.1 h1.2.2.1 h2.2.1 h2.2.2.2

/-- B3b: the flux increment in the right state has the sign of `Δ_i` and is at most `(1 + θ/2) KR |Δ_i|`. -/
theorem flux_right_increment_bounded (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (hmono : MonotoneFlux nf) (m M KL KR : ℝ)
    (hlip : LipschitzOnBounds nf m M KL KR) (hKR : 0 ≤ KR) (u : I → ℝ) (hu : u ∈ boundedStates m M) (i : I) :
    0 ≤ -(nf.eval (leftState g φ u i) (rightState g φ u i) -
        nf.eval (leftState g φ u i) (rightState g φ u (g.prev i))) * (u (g.next i) - u i) ∧
      |-(nf.eval (leftState g φ u i) (rightState g φ u i) -
        nf.eval (leftState g φ u i) (rightState g φ u (g.prev i)))| ≤
        (1 + θ / 2) * KR * |u (g.next i) - u i| := by
  have hr := rightState_sub_bounded g φ θ hφ hθ2 u i
  have hL := leftState_mem_bounded g φ θ hφ hθ2 m M u hu i
  have hR := rightState_mem_bounded g φ θ hφ hθ2 m M u hu i
  have hR' := rightState_mem_bounded g φ θ hφ hθ2 m M u hu (g.prev i)
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

/-- B3b: the flux increment in the left state has the sign of `Δ_{i-1}` and is at most
`(1 + θ/2) KL |Δ_{i-1}|`. -/
theorem flux_left_increment_bounded (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (hmono : MonotoneFlux nf) (m M KL KR : ℝ)
    (hlip : LipschitzOnBounds nf m M KL KR) (hKL : 0 ≤ KL) (u : I → ℝ) (hu : u ∈ boundedStates m M) (i : I) :
    0 ≤ (nf.eval (leftState g φ u i) (rightState g φ u (g.prev i)) -
        nf.eval (leftState g φ u (g.prev i)) (rightState g φ u (g.prev i))) * (u i - u (g.prev i)) ∧
      |nf.eval (leftState g φ u i) (rightState g φ u (g.prev i)) -
        nf.eval (leftState g φ u (g.prev i)) (rightState g φ u (g.prev i))| ≤
        (1 + θ / 2) * KL * |u i - u (g.prev i)| := by
  have hl := leftState_sub_bounded g φ θ hφ hθ2 u i
  have hL := leftState_mem_bounded g φ θ hφ hθ2 m M u hu i
  have hL' := leftState_mem_bounded g φ θ hφ hθ2 m M u hu (g.prev i)
  have hR' := rightState_mem_bounded g φ θ hφ hθ2 m M u hu (g.prev i)
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

/-- B3b: with a limiter in the region `θ ≤ 2` the MUSCL Forward-Euler step is in incremental form with nonnegative
coefficients bounded by `dt/dx · (1 + θ/2) · KR` and `dt/dx · (1 + θ/2) · KL`. -/
theorem muscl_incremental_bounded (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2)
    (hmono : MonotoneFlux nf) (m M KL KR : ℝ) (hlip : LipschitzOnBounds nf m M KL KR) (hKL : 0 ≤ KL)
    (hKR : 0 ≤ KR) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    ∃ C D : I → ℝ,
      (∀ i, 0 ≤ C i ∧ C i ≤ dt / dx * ((1 + θ / 2) * KR)) ∧
      (∀ i, 0 ≤ D i ∧ D i ≤ dt / dx * ((1 + θ / 2) * KL)) ∧
      Time.ForwardEuler.step dt (musclRhs g dx nf φ) u = incrementalUpdate g C D u := by
  have hθ : 0 ≤ 1 + θ / 2 := by linarith [hφ.nonneg]
  have hA : ∀ i, ∃ q, 0 ≤ q ∧ q ≤ (1 + θ / 2) * KR ∧ q * (u (g.next i) - u i) =
      -(nf.eval (leftState g φ u i) (rightState g φ u i) -
        nf.eval (leftState g φ u i) (rightState g φ u (g.prev i))) := by
    intro i
    have h := flux_right_increment_bounded g nf φ θ hφ hθ2 hmono m M KL KR hlip hKR u hu i
    exact exists_ratio _ _ _ h.1 h.2 (mul_nonneg hθ hKR)
  have hB : ∀ j, ∃ q, 0 ≤ q ∧ q ≤ (1 + θ / 2) * KL ∧ q * (u (g.next j) - u j) =
      nf.eval (leftState g φ u (g.next j)) (rightState g φ u j) -
        nf.eval (leftState g φ u j) (rightState g φ u j) := by
    intro j
    have h := flux_left_increment_bounded g nf φ θ hφ hθ2 hmono m M KL KR hlip hKL u hu (g.next j)
    simp only [g.prev_next] at h
    exact exists_ratio _ _ _ h.1 h.2 (mul_nonneg hθ hKL)
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

/-! ### One Forward-Euler MUSCL step -/

theorem coeff_sum_le_one_bounded (θ dx dt KL KR c d : ℝ) (hdx : 0 < dx)
    (hcfl : dt * ((1 + θ / 2) * (KL + KR)) ≤ dx) (hc : c ≤ dt / dx * ((1 + θ / 2) * KR))
    (hd : d ≤ dt / dx * ((1 + θ / 2) * KL)) : c + d ≤ 1 := by
  have e : dt / dx * ((1 + θ / 2) * KR) + dt / dx * ((1 + θ / 2) * KL) = dt * ((1 + θ / 2) * (KL + KR)) / dx := by
    ring
  have h : dt * ((1 + θ / 2) * (KL + KR)) / dx ≤ 1 := by rw [div_le_one hdx]; exact hcfl
  linarith

/-- B3b: with a limiter in the region `θ ≤ 2` and `dt · (1 + θ/2) · (KL + KR) ≤ dx` one Forward-Euler MUSCL step
does not increase the total variation. -/
theorem muscl_step_totalVariation_le_bounded [Fintype I] (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ)
    (θ : ℝ) (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (hmono : MonotoneFlux nf) (m M KL KR : ℝ)
    (hlip : LipschitzOnBounds nf m M KL KR) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : dt * ((1 + θ / 2) * (KL + KR)) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    totalVariation g (Time.ForwardEuler.step dt (musclRhs g dx nf φ) u) ≤ totalVariation g u := by
  rcases lt_or_ge m M with hmM | hMm
  · obtain ⟨hKL, hKR⟩ := hlip.nonneg hmM
    obtain ⟨C, D, hC, hD, e⟩ :=
      muscl_incremental_bounded g nf φ θ hφ hθ2 hmono m M KL KR hlip hKL hKR dx dt hdx hdt u hu
    rw [e]
    exact incrementalUpdate_totalVariation_le g C D u (fun i => (hC i).1) (fun i => (hD i).1)
      (fun i => coeff_sum_le_one_bounded θ dx dt KL KR _ _ hdx hcfl (hC i).2 (hD i).2)
  · rw [muscl_step_eq_self_of_le g dx nf φ dt m M u hu hMm]

/-- B3b: with a limiter in the region `θ ≤ 2` and `dt · (1 + θ/2) · (KL + KR) ≤ dx` one Forward-Euler MUSCL step
keeps the bounds. -/
theorem muscl_step_mem_bounded (g : Grid I) (nf : NumericalFlux) (φ : ℝ → ℝ → ℝ) (θ : ℝ)
    (hφ : SlopeBounded θ φ) (hθ2 : θ ≤ 2) (hmono : MonotoneFlux nf) (m M KL KR : ℝ)
    (hlip : LipschitzOnBounds nf m M KL KR) (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt)
    (hcfl : dt * ((1 + θ / 2) * (KL + KR)) ≤ dx) (u : I → ℝ) (hu : u ∈ boundedStates m M) :
    Time.ForwardEuler.step dt (musclRhs g dx nf φ) u ∈ boundedStates m M := by
  rcases lt_or_ge m M with hmM | hMm
  · obtain ⟨hKL, hKR⟩ := hlip.nonneg hmM
    obtain ⟨C, D, hC, hD, e⟩ :=
      muscl_incremental_bounded g nf φ θ hφ hθ2 hmono m M KL KR hlip hKL hKR dx dt hdx hdt u hu
    rw [e]
    intro i
    exact incrementalUpdate_bounds g C D u m M i (hC i).1 (hD _).1
      (coeff_sum_le_one_bounded θ dx dt KL KR _ _ hdx hcfl (hC i).2 (hD _).2) (fun j => (hu j).1)
      (fun j => (hu j).2)
  · rw [muscl_step_eq_self_of_le g dx nf φ dt m M u hu hMm]
    exact hu

end CFDLean.Scalar.FiniteVolume
