import CFDLean.Papers.JST1.Spec.Item15
import CFDLean.Papers.JST1.Proofs.Item1

/-! Proofs of item 15 (P4): `prop:wallJST`. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open CFDLean.Num Filter Topology Asymptotics Set
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Wall15

/-! ### Taylor's theorem with a moving base point -/

theorem taylor2_eval (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) {x0 x : ℝ} (hx : x0 ≠ x) :
    taylorWithinEval f 2 (uIcc x0 x) x0 x =
      f x0 + deriv f x0 * (x - x0) + deriv (deriv f) x0 * (x - x0) ^ 2 / 2 := by
  rw [taylor_within_apply]
  have hu := uniqueDiffOn_uIcc hx
  have hm : x0 ∈ uIcc x0 x := left_mem_uIcc
  have e : ∀ k : ℕ, k ≤ 3 → iteratedDerivWithin k f (uIcc x0 x) x0 = iteratedDeriv k f x0 := fun k hk =>
    iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by exact_mod_cast hk)) hm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
  have h2 : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  simp only [iteratedDeriv_zero, iteratedDeriv_one, h2, smul_eq_mul, Nat.factorial]
  push_cast
  ring

theorem taylor2_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x0 x, x0 ∈ Icc (-R) R → x ∈ Icc (-R) R →
      |f x - (f x0 + deriv f x0 * (x - x0) + deriv (deriv f) x0 * (x - x0) ^ 2 / 2)| ≤ C * |x - x0| ^ 3 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    (hf.continuous_iteratedDeriv 3 le_rfl).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x0 x h0 h1 => ?_⟩
  rcases eq_or_ne x0 x with rfl | hx
  · simp
  obtain ⟨x', hx', he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hx
    (hf.contDiffOn.of_le (by norm_num))
  rw [taylor2_eval f hf hx] at he
  rw [he]
  have hx'R : x' ∈ Icc (-R) R := (uIcc_subset_Icc h0 h1) (Ioo_subset_Icc_self hx')
  have hb := hC x' hx'R
  rw [Real.norm_eq_abs] at hb
  rw [abs_div, abs_mul, abs_pow]
  have hf6 : |((2 + 1).factorial : ℝ)| = 6 := by norm_num [Nat.factorial]
  rw [hf6]
  have hp : 0 ≤ |x - x0| ^ (2 + 1) := by positivity
  have : |iteratedDeriv (2 + 1) f x'| * |x - x0| ^ (2 + 1) ≤ max C 0 * |x - x0| ^ (2 + 1) :=
    mul_le_mul_of_nonneg_right (hb.trans (le_max_left _ _)) hp
  have h3 : 0 ≤ max C 0 * |x - x0| ^ (2 + 1) := mul_nonneg (le_max_right _ _) hp
  calc |iteratedDeriv (2 + 1) f x'| * |x - x0| ^ (2 + 1) / 6 ≤ max C 0 * |x - x0| ^ (2 + 1) / 6 :=
        div_le_div_of_nonneg_right this (by norm_num)
    _ ≤ max C 0 * |x - x0| ^ 3 := by
        have h3' : 0 ≤ max C 0 * |x - x0| ^ 3 := mul_nonneg (le_max_right _ _) (by positivity)
        rw [show 2 + 1 = 3 from rfl]; linarith

end Wall15

open Wall15

theorem p4_15_1 : CFDLean.JST1.Spec.P4_15_1 := by
  intro f r hf
  set main := fun h : ℝ => (r - 1) * h * deriv f h + (1 / 2) * (1 + r ^ 2) * h ^ 2 * deriv (deriv f) h
    with hmain
  set E := fun h => Spec.wnLk f r h - main h with hE
  obtain ⟨C, hC0, hC⟩ := taylor2_bound f hf (1 + |1 + r|)
  set K := C * (1 + |r| ^ 3) with hK
  have hK0 : 0 ≤ K := mul_nonneg hC0 (by positivity)
  have hbound : ∀ h, |h| ≤ 1 → |E h| ≤ K * |h| ^ 3 := by
    intro h hh
    have hmem : ∀ t, |t| ≤ 1 + |1 + r| → t ∈ Icc (-(1 + |1 + r|)) (1 + |1 + r|) := fun t ht => abs_le.1 ht
    have h0 := hmem 0 (by positivity)
    have hh' := hmem h (by linarith [abs_nonneg (1 + r)])
    have h2 := hmem ((1 + r) * h) (by
      rw [abs_mul]; nlinarith [abs_nonneg (1 + r), abs_nonneg h])
    have t1 := hC h 0 hh' h0
    have t2 := hC h ((1 + r) * h) hh' h2
    have eq : E h = (f 0 - (f h + deriv f h * (0 - h) + deriv (deriv f) h * (0 - h) ^ 2 / 2)) +
        (f ((1 + r) * h) - (f h + deriv f h * ((1 + r) * h - h) +
          deriv (deriv f) h * ((1 + r) * h - h) ^ 2 / 2)) := by
      simp only [hE, hmain, Spec.wnLk]; ring
    rw [eq]
    have e1 : |(0 : ℝ) - h| = |h| := by rw [zero_sub, abs_neg]
    have e2 : |(1 + r) * h - h| = |r| * |h| := by rw [show (1 + r) * h - h = r * h by ring, abs_mul]
    rw [e1] at t1
    rw [e2] at t2
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ C * |h| ^ 3 + C * (|r| * |h|) ^ 3 := add_le_add t1 t2
      _ = K * |h| ^ 3 := by rw [hK]; ring
  have hev : ∀ᶠ h : ℝ in 𝓝 0, |h| < 1 :=
    (continuous_abs.continuousAt (x := (0 : ℝ))).eventually_lt continuousAt_const (by simp)
  have hd1 : Continuous (deriv f) := by
    have := hf.continuous_iteratedDeriv 1 (by norm_num); rwa [iteratedDeriv_one] at this
  have hd2 : Continuous (deriv (deriv f)) := by
    have := hf.continuous_iteratedDeriv 2 (by norm_num)
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at this
  refine ⟨?_, ?_, ?_⟩
  · refine IsBigO.of_bound K ?_
    filter_upwards [hev] with h hh
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    exact hbound h hh.le
  · have hEh : Tendsto (fun h => E h / h) (𝓝[≠] 0) (𝓝 0) := by
      have ht : Tendsto (fun h : ℝ => K * |h| ^ 2) (𝓝[≠] 0) (𝓝 0) := by
        have : Tendsto (fun h : ℝ => K * |h| ^ 2) (𝓝 0) (𝓝 (K * |(0 : ℝ)| ^ 2)) :=
          ((continuous_const.mul (continuous_abs.pow 2)).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ ht
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hh hne
      rw [Real.norm_eq_abs, abs_div, div_le_iff₀ (abs_pos.2 hne)]
      calc |E h| ≤ K * |h| ^ 3 := hbound h hh.le
        _ = K * |h| ^ 2 * |h| := by ring
    have hlim : Tendsto (fun h => (r - 1) * deriv f h + (1 / 2) * (1 + r ^ 2) * h * deriv (deriv f) h + E h / h)
        (𝓝[≠] 0) (𝓝 ((r - 1) * deriv f 0)) := by
      have h1 : Tendsto (fun h => (r - 1) * deriv f h + (1 / 2) * (1 + r ^ 2) * h * deriv (deriv f) h)
          (𝓝 0) (𝓝 ((r - 1) * deriv f 0 + (1 / 2) * (1 + r ^ 2) * 0 * deriv (deriv f) 0)) := by
        have := ((hd1.tendsto 0).const_mul (r - 1)).add
          ((tendsto_id.const_mul ((1 / 2) * (1 + r ^ 2))).mul (hd2.tendsto 0))
        simpa [mul_assoc] using this
      have := (h1.mono_left nhdsWithin_le_nhds).add hEh
      simpa using this
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hne
    have hne' : h ≠ 0 := hne
    simp only [hE, hmain]
    field_simp
    ring
  · intro hr1
    subst hr1
    have hEh : Tendsto (fun h => E h / h ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have ht : Tendsto (fun h : ℝ => K * |h|) (𝓝[≠] 0) (𝓝 0) := by
        have : Tendsto (fun h : ℝ => K * |h|) (𝓝 0) (𝓝 (K * |(0 : ℝ)|)) :=
          ((continuous_const.mul continuous_abs).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ ht
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hh hne
      have hne' : h ≠ 0 := hne
      rw [Real.norm_eq_abs, abs_div, abs_pow, div_le_iff₀ (by positivity)]
      calc |E h| ≤ K * |h| ^ 3 := hbound h hh.le
        _ = K * |h| * |h| ^ 2 := by ring
    have hlim : Tendsto (fun h => deriv (deriv f) h + E h / h ^ 2) (𝓝[≠] 0) (𝓝 (deriv (deriv f) 0)) := by
      simpa using ((hd2.tendsto 0).mono_left nhdsWithin_le_nhds).add hEh
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hne
    have hne' : h ≠ 0 := hne
    simp only [hE, hmain]
    field_simp
    ring

theorem p4_15_2 : CFDLean.JST1.Spec.P4_15_2 := by
  refine ⟨fun e4l σ L0 he hσ => ⟨fun us => ?_, fun he' hL => ?_⟩, fun a r h ha hr hh => ?_⟩
  · have h1 : (1 + e4l / σ) ≠ 0 := by positivity
    have hσ' : σ ≠ 0 := hσ.ne'
    have h2 : e4l + σ ≠ 0 := by positivity
    rw [eq_div_iff h1]
    constructor
    · intro h; field_simp; linarith
    · intro h; field_simp at h; linarith
  · have : 0 < e4l / σ * L0 := mul_pos (div_pos he' hσ) hL
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  · have := mul_pos (mul_pos ha hh) (sub_pos.2 hr)
    nlinarith

theorem p4_15_3 : CFDLean.JST1.Spec.P4_15_3 := by
  intro ι C Q _ _ _ _ d S u s k α
  simp [Scheme.diss2, Scheme.ut', enthalpyState, eE, mom]

theorem p4_15_4 : CFDLean.JST1.Spec.P4_15_4 := by
  intro ι C Q _ _ _ _ _ d S bd fq aq u isWall
  dsimp only
  have hd2 : ∀ i k, Scheme.diss2 (Spec.cutWall S isWall) u i k =
      if isWall i ≠ isWall k then 0 else Scheme.diss2 S u i k := by
    intro i k
    by_cases h : isWall i ≠ isWall k
    · simp only [Scheme.diss2, Spec.cutWall, h, ite_true, mul_zero, zero_smul, ne_eq, not_false_eq_true]
    · simp only [Scheme.diss2, Spec.cutWall, h, ite_false]; rfl
  have hd4 : ∀ i k, Scheme.diss4 (Spec.cutWall S isWall) u i k =
      if isWall i ≠ isWall k then 0 else Scheme.diss4 S u i k := by
    intro i k
    by_cases h : isWall i ≠ isWall k
    · simp only [Scheme.diss4, Spec.cutWall, h, ite_true, mul_zero, zero_smul, ne_eq, not_false_eq_true]
    · simp only [Scheme.diss4, Spec.cutWall, h, ite_false]; rfl
  have hw : Scheme.w (Spec.cutWall S isWall) u = Scheme.w S u := rfl
  refine ⟨fun i k h => by simp [hd2, hd4, h], fun i k h => by simp [hd2, hd4, h],
    fun i k => rfl, fun i => ⟨rfl, rfl, rfl⟩, fun i => ?_, fun hA hnn i k => ?_, ?_, ?_, fun hS => ?_⟩
  · have hk : ∀ k, Scheme.central (Spec.cutWall S isWall) u i k + Scheme.diss2 (Spec.cutWall S isWall) u i k -
        Scheme.diss4 (Spec.cutWall S isWall) u i k =
        (Scheme.central S u i k + Scheme.diss2 S u i k - Scheme.diss4 S u i k) -
        (if isWall i ≠ isWall k then Scheme.diss2 S u i k - Scheme.diss4 S u i k else 0) := by
      intro k
      rw [hd2, hd4]
      by_cases h : isWall i ≠ isWall k
      · simp only [h, ite_true, ne_eq, not_false_eq_true]
        show Scheme.central S u i k + 0 - 0 = _
        abel
      · simp only [h, ite_false]
        show Scheme.central S u i k + Scheme.diss2 S u i k - Scheme.diss4 S u i k = _
        abel
    simp only [Scheme.resid]
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_sub_distrib]
    show -(_ - _) - Scheme.closure S u i + Scheme.visc S u i + Scheme.wall S u i = _
    abel
  · have := (p1_1_5 d S.g (u i) (u k) (S.lam i k) (S.eps2 i k) (hA i) (hA k) (hnn i k).1 (hnn i k).2).2
    exact this.1.trans this.2
  · simp only [Scheme.Pi2, hw, hd2]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : isWall i ≠ isWall k
    · simp only [h, ite_true, ne_eq, not_false_eq_true]
      simp [pairF]
    · simp only [h, ite_false, add_zero]
  · have hsum : (∑ i, ∑ k, pairF (Scheme.w S u k - Scheme.w S u i) (Scheme.diss4 S u i k)) =
        (∑ i, ∑ k, pairF (Scheme.w S u k - Scheme.w S u i)
          (if isWall i ≠ isWall k then 0 else Scheme.diss4 S u i k)) +
        ∑ i, ∑ k, (if isWall i ≠ isWall k then
          pairF (Scheme.w S u k - Scheme.w S u i) (Scheme.diss4 S u i k) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : isWall i ≠ isWall k
      · simp [h, pairF]
      · simp [h]
    simp only [Scheme.Pi4, hw, hd4]
    rw [hsum]
    ring
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := hS
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, fun i k => ?_, fun i k => ?_,
      h16, h17, h18, h19⟩
    · refine ⟨(h14 i k).1, ?_, ?_⟩
      · show (if isWall k ≠ isWall i then 0 else S.eps2 k i) = (if isWall i ≠ isWall k then 0 else S.eps2 i k)
        simp only [(h14 i k).2.1, ne_comm]
      · show (if isWall k ≠ isWall i then 0 else S.eps4 k i) = (if isWall i ≠ isWall k then 0 else S.eps4 i k)
        simp only [(h14 i k).2.2, ne_comm]
    · refine ⟨(h15 i k).1, ?_, ?_⟩
      · show 0 ≤ (if isWall i ≠ isWall k then 0 else S.eps2 i k)
        split_ifs <;> simp [(h15 i k).2.1]
      · show 0 ≤ (if isWall i ≠ isWall k then 0 else S.eps4 i k)
        split_ifs <;> simp [(h15 i k).2.2]

theorem p4_15_5 : CFDLean.JST1.Spec.P4_15_5 := by
  intro d g us uk r lam eps4 hs hk hr hl he
  dsimp only
  have hL : (enthalpyState g us - enthalpyState g uk) +
      (enthalpyState g us + (1 + r) • (enthalpyState g uk - enthalpyState g us) - enthalpyState g uk) -
        (0 : State d) = (r - 1) • (enthalpyState g uk - enthalpyState g us) := by
    funext c; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; ring
  have hP : pairF (entropyVars g uk - entropyVars g us)
      (-((lam * eps4) • ((0 : State d) - ((enthalpyState g us - enthalpyState g uk) +
        (enthalpyState g us + (1 + r) • (enthalpyState g uk - enthalpyState g us) - enthalpyState g uk))))) =
      eps4 * (r - 1) * lam * pairF (entropyVars g uk - entropyVars g us)
        (enthalpyState g uk - enthalpyState g us) := by
    unfold pairF
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.zero_apply]
    ring
  refine ⟨hL, hP, ?_⟩
  rw [hP]
  have h12 := p1_1_2 d g us uk hs hk
  have h13 := p1_1_3 d g us uk hs hk
  have hlow : 0 < lamLow g.γ := by linarith [three_quarter_lt_lamLow g.one_lt_γ]
  have : 0 ≤ pairF (entropyVars g uk - entropyVars g us) (enthalpyState g uk - enthalpyState g us) :=
    le_trans (mul_nonneg hlow.le h13) h12.1
  exact mul_nonneg (mul_nonneg (mul_nonneg he (by linarith)) hl) this

/-! ### The spectrum of the linear model -/

namespace Wall15
variable {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj] (isWall : V → Bool)

/-- The cut graph Laplacian `(K u)_i = Σ_{k ~ i, same side} (u_k - u_i)`. -/
def Kop (u : V → ℂ) (i : V) : ℂ := ∑ k, if adj i k ∧ isWall i = isWall k then u k - u i else 0

theorem cond_symm (hs : ∀ i k, adj i k → adj k i) (i k : V) :
    (adj i k ∧ isWall i = isWall k) ↔ (adj k i ∧ isWall k = isWall i) :=
  ⟨fun h => ⟨hs _ _ h.1, h.2.symm⟩, fun h => ⟨hs _ _ h.1, h.2.symm⟩⟩

theorem swap_sum (hs : ∀ i k, adj i k → adj k i) (F : V → V → ℂ) :
    (∑ i, ∑ k, if adj i k ∧ isWall i = isWall k then F i k else 0) =
      ∑ i, ∑ k, if adj i k ∧ isWall i = isWall k then F k i else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  exact if_congr (cond_symm adj isWall hs k i) rfl rfl

theorem symmK (hs : ∀ i k, adj i k → adj k i) (x y : V → ℂ) :
    ∑ i, conj (x i) * Kop adj isWall y i = ∑ i, conj (Kop adj isWall x i) * y i := by
  simp only [Kop, Finset.mul_sum, Finset.sum_mul, map_sum]
  have l : ∀ i k, conj (x i) * (if adj i k ∧ isWall i = isWall k then y k - y i else 0) =
      (if adj i k ∧ isWall i = isWall k then conj (x i) * y k else 0) -
      (if adj i k ∧ isWall i = isWall k then conj (x i) * y i else 0) := by
    intro i k; split_ifs <;> ring
  have r : ∀ i k, conj (if adj i k ∧ isWall i = isWall k then x k - x i else 0) * y i =
      (if adj i k ∧ isWall i = isWall k then conj (x k) * y i else 0) -
      (if adj i k ∧ isWall i = isWall k then conj (x i) * y i else 0) := by
    intro i k
    split_ifs
    · rw [map_sub]; ring
    · simp
  simp only [l, r, Finset.sum_sub_distrib]
  rw [swap_sum adj isWall hs (fun i k => conj (x k) * y i)]

theorem formK (hs : ∀ i k, adj i k → adj k i) (y : V → ℂ) :
    ∑ i, conj (y i) * Kop adj isWall y i =
      -(((1 / 2 : ℝ) * ∑ i, ∑ k, if adj i k ∧ isWall i = isWall k then Complex.normSq (y k - y i) else 0 : ℝ) : ℂ) := by
  have h1 : ∑ i, conj (y i) * Kop adj isWall y i =
      ∑ i, ∑ k, if adj i k ∧ isWall i = isWall k then conj (y i) * (y k - y i) else 0 := by
    simp only [Kop, Finset.mul_sum, mul_ite, mul_zero]
  have h2 := swap_sum adj isWall hs (fun i k => conj (y i) * (y k - y i))
  have h3 : ∀ i k, (if adj i k ∧ isWall i = isWall k then conj (y k) * (y i - y k) else 0) +
      (if adj i k ∧ isWall i = isWall k then conj (y i) * (y k - y i) else 0) =
      -((if adj i k ∧ isWall i = isWall k then Complex.normSq (y k - y i) else 0 : ℝ) : ℂ) := by
    intro i k
    split_ifs
    · rw [Complex.normSq_eq_conj_mul_self, map_sub]; ring
    · simp
  have h4 : 2 * ∑ i, conj (y i) * Kop adj isWall y i =
      -((∑ i, ∑ k, if adj i k ∧ isWall i = isWall k then Complex.normSq (y k - y i) else 0 : ℝ) : ℂ) := by
    rw [two_mul]
    nth_rewrite 1 [h1]
    rw [h2, h1, ← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, h3]
    simp only [Finset.sum_neg_distrib, Complex.ofReal_sum]
  have h5 := h4
  push_cast at h5 ⊢
  linear_combination (1 / 2 : ℂ) * h5

theorem sum_normSq (x : V → ℂ) : ∑ i, conj (x i) * x i = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  push_cast
  exact Finset.sum_congr rfl fun i _ => (Complex.normSq_eq_conj_mul_self).symm

theorem sum_normSq_pos {x : V → ℂ} (hx : x ≠ 0) : 0 < ∑ i, Complex.normSq (x i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  exact lt_of_lt_of_le (Complex.normSq_pos.2 hi)
    (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i))

theorem real_of_mul {μ : ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (h : μ * a = b) : μ.im = 0 ∧ 0 ≤ μ.re := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hμ : μ = ((b / a : ℝ) : ℂ) := by rw [Complex.ofReal_div, eq_div_iff ha', h]
  rw [hμ]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  exact div_nonneg hb ha.le

theorem Kop_congr (u u' : V → ℂ) (i : V) (h : ∀ k, isWall k = isWall i → u k = u' k) :
    Kop adj isWall u i = Kop adj isWall u' i := by
  unfold Kop
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hc
  · rw [h k hc.2.symm, h i rfl]
  · rfl

end Wall15

theorem p4_15_6 : CFDLean.JST1.Spec.P4_15_6 := by
  intro V _ _ adj _ isWall hs μ v hv hμ
  have hF : ∀ i, Wall15.Kop adj isWall (Spec.lapStar adj isWall v) i = μ * v i := fun i => by
    have := congrFun hμ i
    simpa [Spec.fourthOp, Wall15.Kop] using this
  by_cases hw : ∃ i, isWall i = true ∧ v i ≠ 0
  · -- a wall eigenvector component: `K² x = μ x` for the wall part `x`
    set x : V → ℂ := fun i => if isWall i then v i else 0 with hx
    have hKx : ∀ i, Wall15.Kop adj isWall x i = if isWall i then Spec.lapStar adj isWall v i else 0 := by
      intro i
      by_cases hi : isWall i = true
      · simp only [hi, ite_true, Wall15.Kop, Spec.lapStar, hx]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : isWall k = true
        · simp [hk]
        · simp [hk]
      · simp only [hi, Wall15.Kop, hx]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : isWall k = true
        · simp [hk]
        · simp [hk]
    have hKKx : ∀ i, Wall15.Kop adj isWall (Wall15.Kop adj isWall x) i = μ * x i := by
      intro i
      by_cases hi : isWall i = true
      · rw [Wall15.Kop_congr adj isWall _ (Spec.lapStar adj isWall v) i (fun k hk => by
          rw [hKx, hk, hi]; simp), hF i]
        simp [hx, hi]
      · rw [Wall15.Kop_congr adj isWall _ 0 i (fun k hk => by
          rw [hKx, hk]; simp [hi])]
        simp [Wall15.Kop, hx, hi]
    have hx0 : x ≠ 0 := by
      obtain ⟨i, hi, hvi⟩ := hw
      intro h
      have := congrFun h i
      simp [hx, hi] at this
      exact hvi this
    have e1 : ∑ i, conj (x i) * Wall15.Kop adj isWall (Wall15.Kop adj isWall x) i =
        μ * ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
      rw [← Wall15.sum_normSq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hKKx]; ring
    rw [Wall15.symmK adj isWall hs, Wall15.sum_normSq] at e1
    exact Wall15.real_of_mul (Wall15.sum_normSq_pos hx0)
      (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) e1.symm
  · -- the wall part vanishes: `L v = (K - D) v` and `K (K - D) v = μ v`
    push Not at hw
    set D : V → ℝ := fun i => ∑ k, if adj i k ∧ isWall i = false ∧ isWall k = true then (1 : ℝ) else 0 with hD
    have hD0 : ∀ i, 0 ≤ D i := fun i => Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num
    have hL : ∀ i, Spec.lapStar adj isWall v i = Wall15.Kop adj isWall v i - (D i : ℂ) * v i := by
      intro i
      have hDc : ((D i : ℝ) : ℂ) = ∑ k, if adj i k ∧ isWall i = false ∧ isWall k = true then (1 : ℂ) else 0 := by
        simp only [hD, Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
      rw [hDc, Finset.sum_mul, Wall15.Kop, Spec.lapStar, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases ha : adj i k
      · cases hi : isWall i <;> cases hk : isWall k <;> simp [ha, hi, hk, hw i, hw k]
      · simp [ha]
    set y := Spec.lapStar adj isWall v with hy
    have hKy : ∀ i, Wall15.Kop adj isWall y i = μ * v i := hF
    set P : ℝ := ∑ i, ∑ k, if adj i k ∧ isWall i = isWall k then Complex.normSq (y k - y i) else 0 with hP
    set Pv : ℝ := ∑ i, ∑ k, if adj i k ∧ isWall i = isWall k then Complex.normSq (v k - v i) else 0 with hPv
    set Q : ℝ := (1 / 2) * Pv + ∑ i, D i * Complex.normSq (v i) with hQ
    have hPv0 : ∀ i k, 0 ≤ (if adj i k ∧ isWall i = isWall k then Complex.normSq (v k - v i) else 0) :=
      fun i k => by split_ifs <;> simp [Complex.normSq_nonneg]
    have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by
      split_ifs <;> simp [Complex.normSq_nonneg]
    have hPvn : 0 ≤ Pv := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hPv0 i k
    have hDn : 0 ≤ ∑ i, D i * Complex.normSq (v i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hD0 i) (Complex.normSq_nonneg _)
    have e1 := Wall15.formK adj isWall hs y
    have e2 : ∑ i, conj (y i) * Wall15.Kop adj isWall y i = μ * ∑ i, conj (y i) * v i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hKy]; ring
    have e3 : ∑ i, conj (y i) * v i = -((Q : ℝ) : ℂ) := by
      have : ∑ i, conj (y i) * v i = ∑ i, conj (Wall15.Kop adj isWall v i) * v i -
          ∑ i, (D i : ℂ) * (conj (v i) * v i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hL, map_sub, map_mul, Complex.conj_ofReal]; ring
      rw [this, ← Wall15.symmK adj isWall hs, Wall15.formK adj isWall hs]
      simp only [hQ, hPv, ← Complex.normSq_eq_conj_mul_self]
      push_cast
      ring
    rw [e2, e3, ← hP] at e1
    have hμQ : μ * ((Q : ℝ) : ℂ) = (((1 / 2) * P : ℝ) : ℂ) := by
      linear_combination -e1
    rcases (show 0 ≤ Q by positivity).lt_or_eq with hQp | hQz
    · exact Wall15.real_of_mul hQp (by positivity) hμQ
    · -- `Q = 0`: then `y = L v = 0`, so `μ v = 0`
      have hPvz : Pv = 0 := by linarith
      have hDz : ∑ i, D i * Complex.normSq (v i) = 0 := by linarith
      have hc : ∀ i k, adj i k ∧ isWall i = isWall k → v k = v i := by
        intro i k hik
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun k _ => hPv0 i k)).1
          hPvz i (Finset.mem_univ _)
        have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hPv0 i k)).1 h1 k (Finset.mem_univ _)
        simp only [hik, and_self, ite_true] at h2
        exact sub_eq_zero.1 (Complex.normSq_eq_zero.1 h2)
      have hdv : ∀ i, (D i : ℂ) * v i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => mul_nonneg (hD0 i) (Complex.normSq_nonneg (v i)))).1 hDz i (Finset.mem_univ _)
        rcases mul_eq_zero.1 this with h | h
        · simp [h]
        · simp [Complex.normSq_eq_zero.1 h]
      have hy0 : ∀ i, y i = 0 := by
        intro i
        rw [hL, hdv, sub_zero, Wall15.Kop]
        refine Finset.sum_eq_zero fun k _ => ?_
        split_ifs with h
        · rw [hc i k h, sub_self]
        · rfl
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
      have h0 : μ * v i = 0 := by
        rw [← hKy, Wall15.Kop]
        exact Finset.sum_eq_zero fun k _ => by simp [hy0]
      have hμ0 : μ = 0 := (mul_eq_zero.1 h0).resolve_right hi
      simp [hμ0]

end CFDLean.JST1.Proofs
