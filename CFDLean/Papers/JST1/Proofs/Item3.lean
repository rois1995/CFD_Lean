import CFDLean.Papers.JST1.Spec.Item3

noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

theorem dot_smul_left' {d : ℕ} (c : ℝ) (u v : Vec d) : Num.dot (c • u) v = c * Num.dot u v := by
  simp only [Num.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_smul_right' {d : ℕ} (c : ℝ) (u v : Vec d) : Num.dot u (c • v) = c * Num.dot u v := by
  simp only [Num.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem len_smul {d : ℕ} (c : ℝ) (u : Vec d) : len (c • u) = |c| * len u := by
  unfold len
  rw [dot_smul_left', dot_smul_right', ← mul_assoc, Real.sqrt_mul' _ (by
      unfold Num.dot; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _),
    Real.sqrt_mul_self_eq_abs]

theorem nuOf_smul {d : ℕ} (c : ℝ) (y e : Vec d) : WMesh.nuOf (c • y) e = c • WMesh.nuOf y e := by
  unfold WMesh.nuOf
  rw [dot_smul_left', smul_smul, mul_div_assoc]

theorem radFull_smul {d : ℕ} (vb : Vec d) (cb c : ℝ) (y : Vec d) (hc : 0 ≤ c) :
    radFull vb cb (c • y) = c * radFull vb cb y := by
  unfold radFull
  rw [dot_smul_right', len_smul, abs_mul, abs_of_nonneg hc]; ring

theorem lamHat_smul {d : ℕ} (vb : Vec d) (cb c : ℝ) (e y : Vec d) (hc : 0 ≤ c) :
    lamHat vb cb e (c • y) = c * lamHat vb cb e y := by
  unfold lamHat
  rw [nuOf_smul, dot_smul_right', len_smul, abs_mul, abs_of_nonneg hc]; ring

theorem radFull_zero {d : ℕ} (vb : Vec d) (cb : ℝ) : radFull vb cb 0 = 0 := by
  simp [radFull, Num.dot, len]

theorem phiF_scale (c x y : ℝ) (hc : c ≠ 0) : phiF (c * x) (c * y) = c * phiF x y := by
  unfold phiF
  rcases eq_or_ne (x + y) 0 with h | h
  · have h' : c * x + c * y = 0 := by rw [← mul_add, h, mul_zero]
    rw [h', h]; simp
  · have h' : c * x + c * y ≠ 0 := by rw [← mul_add]; exact mul_ne_zero hc h
    field_simp

/-- `Σ_s ω_s (if χ then X else 0) = π X`. -/
theorem sum_ite_share {ι σ : Type} [Fintype σ] (ω : σ → ℝ) (χ : σ → ι → ι → Bool) (i k : ι) (X : ℝ) :
    (∑ s, ω s * (if χ s i k then X else 0)) = piShare ω χ i k * X := by
  unfold piShare
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp

theorem p1_3_2 : Spec.P1_3_2 := by
  intro ι σ κ _ _ ω χ
  refine ⟨?_, ?_⟩
  · intro ut Nstar i
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold piShare
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun s _ => by split_ifs <;> simp
  · intro f i
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sum_ite_share]

theorem p1_3_1 : Spec.P1_3_1 := by
  intro ι σ _ _ d ω χ n vb cb bnd i hω hsum hpi hzero
  unfold LamOn
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : ∃ s, χ s i k = true
  · have hp := hpi k hk
    have : ∀ s, ω s * radFull (vb i k) (cb i k) (nSplit ω χ n s i k) =
        ω s * (if χ s i k then (piShare ω χ i k)⁻¹ * radFull (vb i k) (cb i k) (n i k) else 0) := by
      intro s
      unfold nSplit
      split_ifs
      · rw [radFull_smul _ _ _ _ (inv_nonneg.mpr hp.le)]
      · rw [radFull_zero]
    rw [Finset.sum_congr rfl fun s _ => this s, sum_ite_share, ← mul_assoc, mul_inv_cancel₀ hp.ne',
      one_mul]
  · push Not at hk
    have hn : n i k = 0 := hzero k fun s => by simpa using hk s
    have : ∀ s, nSplit ω χ n s i k = 0 := by
      intro s; unfold nSplit; rw [hn]; simp
    simp only [this, hn, radFull_zero, mul_zero, Finset.sum_const_zero]

theorem p1_3_3 : Spec.P1_3_3 := by
  intro ι σ κ _ _ d ω χ n e vb cb Lam a D i k _hω hpi hlh hLi hLk
  set p := piShare ω χ i k with hpdef
  set lh := lamHat (vb i k) (cb i k) (e i k) (n i k) with hlhdef
  have hpa : 0 < p ^ a := Real.rpow_pos_of_pos hpi a
  have hcoefS : ∀ s, χ s i k = true →
      coefOn vb cb e Lam a (fun j l => nSplit ω χ n s j l) i k =
        p⁻¹ * (p ^ a * coefOn vb cb e Lam a n i k) := by
    intro s hs
    have hn' : nSplit ω χ n s i k = p⁻¹ • n i k := by unfold nSplit; rw [ite_eq_left hs]
    have hl' : lamHat (vb i k) (cb i k) (e i k) (nSplit ω χ n s i k) = p⁻¹ * lh := by
      rw [hn', lamHat_smul _ _ _ _ _ (inv_nonneg.mpr hpi.le)]
    have hpsi : ∀ L : ℝ, 0 < L → psiF L (p⁻¹ * lh) a = p ^ a * psiF L lh a := by
      intro L hL
      unfold psiF
      have : L / (4 * (p⁻¹ * lh)) = p * (L / (4 * lh)) := by field_simp
      rw [this, Real.mul_rpow hpi.le (div_nonneg hL.le (by linarith))]
    simp only [coefOn]
    rw [hl', hpsi _ hLi, hpsi _ hLk, phiF_scale _ _ _ hpa.ne']
    field_simp
    ring
  have : ∀ s, ω s • (if χ s i k = true then
        coefOn vb cb e Lam a (fun j l => nSplit ω χ n s j l) i k • D else 0) =
      (ω s * (if χ s i k = true then p⁻¹ * (p ^ a * coefOn vb cb e Lam a n i k) else 0)) • D := by
    intro s
    by_cases hs : χ s i k = true
    · rw [ite_eq_left hs, ite_eq_left hs, hcoefS s hs, smul_smul]
    · rw [ite_eq_right hs, ite_eq_right hs]; simp
  rw [Finset.sum_congr rfl fun s _ => this s, ← Finset.sum_smul, sum_ite_share, ← hpdef, ← mul_assoc,
    mul_inv_cancel₀ hpi.ne', one_mul]

theorem p1_3_4 : Spec.P1_3_4 := by
  intro ι d n e vb cb Lam a p i k hp
  rw [hp, Real.one_rpow, one_mul]

end CFDLean.JST1.Proofs
