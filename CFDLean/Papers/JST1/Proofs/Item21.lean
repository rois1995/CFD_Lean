import CFDLean.Papers.JST1.Spec.Item21
import CFDLean.Papers.JST1.Proofs.Item16

/-! Proofs of item 21 (P6): `∫_T φ_b = |T|/(d+1)`. The standard simplex `Δ_d = {t ≥ 0, Σ t ≤ 1}` has volume `1/d!`
(Fubini and scaling); `T = x_0 + E Δ_d` has volume `|det E|/d!`; the affine involution of `T` that swaps two vertices
preserves the measure and swaps their barycentric coordinates, so all `∫_T φ_b` are equal, and they sum to `|T|`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num MeasureTheory Set Pointwise
namespace CFDLean.JST1.Proofs
namespace Int21

/-- `Δ_d(s) = {t ≥ 0, Σ t ≤ s}`. -/
def stdS (d : ℕ) (s : ℝ) : Set (Fin d → ℝ) := {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ s}

theorem isClosed_stdS (d : ℕ) (s : ℝ) : IsClosed (stdS d s) := by
  have h1 : IsClosed {t : Fin d → ℝ | ∀ i, 0 ≤ t i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact h1.inter (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

theorem stdS_smul (d : ℕ) {s : ℝ} (hs : 0 ≤ s) : s • stdS d 1 = stdS d s := by
  ext x
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨fun i => mul_nonneg hs (ht0 i), ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    nlinarith
  · rintro ⟨hx0, hx1⟩
    rcases hs.eq_or_lt with h | h
    · subst h
      have hx : x = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hx0 j).mp
          (le_antisymm hx1 (Finset.sum_nonneg fun j _ => hx0 j)) i (Finset.mem_univ _)
        simpa using this
      exact ⟨0, ⟨fun _ => le_rfl, by simp⟩, by simp [hx]⟩
    · refine ⟨s⁻¹ • x, ⟨fun i => mul_nonneg (inv_nonneg.mpr hs) (hx0 i), ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ h]; linarith
      · show s • s⁻¹ • x = x
        rw [smul_smul, mul_inv_cancel₀ h.ne', one_smul]

theorem volume_stdS_scale (d : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume (stdS d s) = ENNReal.ofReal (s ^ d) * volume (stdS d 1) := by
  rw [← stdS_smul d hs, Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_nonneg (pow_nonneg hs d)]

theorem volume_stdS_one : ∀ d : ℕ, volume (stdS d 1) = ENNReal.ofReal (1 / (Nat.factorial d)) := by
  intro d
  induction d with
  | zero =>
    have : stdS 0 1 = univ := by ext t; simp [stdS]
    rw [this, volume_pi, Measure.pi_empty_univ]; simp
  | succ d ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have hmp : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove (fun _ => ℝ) 0
    set P : Set (ℝ × (Fin d → ℝ)) := {p | 0 ≤ p.1 ∧ p.2 ∈ stdS d (1 - p.1)}
    have hP : MeasurableSet P := by
      refine IsClosed.measurableSet (s := {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} ∩
        ({p | ∀ i, 0 ≤ p.2 i} ∩ {p | ∑ i, p.2 i ≤ 1 - p.1})) ?_
      refine IsClosed.inter (isClosed_le continuous_const continuous_fst) ?_
      have h1 : IsClosed {p : ℝ × (Fin d → ℝ) | ∀ i, 0 ≤ p.2 i} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)
      exact h1.inter (isClosed_le (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_snd)
        (continuous_const.sub continuous_fst))
    have hpre : stdS (d + 1) 1 = e ⁻¹' P := by
      ext t
      simp only [stdS, P, mem_preimage, mem_ofPred_eq, e, MeasurableEquiv.piFinSuccAbove_apply,
        Fin.insertNthEquiv_symm_apply, Fin.removeNth]
      rw [Fin.sum_univ_succ, Fin.forall_fin_succ]
      simp only [Fin.succAbove_zero]
      constructor
      · rintro ⟨⟨h0, hs⟩, h1⟩; exact ⟨h0, hs, by linarith⟩
      · rintro ⟨h0, hs, h1⟩; exact ⟨⟨h0, hs⟩, by linarith⟩
    have hslice : ∀ a : ℝ, volume (Prod.mk a ⁻¹' P) =
        Set.indicator (Icc 0 1) (fun a => ENNReal.ofReal ((1 - a) ^ d / (Nat.factorial d))) a := by
      intro a
      by_cases ha : a ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem ha]
        have : Prod.mk a ⁻¹' P = stdS d (1 - a) := by
          ext u; simp [P, ha.1]
        rw [this, volume_stdS_scale d (by linarith [ha.2]), ih,
          ← ENNReal.ofReal_mul (pow_nonneg (by linarith [ha.2]) _)]
        congr 1; ring
      · rw [indicator_of_notMem ha]
        have : Prod.mk a ⁻¹' P = ∅ := by
          ext u
          simp only [P, mem_preimage, mem_ofPred_eq, stdS, mem_empty_iff_false, iff_false, not_and]
          intro h0 hu0 hu1
          have : 1 < a := by
            by_contra h; exact ha ⟨h0, not_lt.mp h⟩
          linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hu0 j]
        rw [this, measure_empty]
    rw [hpre, hmp.measure_preimage hP.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_apply hP]
    simp only [hslice]
    rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
      simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ d), integral_pow]
      simp [Nat.factorial_succ]
      field_simp
    · exact (continuous_const.sub continuous_id |>.pow d |>.div_const _).integrableOn_Icc
    · exact (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun a ha =>
        div_nonneg (pow_nonneg (by linarith [ha.2]) _) (by positivity))

variable {d : ℕ}

/-- The affine map `t ↦ x_0 + E t` of the standard simplex onto `T`. -/
def aff (T : Simplex d) (t : Fin d → ℝ) : Vec d := T.x 0 + T.edgeMat.mulVec t

theorem dot_mulVec_edge (T : Simplex d) (u : Vec d) (t : Fin d → ℝ) :
    Num.dot u (T.edgeMat.mulVec t) = ∑ β, t β * Num.dot u (T.x β.succ - T.x 0) := by
  simp only [Num.dot, Matrix.mulVec, dotProduct, Simplex.edgeMat, Pi.sub_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem bary_vertex (T : Simplex d) (h : T.Nondeg) (b a : Fin (d + 1)) :
    Spec.bary T b (T.x a) = if b = a then 1 else 0 := by
  obtain ⟨-, hd, -, -, -⟩ := Simplex.calculus d T h
  simp only [Spec.bary, hd]
  split_ifs <;> simp_all

theorem bary_aff_zero (T : Simplex d) (h : T.Nondeg) (t : Fin d → ℝ) :
    Spec.bary T 0 (aff T t) = 1 - ∑ β, t β := by
  obtain ⟨-, hd, -, -, -⟩ := Simplex.calculus d T h
  simp only [Spec.bary, aff, add_sub_cancel_left, dot_mulVec_edge, hd]
  simp [(Fin.succ_ne_zero _).symm]
  ring

theorem bary_aff_succ (T : Simplex d) (h : T.Nondeg) (t : Fin d → ℝ) (γ : Fin d) :
    Spec.bary T γ.succ (aff T t) = t γ := by
  obtain ⟨-, hd, -, -, -⟩ := Simplex.calculus d T h
  simp only [Spec.bary, aff, add_sub_cancel_left, dot_mulVec_edge, hd]
  simp [Fin.succ_ne_zero, Fin.succ_inj]

theorem aff_surj (T : Simplex d) (h : T.Nondeg) (x : Vec d) :
    aff T (T.edgeMat⁻¹.mulVec (x - T.x 0)) = x := by
  have hu : IsUnit T.edgeMat.det := isUnit_iff_ne_zero.mpr h
  simp only [aff, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  abel

theorem bary_add_smul (T : Simplex d) (b : Fin (d + 1)) (x y : Vec d) {a c : ℝ} (hac : a + c = 1) :
    Spec.bary T b (a • x + c • y) = a * Spec.bary T b x + c * Spec.bary T b y := by
  have hc : c = 1 - a := by linarith
  subst hc
  simp only [Spec.bary, Num.dot, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  rw [show (∑ i, T.grad b i * (a * x i + (1 - a) * y i - T.x 0 i)) =
      ∑ i, (a * (T.grad b i * (x i - T.x 0 i)) + (1 - a) * (T.grad b i * (y i - T.x 0 i))) from
    Finset.sum_congr rfl fun _ _ => by ring, Finset.sum_add_distrib]
  ring

/-- The barycentric description of the closed simplex. -/
def bset (T : Simplex d) : Set (Vec d) := {x | ∀ b, 0 ≤ Spec.bary T b x}

theorem bset_eq_image (T : Simplex d) (h : T.Nondeg) : bset T = aff T '' stdS d 1 := by
  ext x
  constructor
  · intro hx
    refine ⟨_, ⟨fun γ => ?_, ?_⟩, aff_surj T h x⟩
    · have := hx γ.succ
      rwa [← aff_surj T h x, bary_aff_succ T h] at this
    · have := hx 0
      rw [← aff_surj T h x, bary_aff_zero T h] at this
      linarith
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩ b
    cases b using Fin.cases with
    | zero => rw [bary_aff_zero T h]; linarith
    | succ γ => rw [bary_aff_succ T h]; exact ht0 γ

theorem hull_eq_bset (T : Simplex d) (h : T.Nondeg) : Spec.hullT T = bset T := by
  apply le_antisymm
  · refine convexHull_min ?_ ?_
    · rintro _ ⟨a, rfl⟩ b
      rw [bary_vertex T h]; split_ifs <;> norm_num
    · intro x hx y hy a c ha hc hac b
      rw [bary_add_smul T b x y hac]
      have := hx b; have := hy b
      positivity
  · intro x hx
    rw [bset_eq_image T h] at hx
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
    set w : Fin (d + 1) → ℝ := Fin.cases (1 - ∑ β, t β) t
    have hw0 : ∀ b ∈ Finset.univ, 0 ≤ w b := by
      intro b _
      cases b using Fin.cases with
      | zero => simp only [w, Fin.cases_zero]; linarith
      | succ γ => simp only [w, Fin.cases_succ]; exact ht0 γ
    have hw1 : ∑ b, w b = 1 := by
      simp [w, Fin.sum_univ_succ]
    have hsum : ∑ b, w b • T.x b = aff T t := by
      rw [Fin.sum_univ_succ]
      funext α
      simp only [w, Fin.cases_zero, Fin.cases_succ, aff, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.mulVec, dotProduct, Simplex.edgeMat, Finset.sum_mul, sub_mul, one_mul]
      rw [Finset.sum_sub_distrib]
      simp only [mul_comm (T.x _ α) (t _)]
      ring
    rw [← hsum]
    exact (convex_convexHull ℝ _).sum_mem hw0 hw1 fun b _ => subset_convexHull ℝ _ ⟨b, rfl⟩

theorem volume_hull (T : Simplex d) (h : T.Nondeg) :
    volume (Spec.hullT T) = ENNReal.ofReal T.vol := by
  have himg : aff T '' stdS d 1 = (fun v => T.x 0 + v) '' (Matrix.toLin' T.edgeMat '' stdS d 1) := by
    rw [Set.image_image]; rfl
  rw [hull_eq_bset T h, bset_eq_image T h, himg, Set.image_add_left, measure_preimage_add,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin', volume_stdS_one,
    ← ENNReal.ofReal_mul (abs_nonneg _), Simplex.vol]
  congr 1; ring

theorem bary_add (T : Simplex d) (c : Fin (d + 1)) (x v : Vec d) :
    Spec.bary T c (x + v) = Spec.bary T c x + Num.dot (T.grad c) v := by
  simp only [Spec.bary, Num.dot, Pi.sub_apply, Pi.add_apply, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem bary_sub_zero (T : Simplex d) (c : Fin (d + 1)) (x : Vec d) :
    Spec.bary T c x - Spec.bary T c 0 = Num.dot (T.grad c) x := by
  have := bary_add T c 0 x
  rw [zero_add] at this
  linarith

theorem continuous_bary (T : Simplex d) (c : Fin (d + 1)) : Continuous (Spec.bary T c) := by
  unfold Spec.bary Num.dot
  fun_prop

theorem sum_bary (T : Simplex d) (h : T.Nondeg) (x : Vec d) : ∑ c, Spec.bary T c x = 1 := by
  obtain ⟨hg, -, -, -, -⟩ := Simplex.calculus d T h
  have h0 : ∑ c, Num.dot (T.grad c) (x - T.x 0) = 0 := by
    simp only [Num.dot, Pi.sub_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [← Finset.sum_mul]
    have := congrFun hg α
    simp only [Finset.sum_apply, Pi.zero_apply] at this
    rw [this, zero_mul]
  simp only [Spec.bary, Finset.sum_add_distrib, h0, add_zero]
  simp

/-- The affine involution of `T` swapping the vertices `a` and `b`. -/
def swapMap (T : Simplex d) (a b : Fin (d + 1)) (x : Vec d) : Vec d :=
  x + (Spec.bary T a x - Spec.bary T b x) • (T.x b - T.x a)

theorem bary_swap (T : Simplex d) (h : T.Nondeg) (a b c : Fin (d + 1)) (x : Vec d) :
    Spec.bary T c (swapMap T a b x) = Spec.bary T c x +
      (Spec.bary T a x - Spec.bary T b x) * ((if c = b then 1 else 0) - (if c = a then 1 else 0)) := by
  obtain ⟨-, hd, -, -, -⟩ := Simplex.calculus d T h
  have hs : ∀ (r : ℝ) (u v : Vec d), Num.dot u (r • v) = r * Num.dot u v := by
    intro r u v; simp only [Num.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [swapMap, bary_add, hs, hd]

theorem swap_swap (T : Simplex d) (h : T.Nondeg) {a b : Fin (d + 1)} (hab : a ≠ b) (x : Vec d) :
    swapMap T a b (swapMap T a b x) = x := by
  have ha := bary_swap T h a b a x
  have hb := bary_swap T h a b b x
  simp only [hab, hab.symm, ite_true, ite_false] at ha hb
  conv_lhs => rw [swapMap, ha, hb]
  rw [swapMap]
  have : (Spec.bary T a x + (Spec.bary T a x - Spec.bary T b x) * (0 - 1) -
      (Spec.bary T b x + (Spec.bary T a x - Spec.bary T b x) * (1 - 0))) =
      -(Spec.bary T a x - Spec.bary T b x) := by ring
  rw [this, neg_smul, add_neg_cancel_right]

theorem swap_mem (T : Simplex d) (h : T.Nondeg) (a b : Fin (d + 1)) {x : Vec d} (hx : x ∈ bset T) :
    swapMap T a b x ∈ bset T := by
  intro c
  rw [bary_swap T h]
  have h1 := hx a; have h2 := hx b; have h3 := hx c
  split_ifs with hcb hca hca <;> (try subst hcb) <;> (try subst hca) <;> linarith

theorem swap_image (T : Simplex d) (h : T.Nondeg) {a b : Fin (d + 1)} (hab : a ≠ b) :
    swapMap T a b '' bset T = bset T := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact swap_mem T h a b hx
  · intro x hx
    exact ⟨swapMap T a b x, swap_mem T h a b hx, swap_swap T h hab x⟩

/-- The linear part of `swapMap`: `y ↦ y + ((g_a - g_b)·y)(x_b - x_a)`. -/
def swapLin (T : Simplex d) (a b : Fin (d + 1)) : Vec d →L[ℝ] Vec d :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin' (1 + Matrix.vecMulVec (T.x b - T.x a) (T.grad a - T.grad b)))

theorem swapMap_eq (T : Simplex d) (a b : Fin (d + 1)) (x : Vec d) :
    swapMap T a b x = swapLin T a b x + swapMap T a b 0 := by
  have hx := bary_sub_zero T a x
  have hy := bary_sub_zero T b x
  simp only [swapLin, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.vecMulVec_mulVec, swapMap, zero_add]
  have hd : (T.grad a - T.grad b) ⬝ᵥ x = Num.dot (T.grad a) x - Num.dot (T.grad b) x := by
    simp only [dotProduct, Num.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [hd, ← hx, ← hy, op_smul_eq_smul]
  funext α
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem abs_det_swapLin (T : Simplex d) (h : T.Nondeg) {a b : Fin (d + 1)} (hab : a ≠ b) :
    |(swapLin T a b : Vec d →L[ℝ] Vec d).det| = 1 := by
  obtain ⟨-, hd, -, -, -⟩ := Simplex.calculus d T h
  have hdot : (T.grad a - T.grad b) ⬝ᵥ (T.x b - T.x a) = -2 := by
    have e1 := hd a b a
    have e2 := hd b b a
    simp only [hab, hab.symm, ite_true, ite_false] at e1 e2
    have : (T.grad a - T.grad b) ⬝ᵥ (T.x b - T.x a) =
        Num.dot (T.grad a) (T.x b - T.x a) - Num.dot (T.grad b) (T.x b - T.x a) := by
      simp only [dotProduct, Num.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [this, e1, e2]; norm_num
  rw [swapLin, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.vecMulVec_eq (ι := Unit), Matrix.det_one_add_replicateCol_mul_replicateRow, hdot]
  norm_num

theorem measurableSet_bset (T : Simplex d) (h : T.Nondeg) : MeasurableSet (bset T) := by
  rw [← hull_eq_bset T h]
  exact ((Set.finite_range T.x).isCompact_convexHull (𝕜 := ℝ)).isClosed.measurableSet

theorem integral_swap (T : Simplex d) (h : T.Nondeg) (a b : Fin (d + 1)) :
    ∫ x in bset T, Spec.bary T a x = ∫ x in bset T, Spec.bary T b x := by
  by_cases hab : a = b
  · rw [hab]
  have himg := swap_image T h hab
  conv_lhs => rw [← himg]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_bset T h)
    (f' := fun _ => swapLin T a b) (fun x _ => ?_) (fun x _ y _ hxy => ?_)]
  · refine setIntegral_congr_fun (measurableSet_bset T h) fun x _ => ?_
    simp only [abs_det_swapLin T h hab, one_smul]
    rw [bary_swap T h]
    simp [hab]
  · have : swapMap T a b = fun x => swapLin T a b x + swapMap T a b 0 := funext (swapMap_eq T a b)
    rw [this]
    exact ((swapLin T a b).hasFDerivAt.add_const _).hasFDerivWithinAt
  · rw [← swap_swap T h hab x, hxy, swap_swap T h hab y]

theorem integral_bary (T : Simplex d) (h : T.Nondeg) (b : Fin (d + 1)) :
    IntegrableOn (Spec.bary T b) (Spec.hullT T) ∧
      ∫ x in Spec.hullT T, Spec.bary T b x = T.vol / ((d : ℝ) + 1) := by
  have hcpt : IsCompact (Spec.hullT T) := (Set.finite_range T.x).isCompact_convexHull (𝕜 := ℝ)
  have hint : ∀ c, IntegrableOn (Spec.bary T c) (Spec.hullT T) :=
    fun c => (continuous_bary T c).continuousOn.integrableOn_compact hcpt
  refine ⟨hint b, ?_⟩
  have hsum : ∑ c, ∫ x in Spec.hullT T, Spec.bary T c x = T.vol := by
    rw [← integral_finsetSum _ fun c _ => hint c]
    simp only [sum_bary T h]
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, volume_hull T h,
      ENNReal.toReal_ofReal (Simplex.calculus d T h).2.2.2.1.le]
  rw [hull_eq_bset T h] at hsum ⊢
  simp only [integral_swap T h _ b, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [← hsum]
  push_cast
  field_simp

end Int21

open Int21

theorem p6_21_1 : CFDLean.JST1.Spec.P6_21_1 := fun _ T h =>
  ⟨hull_eq_bset T h, volume_hull T h⟩

theorem p6_21_2 : CFDLean.JST1.Spec.P6_21_2 := fun _ T h b => integral_bary T h b

namespace Int21

theorem divP1_eq {κ : Type} [Fintype κ] {d : ℕ} (T : Simplex d) (hT : T.Nondeg)
    (F : Fin (d + 1) → Matrix κ (Fin d) ℝ) (x : Vec d) (c : κ) :
    Spec.divP1 T F x c = ∑ β, ∑ b, T.grad b β * F b c β := by
  unfold Spec.divP1
  exact Finset.sum_congr rfl fun β _ => ((p4_16_1.1 κ d T F hT).2.1 x β c β).deriv

end Int21

theorem p6_21_3 : CFDLean.JST1.Spec.P6_21_3 := by
  intro ι C κ _ _ _ _ d M F i hV hC
  rw [p4_16_1.2 ι C κ d M F i hV hC]
  funext c
  refine Finset.sum_congr rfl fun T _ => ?_
  have hT := hV.2 T
  have hint : ∫ x in Spec.hullT (M.simplex T), Spec.hatOn M i T x =
      ∑ a, if M.vert T a = i then M.m T else 0 := by
    unfold Spec.hatOn
    rw [integral_finsetSum _ (fun a _ => ?_)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : M.vert T a = i
      · simp only [h, ite_true]; exact (p6_21_2 d _ hT a).2
      · simp [h]
    · by_cases h : M.vert T a = i
      · simp only [h, ite_true]; exact (p6_21_2 d _ hT a).1
      · simp only [h, ite_false]; exact integrable_zero _ _ _
  simp_rw [divP1_eq _ hT]
  rw [integral_mul_const, hint, Finset.sum_mul, Finset.mul_sum Finset.univ _ (M.ω T)]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> ring

end CFDLean.JST1.Proofs

