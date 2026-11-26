import CFDLean.Papers.JST1.Spec.Item16
import CFDLean.Papers.JST1.Proofs.Item6
import CFDLean.Papers.JST1.Proofs.Item7

/-! Proofs of item 16 (P4): `prop:consistency`(b), (c). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology Asymptotics Set
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Cons16

/-! ### The P1 interpolant -/

variable {d : ℕ}

theorem bary_vert (T : Simplex d) (hT : T.Nondeg) (a b : Fin (d + 1)) :
    Spec.bary T b (T.x a) = if b = a then 1 else 0 := by
  unfold Spec.bary
  rw [(Simplex.calculus d T hT).2.1 b a 0]
  split_ifs <;> norm_num

theorem bary_line (T : Simplex d) (b : Fin (d + 1)) (x : Vec d) (β : Fin d) (s : ℝ) :
    Spec.bary T b (x + s • Pi.single β 1) = Spec.bary T b x + s * T.grad b β := by
  unfold Spec.bary
  simp only [Num.dot, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp only [mul_add, add_sub_right_comm, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem bary_sum (T : Simplex d) (hT : T.Nondeg) (x : Vec d) : ∑ b, Spec.bary T b x = 1 := by
  unfold Spec.bary
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (0 : Fin (d + 1)) (fun _ => (1 : ℝ))]
  simp only [Finset.mem_univ, ite_true]
  have : ∑ b, Num.dot (T.grad b) (x - T.x 0) = Num.dot (∑ b, T.grad b) (x - T.x 0) := by
    simp only [Num.dot, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [this, (Simplex.calculus d T hT).1]
  simp [Num.dot]

theorem bary_affine (T : Simplex d) (hT : T.Nondeg) (x : Vec d) : ∑ b, Spec.bary T b x • T.x b = x := by
  obtain ⟨hs, -, hI, -, -⟩ := Simplex.calculus d T hT
  funext α
  simp only [Spec.bary, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hIα : ∀ β, ∑ b, T.grad b β * T.x b α = if β = α then 1 else 0 := by
    intro β
    have := congrFun (congrFun hI β) α
    simpa [Matrix.sum_apply, outer, Matrix.one_apply] using this
  have h0 : ∀ β, ∑ b, T.grad b β = 0 := by
    intro β
    have := congrFun hs β
    simpa [Finset.sum_apply] using this
  have : ∑ b, Num.dot (T.grad b) (x - T.x 0) * T.x b α = x α - T.x 0 α := by
    simp only [Num.dot, Finset.sum_mul, Pi.sub_apply]
    rw [Finset.sum_comm]
    have e : ∀ β, ∑ b, T.grad b β * (x β - T.x 0 β) * T.x b α =
        (x β - T.x 0 β) * (if β = α then 1 else 0) := by
      intro β
      rw [← hIα β, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.sum_congr rfl fun β _ => e β]
    simp
  rw [this]
  ring

end Cons16

open Cons16

theorem p4_16_1 : CFDLean.JST1.Spec.P4_16_1 := by
  refine ⟨fun κ _ d T F hT => ⟨fun a => ?_, fun x β c γ => ?_, fun F0 A hF x => ?_⟩, ?_⟩
  · simp [Spec.p1Interp, bary_vert T hT]
  · have e : (fun s : ℝ => Spec.p1Interp T F (x + s • Pi.single β 1) c γ) =
        fun s => (∑ b, Spec.bary T b x * F b c γ) + s * ∑ b, T.grad b β * F b c γ := by
      funext s
      simp only [Spec.p1Interp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, bary_line, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (∑ b, T.grad b β * F b c γ)).const_add
      (∑ b, Spec.bary T b x * F b c γ)
  · unfold Spec.p1Interp
    simp only [hF, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, bary_sum T hT, one_smul]
    congr 1
    conv_rhs => rw [← bary_affine T hT x]
    rw [map_sum]
    simp only [map_smul]
  · intro ι C κ _ _ _ _ d M F i hM hi
    obtain ⟨h1, h2⟩ := p2_6_7 ι C κ d M F i hM hi
    rw [h1, h2]
    funext c
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Matrix.mulVec, dotProduct]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun β _ => by
        simp only [WMesh.g]; ring
    · rfl

/-! ### `F^ec` minus the mean flux is `O(|Δu|²)` -/

namespace Cons16

theorem norm_prod_neg {E : Type} [NormedAddCommGroup E] (δ : E) : ‖((-δ, δ) : E × E)‖ = ‖δ‖ := by
  simp [Prod.norm_def]

end Cons16

theorem p4_16_2 : CFDLean.JST1.Spec.P4_16_2 := by
  intro E Fs _ _ _ _ Fec F Ω u0 hΩ hu0 hC hsym hdiag
  set G : E × E → Fs := Function.uncurry Fec with hG
  set H : E × E → Fs := fun p => G p - (1 / 2 : ℝ) • (G (p.1, p.1) + G (p.2, p.2)) with hH
  have hΩ2 : IsOpen (Ω ×ˢ Ω) := hΩ.prod hΩ
  have hHC : ContDiffOn ℝ 2 H (Ω ×ˢ Ω) := by
    have h1 : ContDiffOn ℝ 2 (fun p : E × E => G (p.1, p.1)) (Ω ×ˢ Ω) :=
      hC.comp (contDiff_fst.prodMk contDiff_fst).contDiffOn (fun p hp => ⟨hp.1, hp.1⟩)
    have h2 : ContDiffOn ℝ 2 (fun p : E × E => G (p.2, p.2)) (Ω ×ˢ Ω) :=
      hC.comp (contDiff_snd.prodMk contDiff_snd).contDiffOn (fun p hp => ⟨hp.2, hp.2⟩)
    exact hC.sub ((h1.add h2).const_smul _)
  have hmem : (u0, u0) ∈ Ω ×ˢ Ω := ⟨hu0, hu0⟩
  have hDC : ContDiffAt ℝ 1 (fderiv ℝ H) (u0, u0) :=
    (hHC.contDiffAt (hΩ2.mem_nhds hmem)).fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := hDC.exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht (hΩ2.mem_nhds hmem))
  -- symmetric and vanishing on the diagonal: the derivative kills `(-δ, δ)` at diagonal points
  have hdiag0 : ∀ a : E, H (a, a) = 0 := fun a => by
    simp only [hH]; rw [← two_smul ℝ (G (a, a)), smul_smul]; norm_num
  have hDiff : ∀ p ∈ Metric.ball (u0, u0) r, HasFDerivAt H (fderiv ℝ H p) p := by
    intro p hp
    exact ((hHC.contDiffAt (hΩ2.mem_nhds (hball hp).2)).differentiableAt (by norm_num)).hasFDerivAt
  have hkill : ∀ m : E, (m, m) ∈ Metric.ball (u0, u0) r → ∀ δ : E, fderiv ℝ H (m, m) (-δ, δ) = 0 := by
    intro m hm δ
    have hD := hDiff _ hm
    -- symmetry: `H ∘ swap = H` near `(m, m)`
    have hsw : fderiv ℝ H (m, m) (δ, -δ) = fderiv ℝ H (m, m) (-δ, δ) := by
      have hmΩ : (m, m) ∈ Ω ×ˢ Ω := (hball hm).2
      have hl1 : HasDerivAt (fun s : ℝ => ((m - s • δ, m + s • δ) : E × E)) (-δ, δ) 0 := by
        have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_sub m
        have h2 := ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add m
        simpa using h1.prodMk h2
      have hl2 : HasDerivAt (fun s : ℝ => ((m + s • δ, m - s • δ) : E × E)) (δ, -δ) 0 := by
        have h1 := ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add m
        have h2 := ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_sub m
        simpa using h1.prodMk h2
      have hD0 : HasFDerivAt H (fderiv ℝ H (m, m)) (m - (0 : ℝ) • δ, m + (0 : ℝ) • δ) := by simpa using hD
      have hD0' : HasFDerivAt H (fderiv ℝ H (m, m)) (m + (0 : ℝ) • δ, m - (0 : ℝ) • δ) := by simpa using hD
      have k1 := hD0.comp_hasDerivAt (0 : ℝ) hl1
      have k2 := hD0'.comp_hasDerivAt (0 : ℝ) hl2
      have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ((m - s • δ, m + s • δ) : E × E) ∈ Ω ×ˢ Ω := by
        have hc : ContinuousAt (fun s : ℝ => ((m - s • δ, m + s • δ) : E × E)) 0 := hl1.continuousAt
        have := hc.preimage_mem_nhds (by simpa using hΩ2.mem_nhds hmΩ)
        exact this
      have heq : (H ∘ fun s : ℝ => ((m + s • δ, m - s • δ) : E × E)) =ᶠ[𝓝 0]
          (H ∘ fun s : ℝ => ((m - s • δ, m + s • δ) : E × E)) := by
        filter_upwards [hev] with s hs
        show Fec (m + s • δ) (m - s • δ) - (1 / 2 : ℝ) • (Fec (m + s • δ) (m + s • δ) + Fec (m - s • δ) (m - s • δ)) =
          Fec (m - s • δ) (m + s • δ) - (1 / 2 : ℝ) • (Fec (m - s • δ) (m - s • δ) + Fec (m + s • δ) (m + s • δ))
        rw [hsym _ hs.2 _ hs.1, add_comm (Fec (m + s • δ) (m + s • δ))]
      exact k2.unique (k1.congr_of_eventuallyEq heq)
    have hsum : fderiv ℝ H (m, m) (δ, -δ) + fderiv ℝ H (m, m) (-δ, δ) = 0 := by
      rw [← map_add, Prod.mk_add_mk, add_neg_cancel, neg_add_cancel]; exact (fderiv ℝ H (m, m)).map_zero
    rw [hsw, ← two_smul ℝ] at hsum
    exact (smul_eq_zero.1 hsum).resolve_left two_ne_zero
  -- the bound on a smaller ball
  have hbound : ∀ a b : E, ((a, b) : E × E) ∈ Metric.ball (u0, u0) r →
      ‖H (a, b)‖ ≤ K * ‖(1 / 2 : ℝ) • (b - a)‖ ^ 2 := by
    intro a b hab
    set m : E := (1 / 2 : ℝ) • (a + b) with hm
    set δ : E := (1 / 2 : ℝ) • (b - a) with hδ
    have hpt : ∀ s : ℝ, ((m - s • δ, m + s • δ) : E × E) =
        (m, m) + s • ((a, b) - (m, m)) := by
      intro s
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, hm, hδ]; module
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, hm, hδ]; module
    have hmm : (m, m) ∈ Metric.ball (u0, u0) r := by
      rw [Metric.mem_ball, Prod.dist_eq] at hab ⊢
      have h1 : dist m u0 ≤ max (dist a u0) (dist b u0) := by
        rw [hm, dist_eq_norm, dist_eq_norm, dist_eq_norm]
        calc ‖(1 / 2 : ℝ) • (a + b) - u0‖ = ‖(1 / 2 : ℝ) • (a - u0) + (1 / 2 : ℝ) • (b - u0)‖ := by
              congr 1; module
          _ ≤ ‖(1 / 2 : ℝ) • (a - u0)‖ + ‖(1 / 2 : ℝ) • (b - u0)‖ := norm_add_le _ _
          _ = (1 / 2) * ‖a - u0‖ + (1 / 2) * ‖b - u0‖ := by
              rw [norm_smul, norm_smul]; norm_num
          _ ≤ max ‖a - u0‖ ‖b - u0‖ := by
              have := le_max_left ‖a - u0‖ ‖b - u0‖
              have := le_max_right ‖a - u0‖ ‖b - u0‖
              linarith
      simpa using lt_of_le_of_lt h1 hab
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1, ((m - s • δ, m + s • δ) : E × E) ∈ Metric.ball (u0, u0) r := by
      intro s hs
      rw [hpt]
      have := (convex_ball (u0, u0) r).add_smul_sub_mem hmm hab hs
      exact this
    set φ : ℝ → Fs := fun s => H (m - s • δ, m + s • δ) with hφ
    have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ (fderiv ℝ H (m - s • δ, m + s • δ) (-δ, δ))
        (Icc 0 1) s := by
      intro s hs
      have hl : HasDerivAt (fun s : ℝ => ((m - s • δ, m + s • δ) : E × E)) (-δ, δ) s := by
        have h1 := ((hasDerivAt_id s).smul_const δ).const_sub m
        have h2 := ((hasDerivAt_id s).smul_const δ).const_add m
        simpa using h1.prodMk h2
      exact ((hDiff _ (hseg s hs)).comp_hasDerivAt s hl).hasDerivWithinAt
    have hb : ∀ s ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ H (m - s • δ, m + s • δ) (-δ, δ)‖ ≤ K * ‖δ‖ ^ 2 := by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
      have h0 : ((m - (0 : ℝ) • δ, m + (0 : ℝ) • δ) : E × E) = (m, m) := by simp
      have hrw : fderiv ℝ H (m - s • δ, m + s • δ) (-δ, δ) =
          (fderiv ℝ H (m - s • δ, m + s • δ) - fderiv ℝ H (m, m)) (-δ, δ) := by
        simp [hkill m hmm δ]
      rw [hrw]
      calc _ ≤ ‖fderiv ℝ H (m - s • δ, m + s • δ) - fderiv ℝ H (m, m)‖ * ‖((-δ, δ) : E × E)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (K * dist ((m - s • δ, m + s • δ) : E × E) (m, m)) * ‖δ‖ := by
            rw [Cons16.norm_prod_neg, ← dist_eq_norm]
            exact mul_le_mul_of_nonneg_right
              (hK.dist_le_mul _ (hball (hseg s hs')).1 _ (hball hmm).1) (norm_nonneg _)
        _ ≤ (K * ‖δ‖) * ‖δ‖ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ K.2) (norm_nonneg _)
            rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
            simp only [sub_sub_cancel_left, add_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg hs'.1, max_self]
            exact mul_le_of_le_one_left (norm_nonneg _) hs'.2
        _ = K * ‖δ‖ ^ 2 := by ring
    have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hb 1 (right_mem_Icc.2 zero_le_one)
    have e1 : φ 1 = H (a, b) := by
      simp only [hφ, one_smul, hm, hδ]
      congr 1
      ext <;> simp <;> module
    have e0 : φ 0 = 0 := by simp [hφ, hdiag0]
    rw [e1, e0, sub_zero, sub_zero, mul_one] at this
    exact this
  refine IsBigO.of_bound (K / 4) ?_
  filter_upwards [Metric.ball_mem_nhds (u0, u0) hr, (hΩ2.mem_nhds hmem)] with p hp hpΩ
  have hp' : ((p.1, p.2) : E × E) ∈ Metric.ball (u0, u0) r := hp
  have hhp : Fec p.1 p.2 - (1 / 2 : ℝ) • (F p.1 + F p.2) = H (p.1, p.2) := by
    simp only [hH, hG, Function.uncurry_apply_pair, hdiag p.1 hpΩ.1, hdiag p.2 hpΩ.2]
  rw [hhp]
  refine (hbound p.1 p.2 hp').trans (le_of_eq ?_)
  rw [norm_smul, norm_pow, norm_norm, mul_pow]
  norm_num
  ring

/-! ### The weak effect of the scalar dissipation -/

namespace Cons16

variable {κ : Type} [Fintype κ]

/-- The state vector as a point of the Euclidean space. -/
def eu (x : κ → ℝ) : EuclideanSpace ℝ κ := WithLp.toLp 2 x

theorem snorm_eq (x : κ → ℝ) : Spec.snorm x = ‖eu x‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold Spec.snorm pairF eu
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, sq]

theorem pairF_le (x y : κ → ℝ) : |pairF x y| ≤ Spec.snorm x * Spec.snorm y := by
  have : pairF x y = inner ℝ (eu x) (eu y) := by
    rw [PiLp.inner_apply]
    unfold pairF eu
    exact Finset.sum_congr rfl fun c _ => by rw [PiLp.toLp_apply, PiLp.toLp_apply, RCLike.inner_apply']; simp
  rw [this, snorm_eq, snorm_eq]
  exact abs_real_inner_le_norm _ _

theorem snorm_nonneg (x : κ → ℝ) : 0 ≤ Spec.snorm x := Real.sqrt_nonneg _

theorem snorm_smul (c : ℝ) (x : κ → ℝ) : Spec.snorm (c • x) = |c| * Spec.snorm x := by
  rw [snorm_eq, snorm_eq, eu, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]; rfl

theorem snorm_sub_le (x y : κ → ℝ) : Spec.snorm (x - y) ≤ Spec.snorm x + Spec.snorm y := by
  rw [snorm_eq, snorm_eq, snorm_eq, eu, WithLp.toLp_sub]; exact norm_sub_le _ _

theorem snorm_sub_comm (x y : κ → ℝ) : Spec.snorm (x - y) = Spec.snorm (y - x) := by
  rw [snorm_eq, snorm_eq, eu, eu, WithLp.toLp_sub, WithLp.toLp_sub]; exact norm_sub_rev _ _

theorem snorm_sum_le {ι : Type} (s : Finset ι) (f : ι → κ → ℝ) :
    Spec.snorm (∑ k ∈ s, f k) ≤ ∑ k ∈ s, Spec.snorm (f k) := by
  simp only [snorm_eq, eu, WithLp.toLp_sum]
  exact norm_sum_le _ _

theorem sensor_le {ι : Type} (E : ι → Finset ι) (p : ι → ℝ) (hp : ∀ i, 0 < p i) (i : ι) (hE : (E i).Nonempty) :
    0 ≤ Spec.sensor E p i ∧ Spec.sensor E p i ≤ 1 := by
  have hden : 0 < ∑ k ∈ E i, (p k + p i) := Finset.sum_pos (fun k _ => by linarith [hp k, hp i]) hE
  refine ⟨div_nonneg (abs_nonneg _) hden.le, (div_le_one hden).2 ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_le]; constructor <;> linarith [hp k, hp i]

theorem tau_le {ι : Type} (E : ι → Finset ι) (i k : ι) (hi : 1 ≤ (E i).card) (hk : 1 ≤ (E k).card) :
    0 ≤ Spec.tauC E i k ∧ Spec.tauC E i k ≤ 6 := by
  unfold Spec.tauC
  have ha : (1 : ℝ) ≤ (E i).card := by exact_mod_cast hi
  have hb : (1 : ℝ) ≤ (E k).card := by exact_mod_cast hk
  have hab : 0 < ((E i).card : ℝ) * (E k).card := by positivity
  refine ⟨by positivity, (div_le_iff₀ hab).2 ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem lamHat_nonneg {d : ℕ} (vb : Vec d) (cb : ℝ) (hcb : 0 ≤ cb) (e y : Vec d) : 0 ≤ lamHat vb cb e y :=
  add_nonneg (abs_nonneg _) (mul_nonneg hcb (Real.sqrt_nonneg _))

theorem lamHat_zero {d : ℕ} (vb : Vec d) (cb : ℝ) (e : Vec d) : lamHat vb cb e 0 = 0 := by
  have : WMesh.nuOf (0 : Vec d) e = 0 := by simp [WMesh.nuOf, Num.dot]
  simp [lamHat, this, Num.dot, len]

end Cons16

theorem p4_16_3 : CFDLean.JST1.Spec.P4_16_3 := by
  intro ι C κ _ _ _ _ d M vb cb Φ E Nst p ut φ κ2 κ4 σmax Φmax h Gφ Gu nE hM hk2 hk4 hh hGφ hGu hσ hΦ hp hE
    hN hsm
  dsimp only
  have hEn : ∀ i, (E i).Nonempty := fun i => Finset.card_pos.1 (by have := (hE i).1; omega)
  have heps : ∀ i k, 0 ≤ Spec.eps2C κ2 E p i k ∧ Spec.eps2C κ2 E p i k ≤ 6 * κ2 ∧
      0 ≤ Spec.eps4C κ2 κ4 E p i k ∧ Spec.eps4C κ2 κ4 E p i k ≤ 9 * κ4 := by
    intro i k
    obtain ⟨si0, si1⟩ := Cons16.sensor_le E p hp i (hEn i)
    obtain ⟨sk0, sk1⟩ := Cons16.sensor_le E p hp k (hEn k)
    obtain ⟨t0, t1⟩ := Cons16.tau_le E i k (hE i).1 (hE k).1
    have hs0 : 0 ≤ (1 / 2) * (Spec.sensor E p i + Spec.sensor E p k) := by positivity
    have hs1 : (1 / 2) * (Spec.sensor E p i + Spec.sensor E p k) ≤ 1 := by linarith
    have e20 : 0 ≤ Spec.eps2C κ2 E p i k := by unfold Spec.eps2C; positivity
    have e21 : Spec.eps2C κ2 E p i k ≤ 6 * κ2 := by
      unfold Spec.eps2C
      have := mul_le_mul hs1 t1 t0 zero_le_one
      nlinarith [mul_nonneg hk2 hs0]
    refine ⟨e20, e21, by unfold Spec.eps4C; positivity, ?_⟩
    unfold Spec.eps4C
    have hm : max 0 (κ4 - Spec.eps2C κ2 E p i k) ≤ κ4 := max_le hk4 (by linarith)
    have hm0 : 0 ≤ max 0 (κ4 - Spec.eps2C κ2 E p i k) := le_max_left _ _
    have ht2 : Spec.tauC E i k ^ 2 ≤ 36 := by nlinarith
    have := mul_le_mul hm ht2 (sq_nonneg _) hk4
    linarith
  refine ⟨fun i k => ⟨(heps i k).2.1, (heps i k).2.2.2⟩, ?_⟩
  set C1 := 6 * κ2 + 18 * (nE : ℝ) * κ4 with hC1
  set lh : ι → ι → ℝ := fun i k => lamHat (vb i k) (cb i k) (M.e i k) (M.n i k) with hlh
  have hlh0 : ∀ i k, 0 ≤ lh i k := fun i k => Cons16.lamHat_nonneg _ _ (hσ i k).1 _ _
  have hL : ∀ i, Spec.snorm (∑ k ∈ Nst i, (ut k - ut i)) ≤ nE * (Gu * h) := by
    intro i
    refine (Cons16.snorm_sum_le _ _).trans ?_
    have hcard : ((Nst i).card : ℝ) ≤ nE := by exact_mod_cast (Finset.card_le_card (hN i)).trans (hE i).2
    calc ∑ k ∈ Nst i, Spec.snorm (ut k - ut i) ≤ ∑ _k ∈ Nst i, Gu * h := Finset.sum_le_sum fun k hk => by
          obtain ⟨hlen, -, hu⟩ := hsm i k (Or.inr hk)
          exact hu.trans (mul_le_mul_of_nonneg_left hlen hGu)
      _ = (Nst i).card * (Gu * h) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ nE * (Gu * h) := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hterm : ∀ i k, |pairF (φ k - φ i) ((Φ i k * lh i k) • (Spec.eps2C κ2 E p i k • (ut i - ut k) -
      Spec.eps4C κ2 κ4 E p i k • ((∑ j ∈ Nst i, (ut j - ut i)) - ∑ j ∈ Nst k, (ut j - ut k))))| ≤
      (Gφ * Gu * h * C1 * Φmax) * (lh i k * len (M.e i k)) := by
    intro i k
    by_cases hn : M.n i k = 0
    · have : lh i k = 0 := by simp only [hlh, hn, Cons16.lamHat_zero]
      rw [this]; simp [pairF]
    obtain ⟨hlen, hφ, hu⟩ := hsm i k (Or.inl hn)
    obtain ⟨e20, e21, e40, e41⟩ := heps i k
    have hlam : 0 ≤ Φ i k * lh i k := mul_nonneg (hΦ i k).1 (hlh0 i k)
    have hd : Spec.snorm ((Φ i k * lh i k) • (Spec.eps2C κ2 E p i k • (ut i - ut k) -
        Spec.eps4C κ2 κ4 E p i k • ((∑ j ∈ Nst i, (ut j - ut i)) - ∑ j ∈ Nst k, (ut j - ut k)))) ≤
        (Φ i k * lh i k) * (Gu * h * C1) := by
      rw [Cons16.snorm_smul, abs_of_nonneg hlam]
      refine mul_le_mul_of_nonneg_left ?_ hlam
      refine (Cons16.snorm_sub_le _ _).trans ?_
      rw [Cons16.snorm_smul, Cons16.snorm_smul, abs_of_nonneg e20, abs_of_nonneg e40]
      have h1 : Spec.snorm (ut i - ut k) ≤ Gu * h := by
        rw [Cons16.snorm_sub_comm]; exact hu.trans (mul_le_mul_of_nonneg_left hlen hGu)
      have h2 : Spec.snorm ((∑ j ∈ Nst i, (ut j - ut i)) - ∑ j ∈ Nst k, (ut j - ut k)) ≤ 2 * (nE * (Gu * h)) :=
        (Cons16.snorm_sub_le _ _).trans (by linarith [hL i, hL k])
      have hGh : 0 ≤ Gu * h := mul_nonneg hGu hh
      calc Spec.eps2C κ2 E p i k * Spec.snorm (ut i - ut k) + Spec.eps4C κ2 κ4 E p i k *
            Spec.snorm ((∑ j ∈ Nst i, (ut j - ut i)) - ∑ j ∈ Nst k, (ut j - ut k))
          ≤ (6 * κ2) * (Gu * h) + (9 * κ4) * (2 * (nE * (Gu * h))) :=
            add_le_add (mul_le_mul e21 h1 (Cons16.snorm_nonneg _) (by linarith))
              (mul_le_mul e41 h2 (Cons16.snorm_nonneg _) (by linarith))
        _ = Gu * h * C1 := by rw [hC1]; ring
    have hle0 : 0 ≤ len (M.e i k) := Real.sqrt_nonneg _
    calc _ ≤ Spec.snorm (φ k - φ i) * Spec.snorm _ := Cons16.pairF_le _ _
      _ ≤ (Gφ * len (M.e i k)) * ((Φ i k * lh i k) * (Gu * h * C1)) :=
          mul_le_mul hφ hd (Cons16.snorm_nonneg _) (mul_nonneg hGφ hle0)
      _ ≤ (Gφ * len (M.e i k)) * ((Φmax * lh i k) * (Gu * h * C1)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hΦ i k).2 (hlh0 i k)) ?_) (mul_nonneg hGφ hle0)
          have : 0 ≤ C1 := by rw [hC1]; positivity
          positivity
      _ = _ := by ring
  have h74 := p2_7_4 ι C d M vb cb σmax hM hσ
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
  · have hC : IsEmpty C := ⟨fun T => hι.false (M.vert T 0)⟩
    simp [WMesh.volΩ]
  have hΦm : 0 ≤ Φmax := (hΦ i0 i0).1.trans (hΦ i0 i0).2
  have hC10 : 0 ≤ C1 := by rw [hC1]; positivity
  have hK : 0 ≤ Gφ * Gu * h * C1 * Φmax := by positivity
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hS := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm i k))
  have h2 : ∑ i, ∑ k, (Gφ * Gu * h * C1 * Φmax) * (lh i k * len (M.e i k)) ≤
      (Gφ * Gu * h * C1 * Φmax) * (2 * d * σmax * M.volΩ) := by
    simp only [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h74 hK
  calc (1 / 2) * |_| ≤ (1 / 2) * ((Gφ * Gu * h * C1 * Φmax) * (2 * d * σmax * M.volΩ)) :=
        mul_le_mul_of_nonneg_left (hS.trans h2) (by norm_num)
    _ = _ := by rw [hC1]; ring

/-! ### The face vector: lower bound and an unbounded family -/

namespace Cons16

theorem mu_zero_c {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C] {d : ℕ} (M : WMesh ι C d)
    (hM : M.Valid) {i k : ι} (h : M.mu i k = 0) : M.c i k = 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun T _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => by
      split_ifs
      · exact CFDLean.Num.Internal.DissGeom.wm_nonneg M hM T
      · exact le_rfl)).1 h
  unfold WMesh.c WMesh.cW
  refine Finset.sum_eq_zero fun T hT => ?_
  have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact CFDLean.Num.Internal.DissGeom.wm_nonneg M hM T
    · exact le_rfl)).1 (hz T hT)
  refine Finset.sum_eq_zero fun a ha => ?_
  have hz3 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by
    split_ifs
    · exact CFDLean.Num.Internal.DissGeom.wm_nonneg M hM T
    · exact le_rfl)).1 (hz2 a ha)
  refine Finset.sum_eq_zero fun b hb => ?_
  have := hz3 b hb
  split_ifs at this ⊢ with hc
  · rw [this, zero_smul]
  · rfl

theorem term_nonneg {d : ℕ} (y e : Vec d) : 0 ≤ Num.dot y e * Spec.secOf y e := by
  unfold Spec.secOf
  rcases eq_or_ne (Num.dot y e) 0 with h | h
  · rw [h, zero_mul]
  · rw [mul_div_cancel₀ _ h]; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem abs_le_len2 (v : Vec 2) (j : Fin 2) : |v j| ≤ len v := by
  unfold len
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  simp only [Num.dot, Fin.sum_univ_two]
  fin_cases j <;> simp <;> nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]

end Cons16

theorem p4_16_4 : CFDLean.JST1.Spec.P4_16_4 := by
  refine ⟨fun ι C _ _ _ d M vb cb hM hcb => ?_, fun K => ?_⟩
  · have hpair : ∀ i k, i ≠ k → M.n i k ≠ 0 → 0 < Num.dot (M.n i k) (M.e i k) := by
      intro i k hik hn
      rw [CFDLean.Num.Internal.DissGeom.n_dot_e M hM i k hik]
      rcases (CFDLean.Num.Internal.DissGeom.mu_nonneg M hM i k).lt_or_eq with h | h
      · linarith
      · exfalso; apply hn
        unfold WMesh.n
        rw [Cons16.mu_zero_c M hM h.symm, Cons16.mu_zero_c M hM
          ((CFDLean.Num.Internal.DissGeom.mu_symm M i k).trans h.symm), sub_zero]
    have hpw : ∀ i k, cb i k * Num.dot (M.n i k) (M.e i k) * Spec.secOf (M.n i k) (M.e i k) ≤
        radFull (vb i k) (cb i k) (M.n i k) * len (M.e i k) := by
      intro i k
      have hR : 0 ≤ radFull (vb i k) (cb i k) (M.n i k) * len (M.e i k) :=
        mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (hcb i k) (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
      unfold Spec.secOf
      rcases eq_or_ne (Num.dot (M.n i k) (M.e i k)) 0 with h | h
      · rw [h, mul_zero, zero_mul]; exact hR
      · rw [mul_assoc, mul_div_cancel₀ _ h, ← mul_assoc]
        unfold radFull
        exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (Num.dot (vb i k) (M.n i k))])
          (Real.sqrt_nonneg _)
    refine ⟨fun i k hik hn => ⟨hpair i k hik hn, ?_⟩, hpw,
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hpw i k⟩
    have h0 := hpair i k hik hn
    unfold Spec.secOf
    rw [le_div_iff₀ h0, one_mul]
    exact CFDLean.Num.Internal.DissGeom.dot_le_len _ _
  · -- the stretched triangle `(0,0), (L,0), (L/2, 2/L)`, `|T| = 1`
    set L : ℝ := 1 + 8 * |K| with hL
    have hL0 : 0 < L := by positivity
    let pos : Fin 3 → Vec 2 := ![![0, 0], ![L, 0], ![L / 2, 2 / L]]
    let M : WMesh (Fin 3) Unit 2 := ⟨pos, fun _ => Function.Embedding.refl _, fun _ => 1⟩
    let G : Fin 3 → Vec 2 := ![![-1 / L, -L / 4], ![1 / L, -L / 4], ![0, L / 2]]
    have hx : ∀ a, (M.simplex ()).x a = pos a := fun a => rfl
    have hdual : ∀ a j, Num.dot (G a) ((M.simplex ()).x j - (M.simplex ()).x 0) =
        (if a = j then 1 else 0) - (if a = 0 then 1 else 0) := by
      intro a j
      simp only [hx]
      fin_cases a <;> fin_cases j <;> simp [G, pos, Num.dot, Fin.sum_univ_two] <;> field_simp <;> ring
    obtain ⟨hnd, hgrad⟩ := CFDLean.Num.Internal.Geo3.grads_of_dual (M.simplex ()) G hdual
    have hvol : M.vol () = 1 := by
      show |(M.simplex ()).edgeMat.det| / (Nat.factorial 2) = 1
      rw [Matrix.det_fin_two]
      simp only [Simplex.edgeMat, hx]
      simp [pos]
      rw [abs_of_pos hL0, abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
      field_simp
    have hM : M.Valid := ⟨fun _ => zero_le_one, fun T => by cases T; exact hnd⟩
    have hc : ∀ i k, M.c i k = (1 / 3 : ℝ) • G k := by
      intro i k
      unfold WMesh.c WMesh.cW
      simp only [Fintype.univ_unit, Finset.sum_singleton]
      have hm : M.ω () * M.m () = 1 / 3 := by
        show 1 * (M.vol () / ((2 : ℕ) + 1 : ℝ)) = 1 / 3
        rw [hvol]; norm_num
      have : ∀ a b : Fin 3, (if M.vert () a = i ∧ M.vert () b = k then (M.ω () * M.m ()) • M.g () b else 0) =
          if a = i then (if b = k then (1 / 3 : ℝ) • G b else 0) else 0 := by
        intro a b
        rw [hm, WMesh.g, hgrad]
        show (if a = i ∧ b = k then _ else _) = _
        by_cases ha : a = i <;> by_cases hb : b = k <;> simp [ha, hb]
      simp only [this]
      simp
    have hn02 : M.n 0 2 = ![1 / (3 * L), L / 4] := by
      unfold WMesh.n
      rw [hc, hc]
      funext j
      fin_cases j
      · simp [G]; field_simp
      · simp [G]; field_simp; ring
    have hn20 : M.n 2 0 = -![1 / (3 * L), L / 4] := by
      unfold WMesh.n
      rw [hc, hc]
      funext j
      fin_cases j
      · simp [G]; field_simp
      · simp [G]; field_simp; ring
    have he02 : M.e 0 2 = ![L / 2, 2 / L] := by
      unfold WMesh.e; funext j; fin_cases j <;> simp [M, pos]
    have he20 : M.e 2 0 = -![L / 2, 2 / L] := by
      unfold WMesh.e; funext j; fin_cases j <;> simp [M, pos]
    have hdot : Num.dot (![1 / (3 * L), L / 4] : Vec 2) ![L / 2, 2 / L] ≠ 0 := by
      simp [Num.dot, Fin.sum_univ_two]; field_simp; norm_num
    have hlenN : L / 4 ≤ len (![1 / (3 * L), L / 4] : Vec 2) := by
      have := Cons16.abs_le_len2 (![1 / (3 * L), L / 4] : Vec 2) 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
      rw [abs_of_pos (by positivity)] at this; exact this
    have hlenE : L / 2 ≤ len (![L / 2, 2 / L] : Vec 2) := by
      have := Cons16.abs_le_len2 (![L / 2, 2 / L] : Vec 2) 0
      simp only [Matrix.cons_val_zero] at this
      rw [abs_of_pos (by positivity)] at this; exact this
    have hlen_neg : ∀ v : Vec 2, len (-v) = len v := by
      intro v; simp [len, Num.dot]
    have hdot_neg : ∀ v w : Vec 2, Num.dot (-v) (-w) = Num.dot v w := by
      intro v w; simp [Num.dot]
    have hT : ∀ v w : Vec 2, Num.dot v w ≠ 0 → L / 4 ≤ len v → L / 2 ≤ len w →
        L ^ 2 / 8 ≤ Num.dot v w * Spec.secOf v w := by
      intro v w hvw hv hw
      unfold Spec.secOf
      rw [mul_div_cancel₀ _ hvw]
      nlinarith [mul_le_mul hv hw (by positivity) (le_trans (by positivity) hv)]
    have t02 := hT (M.n 0 2) (M.e 0 2) (by rw [hn02, he02]; exact hdot) (by rw [hn02]; exact hlenN) (by rw [he02]; exact hlenE)
    have t20 := hT (M.n 2 0) (M.e 2 0) (by rw [hn20, he20, hdot_neg]; exact hdot) (by rw [hn20, hlen_neg]; exact hlenN)
      (by rw [he20, hlen_neg]; exact hlenE)
    refine ⟨M, hM, ?_, ?_⟩
    · simp [WMesh.volΩ, hvol, M]
    · have hall : ∀ i k : Fin 3, 0 ≤ Num.dot (M.n i k) (M.e i k) * Spec.secOf (M.n i k) (M.e i k) :=
        fun i k => Cons16.term_nonneg _ _
      have h1 : Num.dot (M.n 0 2) (M.e 0 2) * Spec.secOf (M.n 0 2) (M.e 0 2) ≤
          ∑ k, Num.dot (M.n 0 k) (M.e 0 k) * Spec.secOf (M.n 0 k) (M.e 0 k) :=
        Finset.single_le_sum (fun k _ => hall 0 k) (Finset.mem_univ 2)
      have h2 : Num.dot (M.n 2 0) (M.e 2 0) * Spec.secOf (M.n 2 0) (M.e 2 0) ≤
          ∑ k, Num.dot (M.n 2 k) (M.e 2 k) * Spec.secOf (M.n 2 k) (M.e 2 k) :=
        Finset.single_le_sum (fun k _ => hall 2 k) (Finset.mem_univ 0)
      have h3 : (∑ k, Num.dot (M.n 0 k) (M.e 0 k) * Spec.secOf (M.n 0 k) (M.e 0 k)) +
          (∑ k, Num.dot (M.n 2 k) (M.e 2 k) * Spec.secOf (M.n 2 k) (M.e 2 k)) ≤
          ∑ i, ∑ k, Num.dot (M.n i k) (M.e i k) * Spec.secOf (M.n i k) (M.e i k) := by
        conv_rhs => rw [Fin.sum_univ_three]
        linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hall 1 k]
      have hK : K ≤ L ^ 2 / 8 := by
        rw [hL]; nlinarith [abs_nonneg K, le_abs_self K]
      linarith

end CFDLean.JST1.Proofs
