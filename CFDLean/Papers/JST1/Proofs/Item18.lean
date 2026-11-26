import CFDLean.Papers.JST1.Spec.Item18
import CFDLean.Papers.JST1.Proofs.Item10

/-! Proofs of item 18 (P4): the Hessian form of `lem:sstentropy`. The second derivative along a line is the
quadratic form `q = ρ/(γ-1) (γa² - 2ab + b²) + (ρ²/p)|δv|²` of the proof of `lem:eps2`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology
namespace CFDLean.JST1.Proofs
namespace Hess18

variable {d : ℕ}

/-- The quadratic form `δw·δu` of the Euler entropy at `u` in direction `δ`. -/
def qE (g : Gas) (u δ : State d) : ℝ :=
  rho u / (g.γ - 1) * thermoQ g.γ (δ .mass / rho u)
      ((g.γ - 1) * (δ .energy - Num.dot (vel u) (mom δ) + Num.dot (vel u) (vel u) * δ .mass / 2) /
        pressure g u) +
    rho u ^ 2 / pressure g u * Num.dot ((1 / rho u) • (mom δ - δ .mass • vel u))
      ((1 / rho u) • (mom δ - δ .mass • vel u))

theorem dot_self_nonneg' (v : Vec d) : 0 ≤ Num.dot v v :=
  Finset.sum_nonneg fun α _ => mul_self_nonneg (v α)

theorem dot_self_eq_zero' {v : Vec d} (h : Num.dot v v = 0) : v = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => mul_self_nonneg (v α))).1 h
  funext α
  exact mul_self_eq_zero.1 (this α (Finset.mem_univ α))

theorem qE_nonneg (g : Gas) {u : State d} (hu : Admissible g u) (δ : State d) : 0 ≤ qE g u δ := by
  have hg : 0 < g.γ - 1 := by linarith [g.one_lt_γ]
  unfold qE
  have := thermoQ_nonneg g.one_lt_γ (δ .mass / rho u)
    ((g.γ - 1) * (δ .energy - Num.dot (vel u) (mom δ) + Num.dot (vel u) (vel u) * δ .mass / 2) / pressure g u)
  have h1 : 0 ≤ rho u / (g.γ - 1) := div_nonneg hu.1.le hg.le
  have h2 : 0 ≤ rho u ^ 2 / pressure g u := div_nonneg (sq_nonneg _) hu.2.le
  exact add_nonneg (mul_nonneg h1 this) (mul_nonneg h2 (dot_self_nonneg' _))

theorem qE_eq_zero (g : Gas) {u : State d} (hu : Admissible g u) {δ : State d} (h : qE g u δ = 0) : δ = 0 := by
  have hg : 0 < g.γ - 1 := by linarith [g.one_lt_γ]
  have hr := hu.1
  have hp := hu.2
  unfold qE at h
  set a := δ .mass / rho u
  set b := (g.γ - 1) * (δ .energy - Num.dot (vel u) (mom δ) + Num.dot (vel u) (vel u) * δ .mass / 2) /
    pressure g u
  set dv := (1 / rho u) • (mom δ - δ .mass • vel u)
  have hT := thermoQ_nonneg g.one_lt_γ a b
  have h1 : 0 < rho u / (g.γ - 1) := div_pos hr hg
  have h2 : 0 < rho u ^ 2 / pressure g u := div_pos (by positivity) hp
  have hD := dot_self_nonneg' dv
  have hTz : thermoQ g.γ a b = 0 := by nlinarith [mul_nonneg h1.le hT, mul_nonneg h2.le hD]
  have hDz : Num.dot dv dv = 0 := by nlinarith [mul_nonneg h1.le hT, mul_nonneg h2.le hD]
  have ha : a = 0 := by
    by_contra hne
    exact (thermoQ_pos g.one_lt_γ hne b).ne' hTz
  have hb : b = 0 := by
    rw [thermoQ_eq, ha] at hTz
    nlinarith [sq_nonneg b]
  have hm0 : δ .mass = 0 := by
    have : δ .mass / rho u = 0 := ha
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h hr.ne'
  have hdv := dot_self_eq_zero' hDz
  have hmom : mom δ = 0 := by
    have : (1 / rho u) • (mom δ - δ .mass • vel u) = 0 := hdv
    rw [hm0, zero_smul, sub_zero] at this
    rcases smul_eq_zero.1 this with h | h
    · exact absurd h (by positivity)
    · exact h
  have hE : δ .energy = 0 := by
    have : b = 0 := hb
    have hd0 : Num.dot (vel u) (0 : Vec d) = 0 := by simp [Num.dot]
    simp only [b, hm0, hmom, hd0, mul_zero, zero_div, add_zero, sub_zero] at this
    rcases div_eq_zero_iff.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hg.ne'
      · exact h
    · exact absurd h hp.ne'
  funext c
  cases c with
  | mass => exact hm0
  | momentum α => exact congrFun hmom α
  | energy => exact hE

/-! ### The line derivative of `w(u + s δ) · δ` -/

theorem hasDerivAt_lin (A B : ℝ) : HasDerivAt (fun s : ℝ => A + s * B) B 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const B).const_add A

theorem hasDerivAt_quad (A B C : ℝ) : HasDerivAt (fun s : ℝ => A + 2 * s * B + s ^ 2 * C) (2 * B) 0 := by
  have h1 := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * B))
  have h2 := ((hasDerivAt_pow 2 (0 : ℝ)).mul_const C)
  have := (h1.add h2).const_add A
  convert this using 1
  · funext s; simp only [id, Pi.add_apply]; ring
  · simp

/-- The explicit line function. -/
def lineF (γ r A0 A1 A2 E dr dE : ℝ) (s : ℝ) : ℝ :=
  let R := r + s * dr
  let MM := A0 + 2 * s * A1 + s ^ 2 * A2
  let P := (γ - 1) * ((E + s * dE) - MM / (2 * R))
  ((γ - (Real.log P - γ * Real.log R)) / (γ - 1) - MM / (2 * R * P)) * dr + (A1 + s * A2) / P - R / P * dE

theorem hasDerivAt_lineF {γ r A0 A1 A2 p dr dE : ℝ} (hg : γ - 1 ≠ 0) (hr : 0 < r) (hp : 0 < p) :
    HasDerivAt (lineF γ r A0 A1 A2 (p / (γ - 1) + A0 / (2 * r)) dr dE)
      (r / (γ - 1) * thermoQ γ (dr / r) ((γ - 1) * (dE - A1 / r + A0 / r ^ 2 * dr / 2) / p) +
        r ^ 2 / p * ((A2 - 2 * dr * (A1 / r) + dr ^ 2 * (A0 / r ^ 2)) / r ^ 2)) 0 := by
  have hR := hasDerivAt_lin r dr
  have hMM := hasDerivAt_quad A0 A1 A2
  have hM1 := hasDerivAt_lin A1 A2
  have hE := hasDerivAt_lin (p / (γ - 1) + A0 / (2 * r)) dE
  have hR0 : r + 0 * dr ≠ 0 := by simp [hr.ne']
  have h2R := hR.const_mul 2
  have h2R0 : 2 * (r + 0 * dr) ≠ 0 := by simp [hr.ne']
  have hQ := hMM.div h2R h2R0
  have hP := (hE.sub hQ).const_mul (γ - 1)
  have hPv : (γ - 1) * ((p / (γ - 1) + A0 / (2 * r) + 0 * dE) -
      (A0 + 2 * 0 * A1 + 0 ^ 2 * A2) / (2 * (r + 0 * dr))) = p := by
    field_simp; ring
  have hP0 : (γ - 1) * ((p / (γ - 1) + A0 / (2 * r) + 0 * dE) -
      (A0 + 2 * 0 * A1 + 0 ^ 2 * A2) / (2 * (r + 0 * dr))) ≠ 0 := by rw [hPv]; exact hp.ne'
  have hlogP := hP.log hP0
  have hlogR := hR.log hR0
  have hw0 := ((hlogP.sub (hlogR.const_mul γ)).const_sub γ).div_const (γ - 1)
  have hRP := h2R.mul hP
  have hRP0 := mul_ne_zero h2R0 hP0
  have hK := hMM.div hRP hRP0
  have hF := (((hw0.sub hK).mul_const dr).add (hM1.div hP hP0)).sub ((hR.div hP hP0).mul_const dE)
  convert hF using 1
  · funext s
    simp only [lineF, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.mul_apply]
  · rw [show (γ - 1) * ((p / (γ - 1) + A0 / (2 * r) + 0 * dE) -
      (A0 + 2 * 0 * A1 + 0 ^ 2 * A2) / (2 * (r + 0 * dr))) = p from hPv] at *
    simp only [Pi.sub_apply, Pi.div_apply, Pi.mul_apply, zero_mul, add_zero, mul_zero,
      zero_pow two_ne_zero]
    have hp0 : p ≠ 0 := hp.ne'
    have hr0 : r ≠ 0 := hr.ne'
    unfold thermoQ
    field_simp
    ring

/-- Sums of products of momenta. -/
def sA (x y : State d) : ℝ := ∑ α, x (.momentum α) * y (.momentum α)

theorem dot_mom_line (u δ : State d) (s : ℝ) :
    Num.dot (mom (u + s • δ)) (mom (u + s • δ)) = sA u u + 2 * s * sA u δ + s ^ 2 * sA δ δ := by
  simp only [Num.dot, mom, sA, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by ring

theorem pair_line (g : Gas) (u δ : State d) (s : ℝ) (hR : rho (u + s • δ) ≠ 0) :
    pairF (entropyVars g (u + s • δ)) δ =
      lineF g.γ (rho u) (sA u u) (sA u δ) (sA δ δ) (energy u) (δ .mass) (δ .energy) s := by
  have hρ : rho (u + s • δ) = rho u + s * δ .mass := by simp [rho]
  have hE : energy (u + s • δ) = energy u + s * δ .energy := by simp [energy]
  have hm := dot_mom_line u δ s
  have hv : rho (u + s • δ) * Num.dot (vel (u + s • δ)) (vel (u + s • δ)) =
      Num.dot (mom (u + s • δ)) (mom (u + s • δ)) / rho (u + s • δ) := by
    rw [dot_mom hR]; field_simp
  have hw : ∑ α, rho (u + s • δ) * vel (u + s • δ) α / pressure g (u + s • δ) * δ (.momentum α) =
      (sA u δ + s * sA δ δ) / pressure g (u + s • δ) := by
    rw [show sA u δ + s * sA δ δ = ∑ α, (u + s • δ) (.momentum α) * δ (.momentum α) by
      simp only [sA, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring, Finset.sum_div]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [e1_mom_eq hR α]
    ring
  have hp : pressure g (u + s • δ) = (g.γ - 1) * ((energy u + s * δ .energy) -
      (sA u u + 2 * s * sA u δ + s ^ 2 * sA δ δ) / (2 * (rho u + s * δ .mass))) := by
    rw [pressure, hE, hm, hρ]
  rw [e1_pairF_channel]
  simp only [entropyVars, physEntropy]
  rw [show rho (u + s • δ) * Num.dot (vel (u + s • δ)) (vel (u + s • δ)) / (2 * pressure g (u + s • δ)) =
      (rho (u + s • δ) * Num.dot (vel (u + s • δ)) (vel (u + s • δ))) / (2 * pressure g (u + s • δ)) by ring]
  rw [hv, hw, hm, hp, hρ]
  unfold lineF
  simp only
  field_simp
  ring

theorem energy_eq (g : Gas) {u : State d} (hr : rho u ≠ 0) :
    energy u = pressure g u / (g.γ - 1) + sA u u / (2 * rho u) := by
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  have : Num.dot (mom u) (mom u) = sA u u := rfl
  rw [pressure, this]
  field_simp
  ring

/-- `d/ds [w(u + s δ) · δ]` at `s = 0` is the form `q`. -/
theorem hasDerivAt_wline (g : Gas) {u : State d} (hu : Admissible g u) (δ : State d) :
    HasDerivAt (fun s : ℝ => pairF (entropyVars g (u + s • δ)) δ) (qE g u δ) 0 := by
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  have hr := hu.1
  have hL := hasDerivAt_lineF (A0 := sA u u) (A1 := sA u δ) (A2 := sA δ δ) (dr := δ .mass) (dE := δ .energy)
    hg hr hu.2
  rw [← energy_eq g hr.ne'] at hL
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), rho (u + s • δ) ≠ 0 := by
    have hc : ContinuousAt (fun s : ℝ => rho u + s * δ .mass) 0 := by fun_prop
    have := hc.eventually_ne (by simpa using hr.ne')
    filter_upwards [this] with s hs
    simpa [rho] using hs
  refine (hL.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hev] with s hs
    exact pair_line g u δ s hs
  · have hr0 : rho u ≠ 0 := hr.ne'
    have hp0 : pressure g u ≠ 0 := hu.2.ne'
    have h1 : Num.dot (vel u) (mom δ) = sA u δ / rho u := by
      simp only [Num.dot, vel, mom, sA, Finset.sum_div]
      exact Finset.sum_congr rfl fun α _ => by ring
    have h2 : Num.dot (vel u) (vel u) = sA u u / rho u ^ 2 := by
      simp only [Num.dot, vel, mom, sA, Finset.sum_div]
      exact Finset.sum_congr rfl fun α _ => by ring
    have h3 : Num.dot ((1 / rho u) • (mom δ - δ .mass • vel u)) ((1 / rho u) • (mom δ - δ .mass • vel u)) =
        (sA δ δ - 2 * δ .mass * (sA u δ / rho u) + δ .mass ^ 2 * (sA u u / rho u ^ 2)) / rho u ^ 2 := by
      simp only [Num.dot, vel, mom, sA, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_div,
        Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      field_simp
      ring
    unfold qE
    rw [h1, h2, h3]

theorem contDiffAt_pressure (g : Gas) {u : State d} (hr : rho u ≠ 0) : ContDiffAt ℝ 2 (pressure g) u := by
  have h2 : (2 : ℝ) * u .mass ≠ 0 := mul_ne_zero two_ne_zero hr
  have : ContDiffAt ℝ 2 (fun v : State d =>
      (g.γ - 1) * (v .energy - (∑ α, v (.momentum α) * v (.momentum α)) / (2 * v .mass))) u := by
    fun_prop (disch := exact h2)
  exact this

theorem contDiffAt_entropyFun (g : Gas) {u : State d} (hu : Admissible g u) :
    ContDiffAt ℝ 2 (entropyFun g) u := by
  have hr : u .mass ≠ 0 := hu.1.ne'
  have hP := (contDiffAt_pressure g hu.1.ne').log hu.2.ne'
  have hR : ContDiffAt ℝ 2 (fun v : State d => v .mass) u := by fun_prop
  have hlR := hR.log hr
  have := ((hR.neg.mul (hP.sub (hlR.const_smul g.γ))).div_const (g.γ - 1))
  convert this using 2 with v
  simp [entropyFun, physEntropy, rho, smul_eq_mul]

theorem eventually_admissible (g : Gas) {u : State d} (hu : Admissible g u) : ∀ᶠ v in 𝓝 u, Admissible g v := by
  have h1 : ContinuousAt (fun v : State d => v .mass) u := (continuous_apply _).continuousAt
  have h2 : ContinuousAt (pressure g) u := (contDiffAt_pressure g hu.1.ne').continuousAt
  exact (continuousAt_const.eventually_lt h1 hu.1).and (continuousAt_const.eventually_lt h2 hu.2)

theorem tendsto_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (u δ : E) : Tendsto (fun s : ℝ => u + s • δ) (𝓝 0) (𝓝 u) := by
  have : Continuous (fun s : ℝ => u + s • δ) := by fun_prop
  simpa using this.tendsto 0

theorem hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (u δ : E) : HasDerivAt (fun s : ℝ => u + s • δ) δ 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add u

/-- The second derivative along a line through an admissible point: `H δ δ = d/ds [f'(u + s δ) δ]`. -/
theorem hess_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (u δ : E)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : HasFDerivAt (fderiv ℝ f) H u) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (u + s • δ) δ) (H δ δ) 0 := by
  have hl : HasDerivAt (fun s : ℝ => u + s • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add u
  have h0 : u + (0 : ℝ) • δ = u := by simp
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (u + s • δ)) (H δ) 0 := by
    have := (h0 ▸ hH).comp_hasDerivAt (0 : ℝ) hl
    simpa [Function.comp_def] using this
  have := h1.clm_apply (hasDerivAt_const (0 : ℝ) δ)
  simpa using this

end Hess18

open Hess18

theorem p4_18_1 : CFDLean.JST1.Spec.P4_18_1 := by
  intro d g u hu
  have hC := contDiffAt_entropyFun g hu
  have hD : DifferentiableAt ℝ (fderiv ℝ (entropyFun g)) u :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨fderiv ℝ (fderiv ℝ (entropyFun g)) u, hD.hasFDerivAt, fun δ hδ => ?_⟩
  have h2 := hess_line (entropyFun g) u δ _ hD.hasFDerivAt
  have h3 := hasDerivAt_wline g hu δ
  have heq : (fun s : ℝ => fderiv ℝ (entropyFun g) (u + s • δ) δ) =ᶠ[𝓝 0]
      (fun s : ℝ => pairF (entropyVars g (u + s • δ)) δ) := by
    filter_upwards [(tendsto_line u δ).eventually (eventually_admissible g hu)] with s hs
    rw [(p1_1_0 d g _ hs).fderiv, Sst10.pairCLM_apply]
  have key := h2.unique (h3.congr_of_eventuallyEq heq)
  rw [key]
  exact lt_of_le_of_ne (qE_nonneg g hu δ) (fun h => hδ (qE_eq_zero g hu h.symm))

theorem p4_18_2 : CFDLean.JST1.Spec.P4_18_2 := by
  intro d g U hU
  have hC : ContDiffAt ℝ 2 (eta0 g) U := by
    have := (contDiffAt_entropyFun g hU).comp U (Sst10.hatL d).contDiff.contDiffAt
    exact this
  have hD : DifferentiableAt ℝ (fderiv ℝ (eta0 g)) U :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF := (p2_10_2 d g).1
  have hevA : ∀ᶠ V in 𝓝 U, SAdmissible g V :=
    ((Sst10.hatL d).continuous.tendsto U).eventually (eventually_admissible g hU)
  set H := fderiv ℝ (fderiv ℝ (eta0 g)) U with hHdef
  have hH : HasFDerivAt (fderiv ℝ (eta0 g)) H U := hD.hasFDerivAt
  have hvEta : ∀ V W : SState d, hatState V = hatState W → vEta g V = vEta g W := by
    intro V W h
    funext c
    cases c <;> simp [vEta, h]
  have key : ∀ δ, H δ δ = qE g (hatState U) (hatState δ) := by
    intro δ
    have h2 := hess_line (eta0 g) U δ H hH
    have h3 := hasDerivAt_wline g hU (hatState δ)
    have heq : (fun s : ℝ => fderiv ℝ (eta0 g) (U + s • δ) δ) =ᶠ[𝓝 0]
        (fun s : ℝ => pairF (entropyVars g (hatState U + s • hatState δ)) (hatState δ)) := by
      filter_upwards [(tendsto_line U δ).eventually hevA] with s hs
      rw [(hF _ hs).fderiv, Sst10.pairCLM_apply, Sst10.pair_vEta, Sst10.hat_add, Sst10.hat_smul]
    exact h2.unique (h3.congr_of_eventuallyEq heq)
  have hker := (p2_10_1 d g).1
  have hHδ : ∀ δ, H δ = 0 ↔ hatState δ = 0 := by
    intro δ
    constructor
    · intro h
      have : H δ δ = 0 := by rw [h]; rfl
      rw [key] at this
      have := qE_eq_zero g hU this
      exact this
    · intro h
      have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (eta0 g) (U + s • δ)) (H δ) 0 := by
        have hl := hasDerivAt_line U δ
        have h0 : U + (0 : ℝ) • δ = U := by simp
        have := (h0 ▸ hH).comp_hasDerivAt (0 : ℝ) hl
        simpa [Function.comp_def] using this
      have hc : (fun s : ℝ => fderiv ℝ (eta0 g) (U + s • δ)) =ᶠ[𝓝 0] fun _ => fderiv ℝ (eta0 g) U := by
        filter_upwards [(tendsto_line U δ).eventually hevA] with s hs
        rw [(hF _ hs).fderiv, (hF _ hU).fderiv, hvEta (U + s • δ) U (by rw [Sst10.hat_add, Sst10.hat_smul, h]; simp)]
      exact h1.unique ((hasDerivAt_const (0 : ℝ) (fderiv ℝ (eta0 g) U)).congr_of_eventuallyEq hc)
  refine ⟨H, hH, fun δ => by rw [key]; exact qE_nonneg g hU _, fun δ => ?_, fun δ => ?_⟩
  · rw [hHδ, hker]
  · rw [key]
    constructor
    · intro h; exact (hker δ).1 (qE_eq_zero g hU h)
    · intro h
      rw [(hker δ).2 h]
      simp [qE, Num.dot, mom, thermoQ]

end CFDLean.JST1.Proofs
