import CFDLean.Papers.JST1.Spec.Item17
import CFDLean.Papers.JST1.Proofs.Item10

/-! Proofs of item 17 (P4): the continuous entropy balance of SST (`prop:sstpde`). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Pde17
open Sst10

variable {d : ℕ}

/-- `w(u) · u = ρ + η(u)`. -/
theorem pair_self (g : Gas) {u : State d} (hu : Admissible g u) :
    pairF (entropyVars g u) u = rho u + entropyFun g u := by
  have hr : rho u ≠ 0 := hu.1.ne'
  have hp : pressure g u ≠ 0 := hu.2.ne'
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  have hm : ∀ α, u (.momentum α) = rho u * vel u α := e1_mom_eq hr
  have hE : u .energy = pressure g u / (g.γ - 1) + rho u * Num.dot (vel u) (vel u) / 2 := by
    have := dot_mom hr
    rw [pressure, energy, this]
    field_simp
    ring
  rw [e1_pairF_channel]
  simp only [entropyVars, entropyFun]
  have h1 : ∑ α, rho u * vel u α / pressure g u * u (.momentum α) =
      rho u ^ 2 * Num.dot (vel u) (vel u) / pressure g u := by
    simp only [hm, Num.dot, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [h1, hE]
  show _ = u .mass + _
  have : rho u = u .mass := rfl
  rw [← this]
  field_simp
  ring

theorem pairF_single {κ : Type} [Fintype κ] [DecidableEq κ] (w : κ → ℝ) (c : κ) :
    pairF w (Pi.single c 1) = w c := by
  simp [pairF, Pi.single_apply]

theorem pairF_add' {κ : Type} [Fintype κ] (w x y : κ → ℝ) : pairF w (x + y) = pairF w x + pairF w y := by
  simp [pairF, mul_add, Finset.sum_add_distrib]

theorem pairF_sub' {κ : Type} [Fintype κ] (w x y : κ → ℝ) : pairF w (x - y) = pairF w x - pairF w y := by
  simp [pairF, mul_sub, Finset.sum_sub_distrib]

theorem pairF_smul' {κ : Type} [Fintype κ] (w x : κ → ℝ) (c : ℝ) : pairF w (c • x) = c * pairF w x := by
  simp [pairF, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem pairF_fsum {κ ι : Type} [Fintype κ] [Fintype ι] (w : κ → ℝ) (f : ι → κ → ℝ) :
    pairF w (∑ i, f i) = ∑ i, pairF w (f i) := by
  simp only [pairF, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Expansion of `v^η · X` in the flow, `k` and `ω` rows. -/
theorem pair_vEta_expand (g : Gas) (V X : SState d) :
    pairF (vEta g V) X = vEta g V (.flow .mass) * X (.flow .mass) +
      (∑ α, (rho (hatState V) / pressure g (hatState V)) * vel (hatState V) α * X (.flow (.momentum α))) -
      (rho (hatState V) / pressure g (hatState V)) * X (.flow .energy) +
      (rho (hatState V) / pressure g (hatState V)) * X .tke := by
  unfold pairF
  rw [sum_schan, e1_sum_channel]
  simp only [vEta, entropyVars]
  have : ∀ α, rho (hatState V) * vel (hatState V) α / pressure g (hatState V) * X (.flow (.momentum α)) =
      rho (hatState V) / pressure g (hatState V) * vel (hatState V) α * X (.flow (.momentum α)) :=
    fun α => by ring
  simp only [this]
  ring

/-- `θ = ρ/p = 1/(R T)` with `T = p/(Rρ)`, as an identity of functions (division by zero is 0). -/
theorem theta_eq (R a b : ℝ) (hR : R ≠ 0) : a / b = 1 / (R * (b / (R * a))) := by
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha]
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb]
  field_simp

/-- The SST convective flux as `v_β U + p (e_{m_β} + v_β e_E)`. -/
theorem conv_rep (g : Gas) (V : SState d) (β : Fin d) (hr : rho (hatState V) ≠ 0) :
    Spec.sstConvFlux g V β = vel (hatState V) β • V + pressure g (hatState V) •
      (Pi.single (SChan.flow (Channel.momentum β)) 1 + vel (hatState V) β • Pi.single (SChan.flow .energy) 1) := by
  funext c
  rcases c with c | _ | _
  · cases c with
    | mass =>
      simp only [Spec.sstConvFlux, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      unfold vel mom
      have : rho (hatState V) = V (.flow .mass) := rfl
      rw [this] at hr
      have e1 : hatState V (.momentum β) = V (.flow (.momentum β)) := rfl
      simp only [e1, this, SChan.flow.injEq, reduceCtorEq, ite_false, add_zero, mul_zero]
      field_simp
    | momentum α =>
      simp only [Spec.sstConvFlux, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases h : α = β
      · subst h; simp; ring
      · simp [h]; ring
    | energy =>
      simp only [Spec.sstConvFlux, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      simp
      ring
  · simp [Spec.sstConvFlux]; ring
  · simp [Spec.sstConvFlux]; ring

end Pde17

open Pde17 Sst10 in
theorem p4_17_1 : CFDLean.JST1.Spec.P4_17_1 := by
  intro d g D U Fv t x Ut Ux dFc dFv Fω Sω hR hA hUt hUx hFc hFv hv hT hGv hGT hGk hmass hFvx hpde
  dsimp only
  set u0 := U t x with hu0
  have hr : 0 < rho (hatState u0) := hA.1
  have hp : 0 < pressure g (hatState u0) := hA.2
  set θ0 := rho (hatState u0) / pressure g (hatState u0) with hθ0
  have hRne : D.R ≠ 0 := hR.ne'
  have hTD : D.T = pressure g (hatState u0) / (D.R * rho (hatState u0)) := hT
  have hTne : D.T ≠ 0 := by rw [hTD]; positivity
  have hθ : SSTPoint.theta D = θ0 := by
    unfold SSTPoint.theta
    rw [hTD, hθ0]
    field_simp
  have hl0 : ∀ β : Fin d, x + (0 : ℝ) • (Pi.single β 1 : Vec d) = x := fun β => by simp
  have hF := (p2_10_2 d g).1
  -- the components of `v^η` at `x`
  have hvm : ∀ α, vEta g u0 (.flow (.momentum α)) = θ0 * D.v α := by
    intro α; rw [hv]; simp only [vEta, entropyVars, hθ0]; ring
  have hve : vEta g u0 (.flow .energy) = -θ0 := by
    simp only [vEta, entropyVars, hθ0]; ring
  -- `G` at `x`
  have hGx : ∀ β, -pairF (vEta g u0) (Fv x β) =
      SSTPoint.theta D * D.κ * D.GT β - (if D.withDk then 0 else SSTPoint.theta D * D.Dk * D.Gk β) := by
    intro β
    rw [hFvx β, pair_vEta_expand, hθ, ← hθ0]
    simp only [Spec.sstViscFlux, mul_zero, zero_add]
    have : ∀ α, θ0 * vel (hatState u0) α * SSTPoint.tau D α β = θ0 * (SSTPoint.tau D β α * D.v α) := by
      intro α; rw [tau_symm D α β, ← hv]; ring
    simp only [this, ← Finset.mul_sum]
    cases D.withDk <;> simp <;> ring
  -- time derivative
  have ha : HasDerivAt (fun τ => eta0 g (U τ x)) (pairF (vEta g u0) Ut) t := by
    have := (hF u0 hA).comp_hasDerivAt t hUt
    rw [pairCLM_apply] at this
    exact this
  -- line derivatives
  have hη : ∀ β, HasDerivAt (fun s : ℝ => eta0 g (U t (x + s • Pi.single β 1))) (pairF (vEta g u0) (Ux β)) 0 := by
    intro β
    have h1 : HasFDerivAt (eta0 g) (pairCLM (vEta g u0)) (U t (x + (0 : ℝ) • Pi.single β 1)) := by
      rw [hl0]; exact hF u0 hA
    have := h1.comp_hasDerivAt (0 : ℝ) (hUx β)
    rw [pairCLM_apply] at this
    exact this
  have hθl : ∀ β, HasDerivAt (fun s : ℝ => rho (hatState (U t (x + s • Pi.single β 1))) /
      pressure g (hatState (U t (x + s • Pi.single β 1)))) (SSTPoint.Gtheta D β) 0 := by
    intro β
    have e : (fun s : ℝ => rho (hatState (U t (x + s • Pi.single β 1))) /
        pressure g (hatState (U t (x + s • Pi.single β 1)))) =
        fun s => (D.R * Spec.sstTemp g D.R (U t (x + s • Pi.single β 1)))⁻¹ := by
      funext s; rw [theta_eq D.R _ _ hRne, one_div]; rfl
    rw [e]
    have hT0 : Spec.sstTemp g D.R (U t (x + (0 : ℝ) • Pi.single β 1)) = D.T := by rw [hl0, hT]
    have := ((hGT β).const_mul D.R).inv (by rw [hT0]; exact mul_ne_zero hRne hTne)
    convert this using 1
    rw [hT0]; unfold SSTPoint.Gtheta; field_simp
  have hcomp : ∀ β (c : SChan d), HasDerivAt (fun s : ℝ => U t (x + s • Pi.single β 1) c) (Ux β c) 0 :=
    fun β c => hasDerivAt_pi.1 (hUx β) c
  have hev : ∀ β, ∀ᶠ s in 𝓝 (0 : ℝ), rho (hatState (U t (x + s • Pi.single β 1))) ≠ 0 := by
    intro β
    have h0 : U t (x + (0 : ℝ) • Pi.single β 1) (SChan.flow .mass) ≠ 0 := by rw [hl0]; exact hr.ne'
    exact (hcomp β (SChan.flow .mass)).continuousAt.eventually_ne h0
  -- the pressure along a line: `p = R ρ T`
  have hpl : ∀ β, HasDerivAt (fun s : ℝ => pressure g (hatState (U t (x + s • Pi.single β 1))))
      (D.R * (Ux β (SChan.flow .mass) * D.T + rho (hatState u0) * D.GT β)) 0 := by
    intro β
    have h := ((hcomp β (SChan.flow .mass)).mul (hGT β)).const_mul D.R
    have hT0 : Spec.sstTemp g D.R (U t (x + (0 : ℝ) • Pi.single β 1)) = D.T := by rw [hl0, hT]
    have hr0 : U t (x + (0 : ℝ) • Pi.single β 1) (SChan.flow .mass) = rho (hatState u0) := by rw [hl0]; rfl
    rw [hT0, hr0] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hev β] with s hs
    simp only [Pi.mul_apply]
    unfold Spec.sstTemp
    have : rho (hatState (U t (x + s • Pi.single β 1))) = U t (x + s • Pi.single β 1) (SChan.flow .mass) := rfl
    rw [← this]
    field_simp
  -- compatibility of the convective flux: `v^η · ∂_β F^c_β = ∂_β (v_β η0)`
  have hcompat : ∀ β, pairF (vEta g u0) (dFc β) =
      D.Gv β β * eta0 g u0 + D.v β * pairF (vEta g u0) (Ux β) := by
    intro β
    have hv0 : vel (hatState (U t (x + (0 : ℝ) • Pi.single β 1))) β = D.v β := by rw [hl0, hv]
    have hu00 : U t (x + (0 : ℝ) • Pi.single β 1) = u0 := by rw [hl0]
    have hp00 : pressure g (hatState (U t (x + (0 : ℝ) • Pi.single β 1))) = pressure g (hatState u0) := by
      rw [hu00]
    have hD := ((hGv β β).smul (hUx β)).add ((hpl β).smul ((hasDerivAt_const (0 : ℝ)
      (Pi.single (SChan.flow (Channel.momentum β)) 1 : SState d)).add
        ((hGv β β).smul (hasDerivAt_const (0 : ℝ) (Pi.single (SChan.flow .energy) 1 : SState d)))))
    have hD' := hD.congr_of_eventuallyEq (f₁ := fun s : ℝ => Spec.sstConvFlux g (U t (x + s • Pi.single β 1)) β)
      (by filter_upwards [hev β] with s hs; exact conv_rep g _ β hs)
    have heq := (hFc β).unique hD'
    rw [heq]
    simp only [Pi.add_apply, Pi.smul_apply']
    simp only [hu00, pairF_add', pairF_smul', zero_add, smul_zero, pairF_single, hvm, hve]
    rw [pair_vEta g u0 u0, pair_self g hA, ← hv, show entropyFun g (hatState u0) = eta0 g u0 from rfl]
    rw [hθ0]
    field_simp
    ring
  -- the viscous entropy flux `G` along a line
  have hdFm : ∀ β, dFv β (.flow .mass) = 0 := by
    intro β
    have h1 := hasDerivAt_pi.1 (hFv β) (SChan.flow .mass)
    have h2 : HasDerivAt (fun s : ℝ => Fv (x + s • Pi.single β 1) β (SChan.flow .mass)) 0 0 := by
      simp only [hmass]; exact hasDerivAt_const _ _
    exact h1.unique h2
  set Rb : Fin d → ℝ := fun β =>
    (∑ α, (SSTPoint.theta D * D.Gv α β + D.v α * SSTPoint.Gtheta D β) * SSTPoint.tau D α β) -
      SSTPoint.Gtheta D β * ((∑ α, SSTPoint.tau D β α * D.v α) + D.κ * D.GT β +
        (if D.withDk then D.Dk * D.Gk β else 0)) +
      SSTPoint.Gtheta D β * (D.Dk * D.Gk β) with hRb
  have hGl : ∀ β, HasDerivAt (fun s : ℝ => -pairF (vEta g (U t (x + s • Pi.single β 1)))
      (Fv (x + s • Pi.single β 1) β)) (-pairF (vEta g u0) (dFv β) - Rb β) 0 := by
    intro β
    have hFc' : ∀ c, HasDerivAt (fun s : ℝ => Fv (x + s • Pi.single β 1) β c) (dFv β c) 0 :=
      fun c => hasDerivAt_pi.1 (hFv β) c
    have e : (fun s : ℝ => -pairF (vEta g (U t (x + s • Pi.single β 1))) (Fv (x + s • Pi.single β 1) β)) =
        fun s => -((∑ α, (rho (hatState (U t (x + s • Pi.single β 1))) /
            pressure g (hatState (U t (x + s • Pi.single β 1)))) *
            vel (hatState (U t (x + s • Pi.single β 1))) α * Fv (x + s • Pi.single β 1) β (.flow (.momentum α))) -
          (rho (hatState (U t (x + s • Pi.single β 1))) / pressure g (hatState (U t (x + s • Pi.single β 1)))) *
            Fv (x + s • Pi.single β 1) β (.flow .energy) +
          (rho (hatState (U t (x + s • Pi.single β 1))) / pressure g (hatState (U t (x + s • Pi.single β 1)))) *
            Fv (x + s • Pi.single β 1) β .tke) := by
      funext s
      rw [pair_vEta_expand, hmass, mul_zero, zero_add]
    rw [e]
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun α _ => ((hθl β).mul (hGv α β)).mul (hFc' (.flow (.momentum α))))
    have hall := ((hsum.sub ((hθl β).mul (hFc' (.flow .energy)))).add ((hθl β).mul (hFc' .tke))).neg
    convert hall using 1
    have hθs' : rho (hatState (U t x)) / pressure g (hatState (U t x)) = SSTPoint.theta D := by
      rw [hθ, hθ0]
    have hvs : ∀ α, vel (hatState (U t x)) α = D.v α := fun α => by rw [hv]
    simp only [Pi.mul_apply, hl0, hθs', hvs, hFvx]
    rw [pair_vEta_expand, hdFm, mul_zero, zero_add, ← hθ0, ← hθ]
    simp only [hRb, Spec.sstViscFlux]
    have hvθ : ∀ α, vel (hatState u0) α = D.v α := fun α => by rw [hv]
    simp only [hvθ]
    simp only [Finset.sum_add_distrib, add_mul, mul_add, Finset.mul_sum]
    have e1 : ∀ α, SSTPoint.Gtheta D β * D.v α * SSTPoint.tau D α β =
        D.v α * SSTPoint.Gtheta D β * SSTPoint.tau D α β := fun α => by ring
    simp only [e1]
    ring
  -- assemble
  refine ⟨fun β => hGx β, pairF (vEta g u0) Ut,
    fun β => pairF (vEta g u0) (dFc β) + (-pairF (vEta g u0) (dFv β) - Rb β), ha, fun β => ?_, ?_⟩
  · have h1 := (hGv β β).mul (hη β)
    have hv0 : vel (hatState (U t (x + (0 : ℝ) • Pi.single β 1))) β = D.v β := by rw [hl0, hv]
    have he0 : eta0 g (U t (x + (0 : ℝ) • Pi.single β 1)) = eta0 g u0 := by rw [hl0]
    rw [hv0, he0, ← hcompat β] at h1
    exact h1.add (hGl β)
  · have hS : Ut + ∑ β, dFc β - ∑ β, dFv β = Spec.sstSource D.Pk D.ε Sω := by rw [hpde]; abel
    have hPS : pairF (vEta g u0) (Spec.sstSource D.Pk D.ε Sω) = SSTPoint.theta D * (D.Pk - D.ε) := by
      rw [pair_vEta_expand]
      simp only [Spec.sstSource, mul_zero, zero_add, Finset.sum_const_zero, sub_zero]
      rw [hθ]
    have hlin : pairF (vEta g u0) Ut + ∑ β, (pairF (vEta g u0) (dFc β) + (-pairF (vEta g u0) (dFv β) - Rb β)) =
        pairF (vEta g u0) (Ut + ∑ β, dFc β - ∑ β, dFv β) - ∑ β, Rb β := by
      rw [pairF_sub', pairF_add', pairF_fsum, pairF_fsum]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      ring
    rw [hlin, hS, hPS, ← Pi_form D hRne hTne]
    unfold SSTPoint.Pi
    simp only [hRb, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun β α => (SSTPoint.theta D * D.Gv α β + D.v α * SSTPoint.Gtheta D β) *
      SSTPoint.tau D α β)]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

end CFDLean.JST1.Proofs
