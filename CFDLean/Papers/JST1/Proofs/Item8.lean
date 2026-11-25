import CFDLean.Papers.JST1.Spec.Item8
import CFDLean.Papers.JST1.Proofs.Item1
import CFDLean.Papers.JST1.Proofs.Item2Euler
import CFDLean.Papers.JST1.Proofs.Item6
import CFDLean.Entropy.PairFlux

/-! Proofs of item 8 (P2): `thm:closure` (paper lines 309-321, proof 1022-1043). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num

namespace CFDLean.JST1.Proofs
namespace Cl8

/-! ### Bilinearity of `pairF` and `dot` -/

section
variable {κ : Type} [Fintype κ]

theorem pr_sum {Q : Type} (s : Finset Q) (x : κ → ℝ) (f : Q → κ → ℝ) :
    pairF x (∑ q ∈ s, f q) = ∑ q ∈ s, pairF x (f q) := by
  unfold pairF
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem pr_smul (x y : κ → ℝ) (c : ℝ) : pairF x (c • y) = c * pairF x y := by
  simp only [pairF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem pr_add (x y z : κ → ℝ) : pairF x (y + z) = pairF x y + pairF x z := by
  simp only [pairF, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pr_sub (x y z : κ → ℝ) : pairF x (y - z) = pairF x y - pairF x z := by
  simp only [pairF, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pl_sub (x y z : κ → ℝ) : pairF (x - y) z = pairF x z - pairF y z := by
  simp only [pairF, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

end

section
variable {d : ℕ}

theorem dl_sub (x y z : Vec d) : Num.dot (x - y) z = Num.dot x z - Num.dot y z := by
  simp only [Num.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

end

/-! ### P2-8.0: the entropy-variable map is a bijection onto `{w_E < 0}` -/

section
variable {d : ℕ}

theorem vel_prim (g : Gas) {r : ℝ} (hr : r ≠ 0) (v : Vec d) (p : ℝ) : vel (primState g r v p) = v := by
  funext α
  simp only [vel, mom, rho, primState]
  field_simp

theorem pressure_prim (g : Gas) {r : ℝ} (_hr : r ≠ 0) (v : Vec d) (p : ℝ) :
    pressure g (primState g r v p) = p := by
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  have hd : Num.dot (mom (primState g r v p)) (mom (primState g r v p)) = r ^ 2 * Num.dot v v := by
    simp only [Num.dot, mom, primState, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold pressure
  rw [hd]
  simp only [energy, rho, primState]
  field_simp
  ring

theorem eq_prim (g : Gas) {U : State d} (hr : rho U ≠ 0) :
    U = primState g (rho U) (vel U) (pressure g U) := by
  funext c
  cases c with
  | mass => rfl
  | momentum α => exact e1_mom_eq hr α
  | energy => exact e1_energy_eq g hr

theorem entropyVars_inj (g : Gas) {U1 U2 : State d} (h1 : Admissible g U1) (h2 : Admissible g U2)
    (h : entropyVars g U1 = entropyVars g U2) : U1 = U2 := by
  obtain ⟨hr1, hp1⟩ := h1
  obtain ⟨hr2, hp2⟩ := h2
  have hγ := g.one_lt_γ
  have hg : g.γ - 1 ≠ 0 := by linarith
  have hE : rho U1 / pressure g U1 = rho U2 / pressure g U2 := by
    have := congrFun h .energy
    simp only [entropyVars] at this
    rw [neg_div, neg_div] at this
    linarith
  have hθ : 0 < rho U1 / pressure g U1 := div_pos hr1 hp1
  have hv : vel U1 = vel U2 := by
    funext α
    have := congrFun h (.momentum α)
    simp only [entropyVars] at this
    rw [mul_div_right_comm, mul_div_right_comm (rho U2), ← hE] at this
    exact mul_left_cancel₀ hθ.ne' this
  have hs : physEntropy g U1 = physEntropy g U2 := by
    have := congrFun h .mass
    simp only [entropyVars] at this
    have e : ∀ U : State d, rho U * Num.dot (vel U) (vel U) / (2 * pressure g U) =
        rho U / pressure g U * Num.dot (vel U) (vel U) / 2 := fun U => by ring
    rw [e, e U2, ← hE, ← hv] at this
    have h' : (g.γ - physEntropy g U1) / (g.γ - 1) = (g.γ - physEntropy g U2) / (g.γ - 1) := by linarith
    field_simp at h'
    linarith
  -- `ρ = θ p`, so `s = (1 - γ) ln p - γ ln θ`
  have hlog : ∀ U : State d, 0 < rho U → 0 < pressure g U →
      physEntropy g U = (1 - g.γ) * Real.log (pressure g U) - g.γ * Real.log (rho U / pressure g U) := by
    intro U hr hp
    unfold physEntropy
    rw [Real.log_div hr.ne' hp.ne']
    ring
  rw [hlog U1 hr1 hp1, hlog U2 hr2 hp2, hE] at hs
  have hl : Real.log (pressure g U1) = Real.log (pressure g U2) := by
    have : (1 - g.γ) * (Real.log (pressure g U1) - Real.log (pressure g U2)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (by linarith)
    · linarith
  have hp : pressure g U1 = pressure g U2 := Real.log_injOn_pos hp1 hp2 hl
  have hr : rho U1 = rho U2 := by
    rw [hp] at hE
    field_simp at hE
    exact hE
  rw [eq_prim g hr1.ne', eq_prim g hr2.ne', hr, hv, hp]

end

theorem regroup {Q P : Type} [Fintype Q] [Fintype P] [DecidableEq P] {d : ℕ} (fq : Q → P) (f : Q → ℝ)
    (v : P → Vec d) :
    ∑ q, f q • v (fq q) = ∑ p, (∑ q, if fq q = p then f q else 0) • v p := by
  simp only [Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => by rw [Finset.sum_ite_eq]; simp

end Cl8

open Cl8

/-! ### P2-8.0: entropy projection -/

theorem p2_8_0 : Spec.P2_8_0 := by
  intro d g W hW
  have hγ := g.one_lt_γ
  have hg : g.γ - 1 ≠ 0 := by linarith
  have hg' : 1 - g.γ ≠ 0 := by linarith
  set θ : ℝ := -W .energy with hθdef
  have hθ : 0 < θ := by rw [hθdef]; linarith
  set v : Vec d := fun α => W (.momentum α) / θ with hvdef
  set s : ℝ := g.γ - (g.γ - 1) * (W .mass + θ * Num.dot v v / 2) with hsdef
  set p : ℝ := Real.exp ((s + g.γ * Real.log θ) / (1 - g.γ)) with hpdef
  have hp : 0 < p := Real.exp_pos _
  have hr : 0 < θ * p := mul_pos hθ hp
  have hV : Admissible g (primState g (θ * p) v p) := ⟨hr, by rw [pressure_prim g hr.ne']; exact hp⟩
  have hrho : rho (primState g (θ * p) v p) = θ * p := rfl
  have hs : physEntropy g (primState g (θ * p) v p) = s := by
    unfold physEntropy
    rw [pressure_prim g hr.ne', hrho, Real.log_mul hθ.ne' hp.ne', hpdef, Real.log_exp]
    field_simp
    ring
  have hEV : entropyVars g (primState g (θ * p) v p) = W := by
    funext c
    cases c with
    | mass =>
      simp only [entropyVars, hs, vel_prim g hr.ne', pressure_prim g hr.ne', hrho]
      rw [hsdef]
      field_simp
      ring
    | momentum α =>
      simp only [entropyVars, vel_prim g hr.ne', pressure_prim g hr.ne', hrho]
      show θ * p * (W (.momentum α) / θ) / p = W (.momentum α)
      field_simp
    | energy =>
      simp only [entropyVars, pressure_prim g hr.ne', hrho]
      rw [neg_div, mul_div_assoc, div_self hp.ne', mul_one, hθdef, neg_neg]
  exact ⟨_, ⟨hV, hEV⟩, fun U ⟨hU, hUW⟩ => entropyVars_inj g hU hV (hUW.trans hEV.symm)⟩

/-! ### P2-8.1: exact boundary entropy identity and conservation -/

theorem p2_8_1 : Spec.P2_8_1 := CFDLean.Num.quadratureClosure_entropy

/-! ### P2-8.2: free stream -/

theorem p2_8_2 : Spec.P2_8_2 := CFDLean.Num.quadratureClosure_freeStream

/-! ### P2-8.3: linear fluxes -/

theorem p2_8_3 : Spec.P2_8_3 := CFDLean.Num.quadratureClosure_linear

/-! ### P2-8.4: the face rule reproduces `β` and `B_c` -/

theorem p2_8_4 : Spec.P2_8_4 := CFDLean.Num.WMesh.faceRule_beta_B

/-! ### P2-8.5: slip wall -/

theorem p2_8_5 : Spec.P2_8_5 := by
  intro d g U y ⟨hr, hp⟩
  rw [e1_pairF_channel]
  simp only [pressFlux, entropyVars, mul_zero, zero_add, add_zero, fluxPot, Num.dot]
  rw [sub_eq_zero]
  refine Finset.sum_congr rfl fun α _ => ?_
  unfold vel mom
  field_simp

/-! ### P2-8.6: far field -/

theorem p2_8_6 : Spec.P2_8_6 := by
  refine ⟨?_, ?_⟩
  · intro S κ _ d w ψ ut ug N Fs h
    rw [pl_sub, dl_sub] at h
    linarith
  · intro d g Ut Ug N lam ht hg hlam
    rw [pr_sub, pr_smul, (p1_2_5 d g).1 Ut Ug N ht hg]
    have := p1_1_3 d g Ut Ug ht hg
    nlinarith

end CFDLean.JST1.Proofs
