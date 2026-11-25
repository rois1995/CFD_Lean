import CFDLean.Papers.JST1.Spec.Item10
import CFDLean.Papers.JST1.Proofs.Item1
import CFDLean.Papers.JST1.Proofs.Viscous

/-! Proofs of item 10 (P2): the SST coupled entropy. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs
namespace Sst10

variable {d : ℕ}

/-! ### The SST state space -/

/-- The SST channels as a sum type. -/
def schanEquiv (d : ℕ) : SChan d ≃ Channel d ⊕ (Unit ⊕ Unit) where
  toFun
    | .flow c => .inl c
    | .tke => .inr (.inl ())
    | .omg => .inr (.inr ())
  invFun
    | .inl c => .flow c
    | .inr (.inl _) => .tke
    | .inr (.inr _) => .omg
  left_inv c := by cases c <;> rfl
  right_inv x := by rcases x with _ | _ | _ <;> rfl

theorem sum_schan (f : SChan d → ℝ) :
    ∑ c, f c = ∑ c : Channel d, f (.flow c) + f .tke + f .omg := by
  rw [← (schanEquiv d).symm.sum_comp]
  simp [Fintype.sum_sum_type, schanEquiv, add_assoc]

theorem hat_add (U V : SState d) : hatState (U + V) = hatState U + hatState V := by
  funext c; cases c <;> simp only [hatState, Pi.add_apply]
  ring

theorem hat_smul (a : ℝ) (U : SState d) : hatState (a • U) = a • hatState U := by
  funext c; cases c <;> simp only [hatState, Pi.smul_apply, smul_eq_mul]
  ring

theorem hat_sub (U V : SState d) : hatState (U - V) = hatState U - hatState V := by
  funext c; cases c <;> simp only [hatState, Pi.sub_apply]
  ring

/-- `T` as a continuous linear map. -/
def hatL (d : ℕ) : SState d →L[ℝ] State d :=
  LinearMap.toContinuousLinearMap
    { toFun := hatState
      map_add' := hat_add
      map_smul' := hat_smul }

theorem hatL_apply (U : SState d) : hatL d U = hatState U := rfl

theorem pairCLM_apply {κ : Type} [Fintype κ] (w x : κ → ℝ) : pairCLM w x = pairF w x := by
  simp [pairCLM, pairF]

/-- `v^η · R = w(û) · T R`. -/
theorem pair_vEta (g : Gas) (U R : SState d) :
    pairF (vEta g U) R = pairF (entropyVars g (hatState U)) (hatState R) := by
  unfold pairF
  rw [sum_schan, e1_sum_channel, e1_sum_channel]
  simp only [vEta, hatState]
  ring

/-! ### Strict monotonicity of the Euler entropy variables -/

theorem log_mul_pos {r1 r2 : ℝ} (h1 : 0 < r1) (h2 : 0 < r2) (hne : r1 ≠ r2) :
    0 < (Real.log r2 - Real.log r1) * (r2 - r1) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have := Real.log_lt_log h1 h
    exact mul_pos (by linarith) (by linarith)
  · have := Real.log_lt_log h2 h
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)

theorem log_mul_nonneg {r1 r2 : ℝ} (h1 : 0 < r1) (h2 : 0 < r2) :
    0 ≤ (Real.log r2 - Real.log r1) * (r2 - r1) := by
  by_cases hne : r1 = r2
  · rw [hne]; simp
  · exact (log_mul_pos h1 h2 hne).le

theorem thQ_nonneg {γ : ℝ} (hγ : 1 < γ) {r1 p1 r2 p2 : ℝ} (hr1 : 0 < r1) (hp1 : 0 < p1) (hr2 : 0 < r2)
    (hp2 : 0 < p2) : 0 ≤ thQ γ r1 p1 r2 p2 := by
  have h := thermo_path (μ := 1) (ν := 0) hγ (fun a b => by
      simpa using thermoQ_nonneg hγ a b) hr1 hp1 hr2 hp2
  simpa using h

theorem thQ_mul {γ : ℝ} (hg : γ - 1 ≠ 0) (r1 p1 r2 p2 : ℝ) :
    (γ - 1) * thQ γ r1 p1 r2 p2 = -((entS γ r2 p2 - entS γ r1 p1) * (r2 - r1) +
      (r2 / p2 - r1 / p1) * (p2 - p1)) := by
  unfold thQ
  rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hg, mul_one]

/-- `thQ = 0` only for equal densities and pressures. -/
theorem thQ_eq_zero {γ : ℝ} (hγ : 1 < γ) {r1 p1 r2 p2 : ℝ} (hr1 : 0 < r1) (hp1 : 0 < p1) (hr2 : 0 < r2)
    (hp2 : 0 < p2) (h0 : thQ γ r1 p1 r2 p2 = 0) : r1 = r2 ∧ p1 = p2 := by
  have hγ' : 1 < (1 + γ) / 2 := by linarith
  have h' := thQ_nonneg hγ' hr1 hp1 hr2 hp2
  have hg : γ - 1 ≠ 0 := by linarith
  have hg' : (1 + γ) / 2 - 1 ≠ 0 := by linarith
  have e1 := thQ_mul (γ := γ) hg r1 p1 r2 p2
  have e2 := thQ_mul (γ := (1 + γ) / 2) hg' r1 p1 r2 p2
  have e3 : (γ - 1) * thQ γ r1 p1 r2 p2 - ((1 + γ) / 2 - 1) * thQ ((1 + γ) / 2) r1 p1 r2 p2 =
      (γ - 1) / 2 * ((Real.log r2 - Real.log r1) * (r2 - r1)) := by
    rw [e1, e2]; unfold entS; ring
  have hr : r1 = r2 := by
    rcases eq_or_ne r1 r2 with hr | hne
    · exact hr
    exfalso
    have := log_mul_pos hr1 hr2 hne
    rw [h0, mul_zero, zero_sub] at e3
    have : 0 ≤ ((1 + γ) / 2 - 1) * thQ ((1 + γ) / 2) r1 p1 r2 p2 := mul_nonneg (by linarith) h'
    nlinarith
  refine ⟨hr, ?_⟩
  subst hr
  rw [h0, mul_zero] at e1
  have e4 : -((entS γ r1 p2 - entS γ r1 p1) * (r1 - r1) + (r1 / p2 - r1 / p1) * (p2 - p1)) =
      r1 * (p2 - p1) ^ 2 / (p1 * p2) := by field_simp; ring
  rw [e4] at e1
  have : (p2 - p1) ^ 2 = 0 := by
    have := (div_eq_zero_iff.1 e1.symm).resolve_right (by positivity)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hr1.ne'
    · exact h
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

theorem pairF_sub_left {κ : Type} [Fintype κ] (x y z : κ → ℝ) :
    pairF (x - y) z = pairF x z - pairF y z := by
  simp only [pairF, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Strict monotonicity: `[w]·[u] = 0` forces `u1 = u2`. -/
theorem euler_strict (g : Gas) {U1 U2 : State d} (h1 : Admissible g U1) (h2 : Admissible g U2)
    (h0 : pairF (entropyVars g U2 - entropyVars g U1) (U2 - U1) = 0) : U1 = U2 := by
  rw [(pair_decomp g h1 h2).1] at h0
  have hT := thQ_nonneg g.one_lt_γ h1.1 h1.2 h2.1 h2.2
  have hV := velV_nonneg g h1 h2
  have hT0 : thQ g.γ (rho U1) (pressure g U1) (rho U2) (pressure g U2) = 0 := by linarith
  have hV0 : velV g U1 U2 = 0 := by linarith
  obtain ⟨hr, hp⟩ := thQ_eq_zero g.one_lt_γ h1.1 h1.2 h2.1 h2.2 hT0
  have hcoef : 0 < rho U2 / pressure g U2 * rho U1 + rho U1 / pressure g U1 * rho U2 := by
    have := h1.1; have := h1.2; have := h2.1; have := h2.2; positivity
  have hsum : ∑ α, (vel U2 α - vel U1 α) ^ 2 = 0 := by
    unfold velV at hV0
    rcases mul_eq_zero.1 ((div_eq_zero_iff.1 hV0).resolve_right two_ne_zero) with h | h
    · exact absurd h hcoef.ne'
    · exact h
  have hv : ∀ α, vel U1 α = vel U2 α := by
    intro α
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => sq_nonneg (vel U2 α - vel U1 α))).1 hsum α
      (Finset.mem_univ α)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  have hdot : Num.dot (vel U1) (vel U1) = Num.dot (vel U2) (vel U2) := by
    unfold Num.dot; simp only [hv]
  funext c
  cases c with
  | mass => exact hr
  | momentum α => rw [e1_mom_eq h1.1.ne', e1_mom_eq h2.1.ne', hr, hv]
  | energy => rw [e1_energy_eq g h1.1.ne', e1_energy_eq g h2.1.ne', hr, hp, hdot]

/-! ### Convexity of the admissible set -/

theorem persp_le {a b x y r1 r2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : 0 < r1) (h2 : 0 < r2)
    (hr : 0 < a * r1 + b * r2) :
    (a * x + b * y) * (a * x + b * y) / (2 * (a * r1 + b * r2)) ≤
      a * (x * x / (2 * r1)) + b * (y * y / (2 * r2)) := by
  have key : a * (x * x / (2 * r1)) + b * (y * y / (2 * r2)) -
      (a * x + b * y) * (a * x + b * y) / (2 * (a * r1 + b * r2)) =
      a * b * (x * r2 - y * r1) ^ 2 / (2 * r1 * r2 * (a * r1 + b * r2)) := by
    field_simp
    ring
  have : 0 ≤ a * b * (x * r2 - y * r1) ^ 2 / (2 * r1 * r2 * (a * r1 + b * r2)) := by positivity
  linarith

theorem admissible_convex (g : Gas) : Convex ℝ {u : State d | Admissible g u} := by
  intro u1 h1 u2 h2 a b ha hb hab
  obtain ⟨hr1, hp1⟩ := h1
  obtain ⟨hr2, hp2⟩ := h2
  have hg : 0 < g.γ - 1 := by linarith [g.one_lt_γ]
  have ha' : a = 1 - b := by linarith
  have hr : 0 < a * rho u1 + b * rho u2 := by
    have := convex_comb_pos hr1 hr2 hb (by linarith : b ≤ 1)
    rw [ha']; linarith
  have hrho : rho (a • u1 + b • u2) = a * rho u1 + b * rho u2 := rfl
  refine ⟨hrho ▸ hr, ?_⟩
  have i1 : 0 < energy u1 - Num.dot (mom u1) (mom u1) / (2 * rho u1) := by
    unfold pressure at hp1; exact (pos_iff_pos_of_mul_pos hp1).1 hg
  have i2 : 0 < energy u2 - Num.dot (mom u2) (mom u2) / (2 * rho u2) := by
    unfold pressure at hp2; exact (pos_iff_pos_of_mul_pos hp2).1 hg
  have hle : a * (energy u1 - Num.dot (mom u1) (mom u1) / (2 * rho u1)) +
      b * (energy u2 - Num.dot (mom u2) (mom u2) / (2 * rho u2)) ≤
      energy (a • u1 + b • u2) - Num.dot (mom (a • u1 + b • u2)) (mom (a • u1 + b • u2)) /
        (2 * rho (a • u1 + b • u2)) := by
    have hE : energy (a • u1 + b • u2) = a * energy u1 + b * energy u2 := rfl
    have hm : ∀ α, mom (a • u1 + b • u2) α = a * mom u1 α + b * mom u2 α := fun _ => rfl
    rw [hE, hrho]
    unfold Num.dot
    simp only [hm, Finset.sum_div]
    have := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) =>
      persp_le (x := mom u1 α) (y := mom u2 α) ha hb hr1 hr2 hr
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    linarith
  have hpos : 0 < a * (energy u1 - Num.dot (mom u1) (mom u1) / (2 * rho u1)) +
      b * (energy u2 - Num.dot (mom u2) (mom u2) / (2 * rho u2)) := by
    have := convex_comb_pos i1 i2 hb (by linarith : b ≤ 1)
    rw [ha']; linarith
  unfold pressure
  exact mul_pos hg (lt_of_lt_of_le hpos hle)

theorem sadm_convex (g : Gas) : Convex ℝ {U : SState d | SAdmissible g U} := by
  intro U1 h1 U2 h2 a b ha hb hab
  show Admissible g (hatState (a • U1 + b • U2))
  rw [hat_add, hat_smul, hat_smul]
  exact admissible_convex g h1 h2 ha hb hab

/-- `(v^η_2 - v^η_1)·(U_2 - U_1) = [w(û)]·[û]`. -/
theorem pair_vEta_diff (g : Gas) (U1 U2 : SState d) :
    pairF (vEta g U2 - vEta g U1) (U2 - U1) =
      pairF (entropyVars g (hatState U2) - entropyVars g (hatState U1)) (hatState U2 - hatState U1) := by
  rw [pairF_sub_left, pairF_sub_left, pair_vEta, pair_vEta, hat_sub]

/-! ### Pointwise entropy production -/

section Point
variable (D : SSTPoint.Data d)

theorem tau_symm (α β : Fin d) : SSTPoint.tau D α β = SSTPoint.tau D β α := by
  unfold SSTPoint.tau; rw [eq_comm]; by_cases h : α = β
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; ring

theorem two_SS : 2 * SSTPoint.SS D = ∑ α, ∑ β, D.Gv α β * (D.Gv α β + D.Gv β α) := by
  have hsym : (∑ α, ∑ β, D.Gv β α * (D.Gv α β + D.Gv β α)) = ∑ α, ∑ β, D.Gv α β * (D.Gv α β + D.Gv β α) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hsq : 2 * SSTPoint.SS D = (1 / 2) * ((∑ α, ∑ β, D.Gv α β * (D.Gv α β + D.Gv β α)) +
      ∑ α, ∑ β, D.Gv β α * (D.Gv α β + D.Gv β α)) := by
    unfold SSTPoint.SS
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hsq, hsym]; ring

theorem Q_form : SSTPoint.Q D =
    (∑ α, ∑ β, D.Gv α β * (D.Gv α β + D.Gv β α)) - (2 / 3) * (∑ γ, D.Gv γ γ) ^ 2 := by
  unfold SSTPoint.Q SSTPoint.divv; rw [two_SS]

theorem Gv_tau : (∑ α, ∑ β, D.Gv α β * SSTPoint.tau D α β) = (D.μ + D.μt) * SSTPoint.Q D := by
  unfold SSTPoint.tau SSTPoint.divv
  rw [tau_form, Q_form]

theorem Pi_form (hR : D.R ≠ 0) (hT : D.T ≠ 0) :
    SSTPoint.Pi D = -SSTPoint.theta D * (D.μ * SSTPoint.Q D + (D.μt * SSTPoint.Q D - D.Pk) + D.ε) -
        D.κ * Num.dot D.GT D.GT / (D.R * D.T ^ 2) +
        (if D.withDk then 0 else -(D.Dk * Num.dot D.Gk (SSTPoint.Gtheta D))) := by
  have hA : (∑ α, ∑ β, (SSTPoint.theta D * D.Gv α β + D.v α * SSTPoint.Gtheta D β) * SSTPoint.tau D α β) =
      SSTPoint.theta D * (∑ α, ∑ β, D.Gv α β * SSTPoint.tau D α β) +
        ∑ β, SSTPoint.Gtheta D β * ∑ α, SSTPoint.tau D β α * D.v α := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by rw [tau_symm D α β]; ring
  have hT2 : D.R * D.T ^ 2 ≠ 0 := by positivity
  have hG : (∑ β, SSTPoint.Gtheta D β * D.GT β) = -(Num.dot D.GT D.GT / (D.R * D.T ^ 2)) := by
    unfold SSTPoint.Gtheta Num.dot
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hK : (∑ β, SSTPoint.Gtheta D β * (D.Dk * D.Gk β)) = D.Dk * Num.dot D.Gk (SSTPoint.Gtheta D) := by
    unfold Num.dot; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold SSTPoint.Pi
  rw [hA, Gv_tau]
  have hB : (∑ β, (-SSTPoint.Gtheta D β) * ((∑ α, SSTPoint.tau D β α * D.v α) + D.κ * D.GT β +
      (if D.withDk then D.Dk * D.Gk β else 0))) =
      -(∑ β, SSTPoint.Gtheta D β * ∑ α, SSTPoint.tau D β α * D.v α) -
        D.κ * (∑ β, SSTPoint.Gtheta D β * D.GT β) -
        (if D.withDk then ∑ β, SSTPoint.Gtheta D β * (D.Dk * D.Gk β) else 0) := by
    have hpt : ∀ β, (-SSTPoint.Gtheta D β) * ((∑ α, SSTPoint.tau D β α * D.v α) + D.κ * D.GT β +
        (if D.withDk then D.Dk * D.Gk β else 0)) =
        -(SSTPoint.Gtheta D β * ∑ α, SSTPoint.tau D β α * D.v α) - D.κ * (SSTPoint.Gtheta D β * D.GT β) -
          (if D.withDk then SSTPoint.Gtheta D β * (D.Dk * D.Gk β) else 0) := by
      intro β; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun β _ => hpt β, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.mul_sum]
    congr 1
    split_ifs <;> simp
  rw [hB, hG, hK]
  cases D.withDk
  · simp only [Bool.false_eq_true, ite_false]
    ring
  · simp only [ite_true]
    ring

end Point

end Sst10

open Sst10

theorem p2_10_1 : CFDLean.JST1.Spec.P2_10_1 := by
  intro d g
  have hE : ∀ c : SChan d, (Spec.nullE : SState d) c =
      (if c = .flow .energy then 1 else 0) + (if c = .tke then 1 else 0) := by
    intro c; simp [Spec.nullE, Pi.single_apply]
  have hW : ∀ c : SChan d, (Spec.nullW : SState d) c = if c = .omg then 1 else 0 := by
    intro c; simp [Spec.nullW, Pi.single_apply]
  have hker : ∀ a b : ℝ, hatState (a • (Spec.nullE : SState d) + b • Spec.nullW) = 0 := by
    intro a b
    funext c
    cases c <;> simp [hatState, hE, hW]
  refine ⟨fun U => ⟨fun h => ⟨U .tke, U .omg, ?_⟩, ?_⟩, fun U a b => ?_⟩
  · funext c
    have h' := fun c => congrFun h c
    rcases c with c | _ | _
    · cases c with
      | mass => simpa [hatState, hE, hW] using h' .mass
      | momentum α => simpa [hatState, hE, hW] using h' (.momentum α)
      | energy =>
        have := h' .energy
        simp only [hatState, Pi.zero_apply] at this
        simp [hE, hW]
        linarith
    · simp [hE, hW]
    · simp [hE, hW]
  · rintro ⟨a, b, rfl⟩
    exact hker a b
  · unfold eta0
    congr 1
    rw [add_assoc, hat_add, hker, add_zero]

theorem p2_10_2 : CFDLean.JST1.Spec.P2_10_2 := by
  intro d g
  have hF : ∀ U : SState d, SAdmissible g U → HasFDerivAt (eta0 g) (pairCLM (vEta g U)) U := by
    intro U hU
    have h1 := (p1_1_0 d g (hatState U) hU).comp U (hatL d).hasFDerivAt
    refine h1.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ContinuousLinearMap.comp_apply, pairCLM_apply, hatL_apply, pair_vEta]
  refine ⟨hF, pair_vEta g, ?_⟩
  intro ι _ Ut V R t hA hV hD
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((hF _ (hA i)).comp_hasDerivAt t (hD i)).const_mul (V i))
  convert hs using 1
  · rfl
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pairCLM_apply, pairF_smul_right, pair_vEta]
  field_simp [hV i]

theorem p2_10_3 : CFDLean.JST1.Spec.P2_10_3 := by
  intro d g
  have hmono : ∀ U1 U2 : SState d, SAdmissible g U1 → SAdmissible g U2 →
      0 ≤ pairF (vEta g U2 - vEta g U1) (U2 - U1) := by
    intro U1 U2 h1 h2
    rw [pair_vEta_diff]
    exact p1_1_3 d g _ _ h1 h2
  have hF := (p2_10_2 d g).1
  refine ⟨⟨sadm_convex g, fun U1 h1 U2 h2 a b ha hb hab => ?_⟩, fun U1 U2 h1 h2 =>
    ⟨hmono U1 U2 h1 h2, ⟨fun h0 => euler_strict g h1 h2 (by rw [← pair_vEta_diff]; exact h0),
      fun h => by rw [pair_vEta_diff, h, sub_self, sub_self]; simp [pairF]⟩⟩⟩
  -- the restriction to the segment
  set P : ℝ → SState d := fun t => U1 + t • (U2 - U1) with hP
  have hPadm : ∀ t ∈ Set.Icc (0 : ℝ) 1, SAdmissible g (P t) := by
    rintro t ⟨t0, t1⟩
    have := sadm_convex g h1 h2 (by linarith : (0 : ℝ) ≤ 1 - t) t0 (by ring)
    have e : P t = (1 - t) • U1 + t • U2 := by
      funext c
      simp only [hP, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [e]; exact this
  have hPd : ∀ t, HasDerivAt P (U2 - U1) t := by
    intro t
    have := ((hasDerivAt_id t).smul_const (U2 - U1)).const_add U1
    rw [one_smul] at this
    exact this
  have hφd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => eta0 g (P s)) (pairF (vEta g (P t)) (U2 - U1)) t := by
    intro t ht
    have := (hF _ (hPadm t ht)).comp_hasDerivAt t (hPd t)
    rw [pairCLM_apply] at this
    exact this
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => eta0 g (P s)) := by
    refine MonotoneOn.convexOn_of_deriv (convex_Icc 0 1)
      (fun t ht => (hφd t ht).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Icc]
      exact fun t ht => (hφd t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs t ht hst
      rw [(hφd s (Set.Ioo_subset_Icc_self hs)).deriv, (hφd t (Set.Ioo_subset_Icc_self ht)).deriv]
      rcases eq_or_lt_of_le hst with h | h
      · rw [h]
      · have hm := hmono _ _ (hPadm s (Set.Ioo_subset_Icc_self hs)) (hPadm t (Set.Ioo_subset_Icc_self ht))
        have hd : P t - P s = (t - s) • (U2 - U1) := by
          funext c
          simp only [hP, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          ring
        rw [hd, pairF_smul_right, pairF_sub_left] at hm
        have := (mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < t - s)).1 hm
        linarith
  have hc := hconv.2 (x := 0) (y := 1) (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    ha hb hab
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one] at hc
  have e0 : P 0 = U1 := by simp [hP]
  have e1 : P 1 = U2 := by simp [hP]
  have eb : P b = a • U1 + b • U2 := by
    funext c
    simp only [hP, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [show a = 1 - b by linarith]
    ring
  rw [e0, e1, eb] at hc
  exact hc

theorem p2_10_4 : CFDLean.JST1.Spec.P2_10_4 := by
  intro d D hR hT
  simp only []
  have hθ : 0 < SSTPoint.theta D := by unfold SSTPoint.theta; positivity
  have hQ : d ≤ 3 → 0 ≤ SSTPoint.Q D := fun hd => by rw [Q_form]; exact quad_nonneg _ hd
  refine ⟨Pi_form D hR.ne' hT.ne', hQ, fun hd hw hμ hκ hε hP => ?_, fun _ hP => ?_⟩
  · rw [Pi_form D hR.ne' hT.ne', hw, ite_eq_left rfl]
    have h1 : 0 ≤ D.μ * SSTPoint.Q D + (D.μt * SSTPoint.Q D - D.Pk) + D.ε := by
      have := mul_nonneg hμ (hQ hd); linarith
    have h2 : 0 ≤ D.κ * Num.dot D.GT D.GT / (D.R * D.T ^ 2) := by
      have : 0 ≤ Num.dot D.GT D.GT := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
      positivity
    nlinarith
  · unfold SSTPoint.Q
    nlinarith

theorem p2_10_5 : CFDLean.JST1.Spec.P2_10_5 := by
  intro ι _ mdot kv kin bmass hanti
  simp only []
  refine ⟨?_, ?_, ?_⟩
  · set S := ∑ i, ∑ j, mdot i j * (if 0 ≤ mdot i j then kv i else kv j) with hS
    have hpt : ∀ i j, mdot j i * (if 0 ≤ mdot j i then kv j else kv i) =
        -(mdot i j * (if 0 ≤ mdot i j then kv i else kv j)) := by
      intro i j
      rw [hanti i j]
      rcases lt_trichotomy (mdot i j) 0 with h | h | h
      · rw [ite_eq_left (by linarith), ite_eq_right (by linarith)]; ring
      · rw [h]; simp
      · rw [ite_eq_right (by linarith), ite_eq_left h.le]; ring
    have h2 : S = -S := by
      calc S = ∑ i, ∑ j, mdot j i * (if 0 ≤ mdot j i then kv j else kv i) := by
            rw [hS, Finset.sum_comm]
        _ = -S := by
            rw [hS, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j _ => hpt i j
    linarith
  · intro k0 hk hin i
    simp only [hk, hin, ite_self]
    rw [mul_add, Finset.mul_sum, mul_comm k0 (bmass i)]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · intro i hki hbi hk
    simp only [hbi, zero_mul, add_zero]
    refine Finset.sum_nonpos fun j _ => ?_
    split_ifs with h
    · rw [hki, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (hk j)

theorem p2_10_6 : CFDLean.JST1.Spec.P2_10_6 := by
  intro Pst cl ε hε hP
  have : max 0 (min Pst (cl * ε)) ≤ Pst := max_le hP (min_le_left _ _)
  linarith

theorem p2_10_7 : CFDLean.JST1.Spec.P2_10_7 := by
  intro d R μ μt κ wb G hd hR hμ hμt hκ hE
  have hθ : thetaF wb ≠ 0 := by unfold thetaF; linarith
  refine ⟨?_, (p1_4_2 d ⟨R, μ, κ⟩ wb hd hμ hκ hR hE).1 G, (p1_4_2 d ⟨R, μt, 0⟩ wb hd hμt le_rfl hR hE).1 G⟩
  rw [frob_visc _ wb G G hθ, frob_visc _ wb G G hθ, frob_visc _ wb G G hθ]
  unfold tauF DTF
  simp only [tau_form]
  ring

theorem p2_10_8 : CFDLean.JST1.Spec.P2_10_8 := by
  have hpE : ∀ {d : ℕ} (w R : State d) (s : ℝ), pairF w (R + s • eE) = pairF w R + s * w .energy := by
    intro d w R s
    rw [e1_pairF_channel, e1_pairF_channel]
    simp only [Pi.add_apply, Pi.smul_apply, eE, smul_eq_mul, mul_zero, add_zero, mul_one]
    ring
  refine ⟨?_, ?_⟩
  · intro ι C _ _ d w Rhat X Ck Bk Dh Sk Rrho Pst V β2 inD kD Dgal Dt PiW Bhat Pi2 Pi4 hw hβ hV hP hR _ hX hS
      hD hDt hW
    simp only []
    refine ⟨?_, fun T => by linarith [hW T], fun i => ?_, fun i => ?_⟩
    · simp only [Finset.sum_sub_distrib] at hR
      simp only [hpE, hw, Finset.sum_add_distrib, Finset.sum_sub_distrib, hDt]
      have key : ∀ i, (X i - (if inD i = true then kD * Rrho i else Ck i + Bk i + Dh i - V i * Sk i)) *
          -β2 i ≥ (if inD i = true then 0 else β2 i * V i * (Pst i - Sk i)) +
            (if inD i = true then β2 i * V i * Pst i else 0) - β2 i * V i * Pst i := by
        intro i
        cases h : inD i
        · simp only [ite_false, Bool.false_eq_true]
          rw [hX i h]
          nlinarith
        · simp only [ite_true]
          nlinarith [hD i h, hβ i]
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at this
      linarith
    · split_ifs with h
      · exact le_rfl
      · have := hS i (by simpa using h)
        have := mul_nonneg (hβ i) (hV i)
        nlinarith
    · split_ifs
      · exact mul_nonneg (mul_nonneg (hβ i) (hV i)) (hP i)
      · exact le_rfl
  · intro Dgal Dt PiW c
    refine ⟨fun h0 h1 => by linarith, fun hc h1 h2 => ?_⟩
    have : Dgal - Dt ≥ Dgal / c := by
      have : (1 - 1 / c) * Dgal = Dgal - Dgal / c := by ring
      linarith
    linarith

end CFDLean.JST1.Proofs
