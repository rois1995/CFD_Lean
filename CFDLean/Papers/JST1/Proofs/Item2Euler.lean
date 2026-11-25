import CFDLean.Papers.JST1.Proofs.Item2Generic

noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

variable {d : ℕ}

/-! ### Generic helpers -/

theorem dot_add_l (a b c : Vec d) : Num.dot (a + b) c = Num.dot a c + Num.dot b c := by
  simp only [Num.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
theorem dot_add_r (a b c : Vec d) : Num.dot a (b + c) = Num.dot a b + Num.dot a c := by
  simp only [Num.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem ir_dot_sub_l (a b c : Vec d) : Num.dot (a - b) c = Num.dot a c - Num.dot b c := by
  simp only [Num.dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
theorem dot_sub_r (a b c : Vec d) : Num.dot a (b - c) = Num.dot a b - Num.dot a c := by
  simp only [Num.dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
theorem ir_dot_smul_l (r : ℝ) (a c : Vec d) : Num.dot (r • a) c = r * Num.dot a c := by
  simp only [Num.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
theorem ir_dot_smul_r (r : ℝ) (a c : Vec d) : Num.dot a (r • c) = r * Num.dot a c := by
  simp only [Num.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
theorem dot_comm' (a c : Vec d) : Num.dot a c = Num.dot c a := by
  simp only [Num.dot, mul_comm]

/-- Reindexing of the channels. -/
def chEquiv : Unit ⊕ Fin d ⊕ Unit ≃ Channel d where
  toFun
    | .inl _ => .mass
    | .inr (.inl α) => .momentum α
    | .inr (.inr _) => .energy
  invFun
    | .mass => .inl ()
    | .momentum α => .inr (.inl α)
    | .energy => .inr (.inr ())
  left_inv := by intro x; rcases x with _ | _ | _ <;> rfl
  right_inv := by intro c; cases c <;> rfl

theorem ir_sum_channel (f : Channel d → ℝ) :
    ∑ c, f c = f .mass + ∑ α, f (.momentum α) + f .energy := by
  rw [← Equiv.sum_comp chEquiv]
  simp [Fintype.sum_sum_type, chEquiv]
  ring

theorem ir_pairF_channel (x z : State d) :
    pairF x z = x .mass * z .mass + Num.dot (mom x) (mom z) + x .energy * z .energy := by
  unfold pairF
  rw [ir_sum_channel]
  rfl

theorem logMean_comm (a b : ℝ) : logMean a b = logMean b a := by
  unfold logMean
  by_cases h : a = b
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), ← neg_sub b a, ← neg_sub (Real.log b) (Real.log a), neg_div_neg_eq]

/-! ### Symmetry and linearity -/

theorem ismailRoe_symm (g : Gas) (Ua Ub : State d) (y : Vec d) :
    ismailRoe g Ua Ub y = ismailRoe g Ub Ua y := by
  simp only [ismailRoe]
  generalize √(rho Ua / pressure g Ua) = z1a
  generalize √(rho Ub / pressure g Ub) = z1b
  generalize √(rho Ua * pressure g Ua) = z5a
  generalize √(rho Ub * pressure g Ub) = z5b
  rw [logMean_comm z5b z5a, logMean_comm z1b z1a, add_comm z1b z1a, add_comm z5b z5a]
  have h : (fun α => (z1b * vel Ub α + z1a * vel Ua α) / 2 / ((z1a + z1b) / 2)) =
      (fun α => (z1a * vel Ua α + z1b * vel Ub α) / 2 / ((z1a + z1b) / 2)) := by
    funext α; ring
  rw [h]
  funext c
  cases c <;> dsimp only; ring

theorem ismailRoe_linear (g : Gas) (Ua Ub : State d) : IsLinearMap ℝ (ismailRoe g Ua Ub) := by
  constructor
  · intro x y
    funext c
    cases c <;> simp only [ismailRoe, dot_add_r, Pi.add_apply] <;> ring
  · intro r x
    funext c
    cases c <;> simp only [ismailRoe, ir_dot_smul_r, Pi.smul_apply, smul_eq_mul] <;> ring


/-! ### Admissible states -/

theorem ir_mom_eq (U : State d) (h : rho U ≠ 0) : mom U = rho U • vel U := by
  funext α
  simp only [vel, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem ir_energy_eq (g : Gas) (U : State d) (h : rho U ≠ 0) :
    energy U = pressure g U / (g.γ - 1) + rho U * Num.dot (vel U) (vel U) / 2 := by
  have hg : g.γ - 1 ≠ 0 := by have := g.one_lt_γ; linarith
  have hm : Num.dot (mom U) (mom U) = rho U * rho U * Num.dot (vel U) (vel U) := by
    rw [ir_mom_eq U h, ir_dot_smul_l, ir_dot_smul_r]; ring
  simp only [pressure, hm]
  field_simp
  ring

theorem zfacts (g : Gas) (U : State d) (hU : Admissible g U) :
    0 < √(rho U / pressure g U) ∧ 0 < √(rho U * pressure g U) ∧
      rho U = √(rho U / pressure g U) * √(rho U * pressure g U) ∧
      pressure g U = √(rho U * pressure g U) / √(rho U / pressure g U) := by
  obtain ⟨hr, hp⟩ := hU
  have h1 : 0 < √(rho U / pressure g U) := Real.sqrt_pos.mpr (div_pos hr hp)
  have h5 : 0 < √(rho U * pressure g U) := Real.sqrt_pos.mpr (mul_pos hr hp)
  have hprod : rho U = √(rho U / pressure g U) * √(rho U * pressure g U) := by
    rw [← Real.sqrt_mul (div_nonneg hr.le hp.le)]
    have : rho U / pressure g U * (rho U * pressure g U) = rho U ^ 2 := by field_simp
    rw [this, Real.sqrt_sq hr.le]
  have hsq : √(rho U / pressure g U) ^ 2 = rho U / pressure g U := Real.sq_sqrt (div_nonneg hr.le hp.le)
  refine ⟨h1, h5, hprod, ?_⟩
  rw [eq_div_iff h1.ne']
  have h2 : pressure g U * √(rho U / pressure g U) ^ 2 = rho U := by
    rw [hsq]; field_simp
  have e : √(rho U / pressure g U) * (pressure g U * √(rho U / pressure g U)) =
      √(rho U / pressure g U) * √(rho U * pressure g U) := by
    calc _ = pressure g U * √(rho U / pressure g U) ^ 2 := by ring
      _ = _ := h2
      _ = _ := hprod
  exact mul_left_cancel₀ h1.ne' e

/-! ### P1-2.0 -/

theorem p1_2_0 : Spec.P1_2_0 := by
  intro d g U y hU
  have hr : rho U ≠ 0 := hU.1.ne'
  have hp : pressure g U ≠ 0 := hU.2.ne'
  have hg : g.γ - 1 ≠ 0 := by have := g.one_lt_γ; linarith
  rw [ir_pairF_channel]
  have hw : mom (entropyVars g U) = (rho U / pressure g U) • vel U := by
    funext α; simp only [mom, entropyVars, Pi.smul_apply, smul_eq_mul]; ring
  have hF : mom (physFlux g U y) = (rho U * Num.dot (vel U) y) • vel U + pressure g U • y := by
    funext α
    simp only [mom, physFlux, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hmα : U (Channel.momentum α) = rho U * vel U α := by
      simp only [vel, mom]; field_simp
    rw [hmα]
    ring
  rw [hw, hF]
  simp only [entropyVars, physFlux, entropyFun, fluxPot, dot_add_r, ir_dot_smul_l, ir_dot_smul_r,
    ir_energy_eq g U hr, ir_mom_eq U hr]
  field_simp
  ring


/-! ### Consistency -/

theorem logMean_self (a : ℝ) : logMean a a = a := by simp [logMean]

theorem ismailRoe_consistent (g : Gas) (U : State d) (y : Vec d) (hU : Admissible g U) :
    ismailRoe g U U y = physFlux g U y := by
  obtain ⟨h1, h5, hr, hp⟩ := zfacts g U hU
  have hr0 : rho U ≠ 0 := hU.1.ne'
  have hg : g.γ - 1 ≠ 0 := by have := g.one_lt_γ; linarith
  have hγ : g.γ ≠ 0 := by have := g.one_lt_γ; linarith
  have hm := ir_mom_eq U hr0
  have he := ir_energy_eq g U hr0
  funext c
  simp only [ismailRoe, logMean_self]
  generalize √(rho U / pressure g U) = z1 at hr hp h1 ⊢
  generalize √(rho U * pressure g U) = z5 at hr hp h5 ⊢
  have huh : (fun α => (z1 * vel U α + z1 * vel U α) / 2 / ((z1 + z1) / 2)) = vel U := by
    funext α; field_simp
  cases c
  · simp only [physFlux]
    rw [huh, hm, ir_dot_smul_l, hr]
    ring
  · simp only [physFlux]
    rw [huh, hm, hp]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hr]
    field_simp
    ring
  · simp only [physFlux]
    rw [huh, he, hp, hr]
    field_simp
    ring

/-! ### Tadmor's condition -/

theorem mom_def (U : State d) : mom U = fun α => U (.momentum α) := rfl

theorem dot_lin2_l (va vb y : Vec d) (za zb m : ℝ) :
    Num.dot (fun α => (za * va α + zb * vb α) / 2 / m) y = za / 2 / m * Num.dot va y + zb / 2 / m * Num.dot vb y := by
  simp only [Num.dot, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_lin2_r (x va vb : Vec d) (za zb m : ℝ) :
    Num.dot x (fun α => (za * va α + zb * vb α) / 2 / m) = za / 2 / m * Num.dot x va + zb / 2 / m * Num.dot x vb := by
  simp only [Num.dot, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_momIR (W va vb y : Vec d) (R m K P za zb : ℝ) :
    Num.dot W (fun α => R * ((za * va α + zb * vb α) / 2 / m) * K + P * y α) =
      R * K * (za / 2 / m) * Num.dot W va + R * K * (zb / 2 / m) * Num.dot W vb + P * Num.dot W y := by
  simp only [Num.dot, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem ismailRoe_tadmor (g : Gas) (Ua Ub : State d) (y : Vec d) (ha : Admissible g Ua)
    (hb : Admissible g Ub) :
    pairF (entropyVars g Ub - entropyVars g Ua) (ismailRoe g Ua Ub y) = Num.dot (fluxPot Ub - fluxPot Ua) y := by
  obtain ⟨h1a, h5a, hra, hpa⟩ := zfacts g Ua ha
  obtain ⟨h1b, h5b, hrb, hpb⟩ := zfacts g Ub hb
  have hma := ir_mom_eq Ua ha.1.ne'
  have hmb := ir_mom_eq Ub hb.1.ne'
  have hg : g.γ - 1 ≠ 0 := by have := g.one_lt_γ; linarith
  have hγ : g.γ ≠ 0 := by have := g.one_lt_γ; linarith
  have hψ : Num.dot (fluxPot Ub - fluxPot Ua) y = rho Ub * Num.dot (vel Ub) y - rho Ua * Num.dot (vel Ua) y := by
    simp only [fluxPot, hma, hmb, ir_dot_sub_l, ir_dot_smul_l]
  have hw : mom (entropyVars g Ub - entropyVars g Ua) =
      (rho Ub / pressure g Ub) • vel Ub - (rho Ua / pressure g Ua) • vel Ua := by
    funext α; simp only [mom, entropyVars, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hψ, ir_pairF_channel, hw]
  simp only [ismailRoe, Pi.sub_apply, entropyVars, physEntropy]
  generalize √(rho Ua / pressure g Ua) = z1a at hra hpa h1a ⊢
  generalize √(rho Ua * pressure g Ua) = z5a at hra hpa h5a ⊢
  generalize √(rho Ub / pressure g Ub) = z1b at hrb hpb h1b ⊢
  generalize √(rho Ub * pressure g Ub) = z5b at hrb hpb h5b ⊢
  simp only [mom_def]
  simp only [dot_momIR, dot_lin2_l, dot_lin2_r, ir_dot_sub_l, ir_dot_smul_l]
  rw [dot_comm' (vel Ub) (vel Ua)]
  rw [hra, hrb, hpa, hpb]
  simp only [Real.log_div h5a.ne' h1a.ne', Real.log_mul h1a.ne' h5a.ne',
    Real.log_div h5b.ne' h1b.ne', Real.log_mul h1b.ne' h5b.ne']
  obtain ⟨-, -, hL1pos, hL1⟩ := p1_2_4 z1a z1b h1a h1b
  obtain ⟨-, -, hL5pos, hL5⟩ := p1_2_4 z5a z5b h5a h5b
  generalize logMean z1a z1b = L1 at hL1pos hL1 ⊢
  generalize logMean z5a z5b = L5 at hL5pos hL5 ⊢
  generalize Real.log z1b = lb1 at hL1 ⊢
  generalize Real.log z5b = lb5 at hL5 ⊢
  have e1 : lb1 = Real.log z1a + (z1b - z1a) / L1 := by
    field_simp; linarith
  have e5 : lb5 = Real.log z5a + (z5b - z5a) / L5 := by
    field_simp; linarith
  subst e1 e5
  have : z1a + z1b ≠ 0 := by positivity
  field_simp
  ring

/-! ### P1-2.5 -/

theorem p1_2_5 : Spec.P1_2_5 := by
  intro d g
  exact ⟨fun Ua Ub y ha hb => ismailRoe_tadmor g Ua Ub y ha hb,
    fun Ua Ub y => ismailRoe_symm g Ua Ub y,
    fun Ua Ub => ismailRoe_linear g Ua Ub,
    fun U y hU => ismailRoe_consistent g U y hU⟩

end CFDLean.JST1.Proofs
