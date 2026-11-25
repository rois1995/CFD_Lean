import CFDLean.Papers.JST1.Proofs.MeshAlgebra

noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

/-- Channels split as mass, momenta, energy. -/
def channelEquiv (d : ℕ) : Channel d ≃ Unit ⊕ (Fin d ⊕ Unit) where
  toFun c := match c with
    | .mass => .inl ()
    | .momentum α => .inr (.inl α)
    | .energy => .inr (.inr ())
  invFun s := match s with
    | .inl _ => .mass
    | .inr (.inl α) => .momentum α
    | .inr (.inr _) => .energy
  left_inv c := by cases c <;> rfl
  right_inv s := by rcases s with _ | _ | _ <;> rfl

theorem sum_channel {d : ℕ} {X : Type} [AddCommMonoid X] (f : Channel d → X) :
    (∑ c, f c) = f .mass + (∑ α, f (.momentum α)) + f .energy := by
  rw [← (channelEquiv d).symm.sum_comp]
  simp [Fintype.sum_sum_type, channelEquiv, add_assoc]

section
variable {d : ℕ} (P : ViscParams) (wb : State d)

def thetaF : ℝ := -wb .energy
def vF (α : Fin d) : ℝ := wb (.momentum α) / thetaF wb
def DvF (G : Matrix (Channel d) (Fin d) ℝ) (α β : Fin d) : ℝ :=
  (G (.momentum α) β - vF wb α * -G .energy β) / thetaF wb
def DTF (G : Matrix (Channel d) (Fin d) ℝ) (β : Fin d) : ℝ := -(-G .energy β) / (P.R * thetaF wb ^ 2)
def tauF (G : Matrix (Channel d) (Fin d) ℝ) (α β : Fin d) : ℝ :=
  P.μ * (DvF wb G α β + DvF wb G β α) - (2 / 3) * P.μ * (∑ γ, DvF wb G γ γ) * (if α = β then 1 else 0)

theorem viscFlux_mass (G) (β : Fin d) : viscFlux P wb G .mass β = 0 := rfl
theorem viscFlux_mom (G) (α β : Fin d) : viscFlux P wb G (.momentum α) β = tauF P wb G α β := rfl
theorem viscFlux_energy (G) (β : Fin d) :
    viscFlux P wb G .energy β = (∑ α, tauF P wb G β α * vF wb α) + P.κ * DTF P wb G β := rfl

theorem tauF_symm (G) (α β : Fin d) : tauF P wb G α β = tauF P wb G β α := by
  unfold tauF; rw [eq_comm]; by_cases h : α = β
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; ring

/-- `G : K(w̄) H = θ Σ Dv_G τ_H + κ Σ G_E DT_H`. -/
theorem frob_visc (G H : Matrix (Channel d) (Fin d) ℝ) (hθ : thetaF wb ≠ 0) :
    frob G (viscFlux P wb H) =
      thetaF wb * (∑ α, ∑ β, DvF wb G α β * tauF P wb H α β) + P.κ * ∑ β, G .energy β * DTF P wb H β := by
  unfold frob
  rw [sum_channel]
  simp only [viscFlux_mass, viscFlux_mom, viscFlux_energy, mul_zero, Finset.sum_const_zero, zero_add]
  have hG : ∀ α β, G (.momentum α) β = thetaF wb * DvF wb G α β + vF wb α * -G .energy β := by
    intro α β; unfold DvF; field_simp; ring
  simp only [hG, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  have hcancel : (∑ α, ∑ β, vF wb α * -G .energy β * tauF P wb H α β) +
      ∑ β, ∑ α, G .energy β * (tauF P wb H β α * vF wb α) = 0 := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [tauF_symm P wb H β α]; ring
  have e1 : ∀ α β, thetaF wb * DvF wb G α β * tauF P wb H α β =
      thetaF wb * (DvF wb G α β * tauF P wb H α β) := fun _ _ => by ring
  have e2 : ∀ β, G .energy β * (P.κ * DTF P wb H β) = P.κ * (G .energy β * DTF P wb H β) := fun _ => by ring
  simp only [e1, e2]
  linear_combination hcancel

/-- Pure algebra: `Σ D(D + Dᵀ) - (2/3)(tr D)² ≥ 0` for `d ≤ 3`. -/
theorem quad_nonneg (D : Fin d → Fin d → ℝ) (hd : d ≤ 3) :
    0 ≤ (∑ α, ∑ β, D α β * (D α β + D β α)) - (2 / 3) * (∑ γ, D γ γ) ^ 2 := by
  have hsym : (∑ α, ∑ β, D β α * (D α β + D β α)) = ∑ α, ∑ β, D α β * (D α β + D β α) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hsq : (∑ α, ∑ β, (D α β + D β α) ^ 2) = 2 * ∑ α, ∑ β, D α β * (D α β + D β α) := by
    calc (∑ α, ∑ β, (D α β + D β α) ^ 2)
        = ∑ α, ∑ β, (D α β * (D α β + D β α) + D β α * (D α β + D β α)) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = (∑ α, ∑ β, D α β * (D α β + D β α)) + ∑ α, ∑ β, D β α * (D α β + D β α) := by
          simp only [Finset.sum_add_distrib]
      _ = 2 * ∑ α, ∑ β, D α β * (D α β + D β α) := by rw [hsym]; ring
  have hdiagle : (∑ γ, (2 * D γ γ) ^ 2) ≤ ∑ α, ∑ β, (D α β + D β α) ^ 2 := by
    refine Finset.sum_le_sum fun α _ => ?_
    have := Finset.single_le_sum (f := fun β => (D α β + D β α) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ α)
    simpa [two_mul] using this
  have hcs : (∑ γ, D γ γ) ^ 2 ≤ (d : ℝ) * ∑ γ, D γ γ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun γ => D γ γ)
    simpa using this
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd
  have h4 : (∑ γ, (2 * D γ γ) ^ 2) = 4 * ∑ γ, D γ γ ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hS : 0 ≤ ∑ γ, D γ γ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hd' hS]

theorem tau_form (D : Fin d → Fin d → ℝ) (μ : ℝ) :
    (∑ α, ∑ β, D α β * (μ * (D α β + D β α) - (2 / 3) * μ * (∑ γ, D γ γ) * (if α = β then 1 else 0))) =
      μ * ((∑ α, ∑ β, D α β * (D α β + D β α)) - (2 / 3) * (∑ γ, D γ γ) ^ 2) := by
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · have h : ∀ x, ∑ i, D x x * (2 / 3 * μ * D i i) = D x x * (2 / 3 * μ) * ∑ i, D i i := fun x => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [h, ← Finset.sum_mul]
    ring

theorem dissip_nonneg (hd : d ≤ 3) (hμ : 0 ≤ P.μ) (G) :
    0 ≤ ∑ α, ∑ β, DvF wb G α β * tauF P wb G α β := by
  unfold tauF
  rw [tau_form]
  exact mul_nonneg hμ (quad_nonneg _ hd)

theorem DvF_add (G H) (α β : Fin d) : DvF wb (G + H) α β = DvF wb G α β + DvF wb H α β := by
  unfold DvF; simp only [Matrix.add_apply]; ring
theorem DvF_smul (c : ℝ) (G) (α β : Fin d) : DvF wb (c • G) α β = c * DvF wb G α β := by
  unfold DvF; simp only [Matrix.smul_apply, smul_eq_mul]; ring
theorem DTF_add (G H) (β : Fin d) : DTF P wb (G + H) β = DTF P wb G β + DTF P wb H β := by
  unfold DTF; simp only [Matrix.add_apply]; ring
theorem DTF_smul (c : ℝ) (G) (β : Fin d) : DTF P wb (c • G) β = c * DTF P wb G β := by
  unfold DTF; simp only [Matrix.smul_apply, smul_eq_mul]; ring
theorem tauF_add (G H) (α β : Fin d) : tauF P wb (G + H) α β = tauF P wb G α β + tauF P wb H α β := by
  unfold tauF; simp only [DvF_add, Finset.sum_add_distrib]; ring
theorem tauF_smul (c : ℝ) (G) (α β : Fin d) : tauF P wb (c • G) α β = c * tauF P wb G α β := by
  unfold tauF; simp only [DvF_smul, ← Finset.mul_sum]; ring
end

theorem p1_4_3b : Spec.P1_4_3b := by
  intro d g U ⟨hr, hp⟩
  show -(rho U) / pressure g U < 0
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hr) hp

theorem p1_4_2 : Spec.P1_4_2 := by
  intro d P wb hd hμ hκ hR hE
  have hθ : 0 < thetaF wb := by unfold thetaF; linarith
  refine ⟨fun G => ?_, ?_⟩
  · rw [frob_visc P wb G G hθ.ne']
    apply add_nonneg (mul_nonneg hθ.le (dissip_nonneg P wb hd hμ G))
    apply mul_nonneg hκ
    refine Finset.sum_nonneg fun β _ => ?_
    unfold DTF
    rw [neg_neg, ← mul_div_assoc, ← sq]
    exact div_nonneg (sq_nonneg _) (by positivity)
  · constructor
    · intro G H; ext c β
      cases c with
      | mass => simp only [Matrix.add_apply, viscFlux_mass, add_zero]
      | momentum α => simp only [Matrix.add_apply, viscFlux_mom, tauF_add]
      | energy =>
        simp only [Matrix.add_apply, viscFlux_energy, tauF_add, DTF_add, add_mul, Finset.sum_add_distrib]
        ring
    · intro c G; ext ch β
      cases ch with
      | mass => simp only [Matrix.smul_apply, viscFlux_mass, smul_eq_mul, mul_zero]
      | momentum α => simp only [Matrix.smul_apply, viscFlux_mom, tauF_smul, smul_eq_mul]
      | energy =>
        simp only [Matrix.smul_apply, viscFlux_energy, tauF_smul, DTF_smul, smul_eq_mul, mul_assoc,
          ← Finset.mul_sum]
        ring

theorem p1_4_4 : Spec.P1_4_4 := by
  intro d P wb G H hE
  have hθ : thetaF wb ≠ 0 := by unfold thetaF; exact neg_ne_zero.mpr hE
  rw [frob_visc P wb G H hθ, frob_visc P wb H G hθ]
  congr 1
  · congr 1
    unfold tauF
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have h1 : (∑ α, ∑ β, DvF wb G α β * (P.μ * DvF wb H β α)) = ∑ α, ∑ β, DvF wb H α β * (P.μ * DvF wb G β α) := by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h2 : (∑ α, ∑ β, DvF wb G α β * (P.μ * DvF wb H α β)) = ∑ α, ∑ β, DvF wb H α β * (P.μ * DvF wb G α β) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h1, h2]
    simp only [← Finset.sum_mul]
    ring
  · congr 1
    refine Finset.sum_congr rfl fun β _ => ?_
    unfold DTF; ring

theorem p1_4_3 : Spec.P1_4_3 := by
  intro ι C _ _ _ d M P w hM hd hμ hκ hR hE wbar Fl
  have hbar : ∀ T, wbar T .energy < 0 := by
    intro T
    simp only [wbar, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    apply mul_neg_of_pos_of_neg (by positivity)
    have := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun a => w (M.vert T a) .energy) (g := fun _ => (0 : ℝ)) Finset.univ_nonempty
      (fun a _ => hE _)
    simpa using this
  have hid := p1_4_1 ι C (Channel d) d M w Fl
  refine ⟨hbar, hid, ?_⟩
  rw [hid, neg_nonpos]
  refine Finset.sum_nonneg fun T _ => ?_
  have hvol : 0 ≤ M.vol T := by
    unfold WMesh.vol Simplex.vol
    exact div_nonneg (abs_nonneg _) (by positivity)
  exact mul_nonneg (mul_nonneg (hM.1 T) hvol) ((p1_4_2 d P (wbar T) hd hμ hκ hR (hbar T)).1 _)

theorem p1_4_0 : Spec.P1_4_0 := by
  intro d g P r T v hr hT hR
  have hg : g.γ - 1 ≠ 0 := by have := g.one_lt_γ; linarith
  have hRT : P.R * T ≠ 0 := mul_ne_zero hR.ne' hT.ne'
  set p := r * P.R * T with hpdef
  have hp : pressure g (primState g r v p) = p := by
    simp only [pressure, primState, energy, mom, rho, Num.dot]
    have : (∑ x, r * v x * (r * v x)) = r * (r * ∑ x, v x * v x) := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this]
    field_simp
    ring
  have hvel : ∀ α, vel (primState g r v p) α = v α := by
    intro α; simp only [vel, mom, rho, primState]; field_simp
  have hmom : ∀ α, entropyVars g (primState g r v p) (.momentum α) = v α / (P.R * T) := by
    intro α
    show rho (primState g r v p) * vel (primState g r v p) α / pressure g (primState g r v p) = _
    rw [hp, hvel]
    simp only [rho, primState, hpdef]
    field_simp
  have hen : entropyVars g (primState g r v p) .energy = -1 / (P.R * T) := by
    show -(rho (primState g r v p)) / pressure g (primState g r v p) = _
    rw [hp]
    simp only [rho, primState, hpdef]
    field_simp
  refine ⟨hmom, hen, ?_⟩
  intro Gv GT G hGm hGE
  set wb := entropyVars g (primState g r v p)
  have hθ : thetaF wb = 1 / (P.R * T) := by
    unfold thetaF; rw [hen]; ring
  have hv : ∀ α, vF wb α = v α := by
    intro α; unfold vF; rw [hmom, hθ]; field_simp
  have hDv : ∀ α β, DvF wb G α β = Gv α β := by
    intro α β; unfold DvF; rw [hv, hθ, hGm, hGE]; field_simp; ring
  have hDT : ∀ β, DTF P wb G β = GT β := by
    intro β; unfold DTF; rw [hθ, hGE]; field_simp
  ext c β
  cases c with
  | mass => rfl
  | momentum α =>
    rw [viscFlux_mom]
    unfold tauF
    simp only [hDv]
    rfl
  | energy =>
    rw [viscFlux_energy]
    unfold tauF
    simp only [hDv, hv, hDT]
    rfl

end CFDLean.JST1.Proofs
