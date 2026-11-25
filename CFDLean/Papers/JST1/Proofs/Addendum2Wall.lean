import CFDLean.Papers.JST1.Spec.Addendum2
import CFDLean.Papers.JST1.Proofs.Item9
import CFDLean.Papers.JST1.Proofs.Item10

/-! Proofs of P2-9.2b (`thm:wall` sharpness with `K = K(w̄_T)` of the witness itself) and P2-10.8b (`thm:sst`
with the element operators). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num

namespace CFDLean.JST1.Proofs
namespace Ad2W
open CFDLean.JST1.Wall Wl9

/-- The vertex mean of admissible values is admissible. -/
theorem vmean_neg {d : ℕ} (w : Fin (d + 1) → State d) (hw : ∀ a, w a .energy < 0) :
    Spec.vmean w .energy < 0 := by
  simp only [Spec.vmean, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  apply mul_neg_of_pos_of_neg (by positivity)
  have := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin (d + 1))))
    (f := fun a => w a .energy) (g := fun _ => (0 : ℝ)) Finset.univ_nonempty (fun a _ => hw a)
  simpa using this

/-- Nodal jump of the sharpness witness. -/
def sV {d : ℕ} (T : Simplex d) (o : Fin (d + 1)) : ℝ := -(area T o / T.vol) / len (T.grad o)

/-- Sharpness witness `w_a = b + e + [a = o] s e` (the P2-9.2 witness with a base state `b`). -/
def wit {κ : Type} {d : ℕ} (T : Simplex d) (o : Fin (d + 1)) (e b : κ → ℝ) : Fin (d + 1) → κ → ℝ :=
  fun a => b + e + (if a = o then sV T o else 0) • e

/-- The computation of P2-9.2 for any linear `K`: `D^gal - Π^w = (c - 1) A_f² |e ⊗ N_f|²_K / |T|`. -/
theorem sharp_core {κ : Type} [Fintype κ] {d : ℕ} (T : Simplex d)
    (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (hK : IsLinearMap ℝ K) (P : Matrix κ κ ℝ) (gw : κ → ℝ)
    (o : Fin (d + 1)) (c : ℝ) (e b : κ → ℝ) (hd : 1 ≤ d) (hT : T.Nondeg) (hPe : P.mulVec (b + e - gw) = e) :
    Dgal T K (wit T o e b) - PiW T K P gw {o} c (wit T o e b) =
      (c - 1) * (area T o ^ 2 * frob (outerK e (normal T o)) (K (outerK e (normal T o))) / T.vol) := by
  have hvol : 0 < T.vol := (p1_5_1 d T hT).2.2.2.1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hL : 0 < len (T.grad o) := Real.sqrt_pos.2 (grad_dot_pos T hd hT o)
  have hA : 0 < area T o := by unfold area; positivity
  set N := normal T o with hN
  set z := frob (outerK e N) (K (outerK e N)) with hzdef
  set τ := area T o / T.vol with hτ
  set s := sV T o with hs
  have hs' : s = -τ / len (T.grad o) := rfl
  set w := wit T o e b with hwdef
  have hgsum : ∀ α, ∑ a, T.grad a α = 0 := by
    intro α
    have := congrFun (p1_5_1 d T hT).1 α
    simpa [Finset.sum_apply] using this
  have hG : gradT T w = τ • outerK e N := by
    funext r α
    have e1 : gradT T w r α = ∑ a, w a r * T.grad a α := by
      unfold gradT
      rw [Matrix.sum_apply]
      rfl
    have e2 : ∀ a, w a r * T.grad a α =
        (b r + e r) * T.grad a α + (if o = a then s * e r * T.grad o α else 0) := by
      intro a
      by_cases h : a = o
      · subst h; simp [w, wit, ← hs]; ring
      · simp [w, wit, h, Ne.symm h]
    rw [e1, Finset.sum_congr rfl fun a _ => e2 a, Finset.sum_add_distrib, ← Finset.mul_sum, hgsum,
      Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true, mul_zero, zero_add, Matrix.smul_apply, smul_eq_mul, outerK, hN,
      normal, Pi.smul_apply, hs']
    ring
  have hE : ∀ a ∈ Finset.univ.erase o, eW P gw w a = e := by
    intro a ha
    have h : a ≠ o := Finset.ne_of_mem_erase ha
    unfold eW
    have : w a - gw = b + e - gw := by funext r; simp [w, wit, h]
    rw [this, hPe]
  let L := IsLinearMap.mk' K hK
  have hKs : K (τ • outerK e N) = τ • K (outerK e N) := map_smul L τ (outerK e N)
  have hcard : (Finset.univ.erase o).card = d := by simp [Finset.card_erase_of_mem]
  have hDg : Dgal T K w = T.vol * (τ * (τ * z)) := by
    unfold Dgal
    rw [hG, hKs, frob_smul_l, frob_smul_r]
  have hσv : sigmaF T {o} c o * T.vol = c * area T o := by
    unfold sigmaF hf
    rw [div_div_eq_mul_div, Finset.card_singleton]
    field_simp
    ring
  have hPi : PiW T K P gw {o} c w = 2 * area T o * (τ * z) - sigmaF T {o} c o * (area T o * z) := by
    unfold PiW Xf
    rw [Finset.sum_singleton,
      Finset.sum_congr rfl (g := fun _ => pairF e ((K (gradT T w)).mulVec (normal T o)))
        fun a ha => by rw [hE a ha],
      Finset.sum_congr rfl (f := fun a => frob (outerK (eW P gw w a) (normal T o))
          (K (outerK (eW P gw w a) (normal T o))))
        (g := fun _ => frob (outerK e (normal T o)) (K (outerK e (normal T o))))
        fun a ha => by rw [hE a ha]]
    simp only [Finset.sum_const, hcard, nsmul_eq_mul, ← hN, ← frob_outer, hG, hKs, frob_smul_r, ← hzdef]
    field_simp
  rw [hDg, hPi]
  have hσ : sigmaF T {o} c o = c * area T o / T.vol := by
    field_simp
    linarith [hσv]
  rw [hσ, hτ]
  field_simp
  ring

/-- Momentum unit vector. -/
def munit {d : ℕ} (α0 : Fin d) : State d := fun ch => if ch = .momentum α0 then 1 else 0

/-- Energy base state `-e_E`. -/
def ebase {d : ℕ} : State d := fun ch => if ch = .energy then -1 else 0

/-- `|e_{α0} ⊗ N|²_{K(w̄)} > 0` for every admissible `w̄` (independent of the velocity of `w̄`). -/
theorem zpos {d : ℕ} (Pv : ViscParams) (wb : State d) (N : Vec d) (α0 : Fin d) (hα0 : N α0 ≠ 0)
    (hμ : 0 < Pv.μ) (hE : wb .energy < 0) :
    0 < frob (outerK (munit α0) N) (viscFlux Pv wb (outerK (munit α0) N)) := by
  have hθ : 0 < thetaF wb := by unfold thetaF; linarith
  rw [frob_visc Pv wb _ _ hθ.ne']
  have hGE : ∀ β, outerK (munit α0) N .energy β = 0 := fun β => by simp [outerK, munit]
  have hD : ∀ α β, DvF wb (outerK (munit α0) N) α β = if α = α0 then N β / thetaF wb else 0 := by
    intro α β
    unfold DvF
    rw [hGE]
    by_cases h : α = α0
    · subst h; simp [outerK, munit]
    · simp [outerK, munit, h]
  simp only [hGE, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  unfold tauF
  rw [tau_form]
  simp only [hD]
  set θ := thetaF wb
  have htr : (∑ x, if x = α0 then N x / θ else 0) = N α0 / θ := by
    rw [Finset.sum_ite_eq']; simp
  have hsum : (∑ x, ∑ x_1, (if x = α0 then N x_1 / θ else 0) *
      ((if x = α0 then N x_1 / θ else 0) + if x_1 = α0 then N x / θ else 0)) =
      (∑ β, (N β / θ) ^ 2) + (N α0 / θ) ^ 2 := by
    rw [Finset.sum_eq_single α0 (fun α _ h => by simp [h]) (by simp)]
    simp only [ite_true, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, sq]
  rw [htr, hsum]
  have hS : 0 ≤ ∑ β, (N β / θ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha : 0 < (N α0 / θ) ^ 2 := by
    have : N α0 / θ ≠ 0 := div_ne_zero hα0 hθ.ne'
    positivity
  have : 0 < (∑ β, (N β / θ) ^ 2) + (N α0 / θ) ^ 2 - 2 / 3 * (N α0 / θ) ^ 2 := by linarith
  positivity

end Ad2W

open Ad2W Wl9 CFDLean.JST1.Wall

theorem p2_9_2b : Spec.P2_9_2b := by
  intro d Pv T o c hd hd3 hμ hκ hR hT _ hc1
  have hvol : 0 < T.vol := (p1_5_1 d T hT).2.2.2.1
  have hL : 0 < len (T.grad o) := Real.sqrt_pos.2 (grad_dot_pos T hd hT o)
  have hA : 0 < area T o := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    unfold area; positivity
  obtain ⟨α0, hα0⟩ : ∃ α, normal T o α ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hg : ∀ α, T.grad o α = 0 := by
      intro α
      have h := hcon α
      simp only [normal, Pi.smul_apply, smul_eq_mul, mul_eq_zero, neg_eq_zero, one_div, inv_eq_zero] at h
      rcases h with h | h
      · exact absurd h hL.ne'
      · exact h
    have := grad_dot_pos T hd hT o
    simp [Num.dot, hg] at this
  have hwE : ∀ a, wit T o (munit α0) ebase a .energy < 0 := by
    intro a
    by_cases h : a = o <;> simp [wit, munit, ebase, h]
  have hbar := vmean_neg _ hwE
  refine ⟨wit T o (munit α0) ebase, hwE, ?_⟩
  have hPe : (Spec.momProj d).mulVec (ebase + munit α0 - 0) = munit α0 := by
    funext ch
    unfold Spec.momProj
    rw [Matrix.mulVec_diagonal]
    cases ch <;> simp [ebase, munit]
  rw [sharp_core T _ (p2_9_3 d Pv _ (normal T o) hd hd3 hμ hκ hR hbar (fun h => hα0 (by simp [h]))).1.1
    (Spec.momProj d) 0 o c (munit α0) ebase hd hT hPe]
  exact mul_neg_of_neg_of_pos (by linarith)
    (div_pos (mul_pos (pow_pos hA 2) (zpos Pv _ _ α0 hα0 hμ hbar)) hvol)

theorem p2_10_8b : Spec.P2_10_8b := by
  intro d T R μ μt κ c P gw walls w hd hd3 hR hμ hμt hκ hT hc hw hPT hPP hPg K Kt Dg Dt Pw
  have hvol : 0 < T.vol := (p1_5_1 d T hT).2.2.2.1
  have hbar := vmean_neg w hw
  have h42 := p1_4_2 d ⟨R, μ + μt, κ⟩ (Spec.vmean w) hd3 (add_nonneg hμ hμt) hκ hR hbar
  have hWH : Spec.WallHyp K P gw :=
    ⟨h42.2, fun G H => p1_4_4 d _ _ G H hbar.ne, h42.1, hPT, hPP, hPg⟩
  have h7 := p2_10_7 d R μ μt κ (Spec.vmean w) (gradT T w) hd3 hR hμ hμt hκ hbar
  have hDg : Dg = T.vol * frob (gradT T w) (viscFlux ⟨R, μ, κ⟩ (Spec.vmean w) (gradT T w)) + Dt := by
    show T.vol * frob (gradT T w) (K (gradT T w)) = _
    rw [h7.1]
    show _ = _ + T.vol * frob (gradT T w) (Kt (gradT T w))
    ring
  have hDt : 0 ≤ Dt := mul_nonneg hvol.le h7.2.2
  have hlam : 0 ≤ T.vol * frob (gradT T w) (viscFlux ⟨R, μ, κ⟩ (Spec.vmean w) (gradT T w)) :=
    mul_nonneg hvol.le h7.2.1
  refine ⟨hDt, by linarith, fun hw0 => ?_, fun _ hle => ?_⟩
  · have hP0 : Pw = 0 := by
      show PiW T K P gw walls c w = 0
      subst hw0
      simp [PiW]
    exact ⟨hP0, by linarith⟩
  · have h91 := (p2_9_1 (Channel d) d T K P gw walls c w hWH hd hT hc).1
    have : (1 - 1 / c) * Dg = Dg - Dg / c := by ring
    show Pw ≤ Dg - Dt
    linarith

end CFDLean.JST1.Proofs
