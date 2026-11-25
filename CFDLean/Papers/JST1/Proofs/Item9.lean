import CFDLean.Papers.JST1.Spec.Item9
import CFDLean.Papers.JST1.Proofs.Simplex
import CFDLean.Papers.JST1.Proofs.Viscous

/-! Proofs of item 9 (P2): `thm:wall` (paper lines 336-346, proof 1067-1090), on one simplex. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num

namespace CFDLean.JST1.Proofs
namespace Wl9
open CFDLean.JST1.Wall

/-! ### Bilinear algebra of `pairF` and `frob` -/

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

theorem pr_neg (x y : κ → ℝ) : pairF x (-y) = -pairF x y := by
  simp only [pairF, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem pl_add (x y z : κ → ℝ) : pairF (x + y) z = pairF x z + pairF y z := by
  simp only [pairF, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pr_ite (x y : κ → ℝ) (p : Prop) [Decidable p] :
    pairF x (if p then y else 0) = if p then pairF x y else 0 := by
  split_ifs <;> simp [pairF]

/-- `y · P x = (P y) · x` for a symmetric `P`. -/
theorem pr_symm (P : Matrix κ κ ℝ) (hP : P.transpose = P) (x y : κ → ℝ) :
    pairF y (P.mulVec x) = pairF (P.mulVec y) x := by
  show dotProduct y (P.mulVec x) = dotProduct (P.mulVec y) x
  rw [Matrix.dotProduct_mulVec, ← hP, Matrix.vecMul_transpose, hP]

variable {ι : Type} [Fintype ι]

theorem frob_add_l (A B C : Matrix κ ι ℝ) : frob (A + B) C = frob A C + frob B C := by
  simp only [frob, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem frob_add_r (A B C : Matrix κ ι ℝ) : frob A (B + C) = frob A B + frob A C := by
  simp only [frob, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem frob_sub_l (A B C : Matrix κ ι ℝ) : frob (A - B) C = frob A C - frob B C := by
  simp only [frob, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem frob_sub_r (A B C : Matrix κ ι ℝ) : frob A (B - C) = frob A B - frob A C := by
  simp only [frob, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem frob_smul_l (c : ℝ) (A B : Matrix κ ι ℝ) : frob (c • A) B = c * frob A B := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem frob_smul_r (c : ℝ) (A B : Matrix κ ι ℝ) : frob A (c • B) = c * frob A B := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem frob_sum_l {Q : Type} (s : Finset Q) (A : Q → Matrix κ ι ℝ) (B : Matrix κ ι ℝ) :
    frob (∑ q ∈ s, A q) B = ∑ q ∈ s, frob (A q) B := by
  unfold frob
  have h : ∀ r c', (∑ q ∈ s, A q : Matrix κ ι ℝ) r c' = ∑ q ∈ s, A q r c' := fun r c' => Matrix.sum_apply r c' s A
  simp only [h, Finset.sum_mul]
  calc _ = ∑ r, ∑ q ∈ s, ∑ c', A q r c' * B r c' := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

end

section
variable {κ : Type} [Fintype κ] {d : ℕ}

theorem frob_outer (e : κ → ℝ) (N : Vec d) (M : Matrix κ (Fin d) ℝ) :
    frob (outerK e N) M = pairF e (M.mulVec N) := by
  simp only [frob, outerK, pairF, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem frob_grad (T : Simplex d) (w : Fin (d + 1) → κ → ℝ) (M : Matrix κ (Fin d) ℝ) :
    frob (gradT T w) M = ∑ b, pairF (w b) (M.mulVec (T.grad b)) := by
  unfold gradT
  rw [frob_sum_l]
  simp only [frob_outer]

/-- The node inequality behind the two Cauchy-Schwarz steps and Young: `0 ≤ |σ Y - G|²_K`. -/
theorem node_bound (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (hK : IsLinearMap ℝ K)
    (hS : ∀ G H, frob G (K H) = frob H (K G)) (hP : ∀ G, 0 ≤ frob G (K G))
    (σ : ℝ) (Y G : Matrix κ (Fin d) ℝ) :
    σ * (2 * frob Y (K G) - σ * frob Y (K Y)) ≤ frob G (K G) := by
  let L := IsLinearMap.mk' K hK
  have hL : ∀ X, L X = K X := fun _ => rfl
  have h := hP (σ • Y - G)
  rw [← hL, map_sub, map_smul, hL, hL, frob_sub_l, frob_sub_r, frob_sub_r, frob_smul_l, frob_smul_l,
    frob_smul_r, frob_smul_r, hS G Y] at h
  nlinarith [h]

/-- `x · F̂_a` splits into the consistency, penalty and data parts. -/
theorem fhat_pair (T : Simplex d) (K : Matrix κ (Fin d) ℝ → Matrix κ (Fin d) ℝ) (P : Matrix κ κ ℝ)
    (gw : κ → ℝ) (walls : Finset (Fin (d + 1))) (c : ℝ) (w : Fin (d + 1) → κ → ℝ) (o b : Fin (d + 1))
    (hPT : P.transpose = P) (hPP : P * P = P) :
    pairF (w b) (Fhat T K P gw walls c w o b) =
      pairF (eW P gw w b) ((K (gradT T w)).mulVec (normal T o)) -
        sigmaF T walls c o * frob (outerK (eW P gw w b) (normal T o)) (K (outerK (eW P gw w b) (normal T o))) +
        pairF gw (Fhat T K P gw walls c w o b) := by
  have hPe : P.mulVec (eW P gw w b) = eW P gw w b := by
    unfold eW
    rw [Matrix.mulVec_mulVec, hPP]
  have hw : w b = (w b - gw) + gw := by abel
  conv_lhs => rw [hw]
  rw [pl_add]
  unfold Fhat
  rw [pr_sub (w b - gw), pr_smul, pr_symm P hPT, pr_symm P hPT, hPe, frob_outer]
  rfl

/-- `g_o ≠ 0` on a nondegenerate simplex. -/
theorem grad_dot_pos (T : Simplex d) (hd : 1 ≤ d) (hT : T.Nondeg) (o : Fin (d + 1)) :
    0 < Num.dot (T.grad o) (T.grad o) := by
  obtain ⟨c', hc'⟩ := Fintype.exists_ne_of_one_lt_card (by simp; omega : 1 < Fintype.card (Fin (d + 1))) o
  have h1 := (p1_5_1 d T hT).2.1 o o c'
  rw [ite_eq_left rfl, ite_eq_right (Ne.symm hc')] at h1
  by_contra hneg
  have h0 : Num.dot (T.grad o) (T.grad o) = 0 :=
    le_antisymm (not_lt.1 hneg) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
  have hz : ∀ α, T.grad o α = 0 := by
    intro α
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_self_nonneg _)).1 h0 α (Finset.mem_univ _)
    exact mul_self_eq_zero.1 this
  simp [Num.dot, hz] at h1

end

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

end

end Wl9

open Wl9 CFDLean.JST1.Wall

/-! ### P2-9.0: balance -/

theorem p2_9_0 : Spec.P2_9_0 := by
  intro κ _ d T K P gw walls c w ⟨_, hS, _, hPT, hPP, _⟩
  have hvisc : ∑ b, pairF (w b) (Rvisc T K w b) = -Dgal T K w := by
    unfold Rvisc Dgal
    simp only [pr_neg, pr_smul, Finset.sum_neg_distrib, ← Finset.mul_sum, frob_grad]
  have hface : ∀ o, ∑ b, pairF (w b) ((if b ≠ o then (area T o / d) • Fhat T K P gw walls c w o b else 0) +
      (K ((area T o / d) • ∑ a ∈ Finset.univ.erase o, outerK (eW P gw w a) (normal T o))).mulVec (T.grad b)) =
      (2 * (area T o / d) * ∑ a ∈ Finset.univ.erase o,
          pairF (eW P gw w a) ((K (gradT T w)).mulVec (normal T o)) - sigmaF T walls c o * Xf T K P gw w o) +
        area T o / d * ∑ a ∈ Finset.univ.erase o, pairF gw (Fhat T K P gw walls c w o a) := by
    intro o
    simp only [pr_add, Finset.sum_add_distrib, pr_ite]
    rw [← frob_grad, hS, frob_smul_l, frob_sum_l, ← Finset.sum_filter, Finset.filter_ne']
    simp only [pr_smul, frob_outer, fhat_pair T K P gw walls c w o _ hPT hPP]
    unfold Xf
    simp only [frob_outer]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  calc ∑ b, pairF (w b) (Rvisc T K w b + Rwall T K P gw walls c w b)
      = ∑ b, pairF (w b) (Rvisc T K w b) + ∑ b, pairF (w b) (Rwall T K P gw walls c w b) := by
        simp only [pr_add, Finset.sum_add_distrib]
    _ = _ := by
        rw [hvisc]
        unfold Rwall
        simp only [pr_sum]
        rw [Finset.sum_comm]
        simp only [hface]
        unfold PiW
        rw [Finset.sum_add_distrib]
        ring


/-! ### P2-9.1: wall production bounded by the Galerkin dissipation -/

theorem p2_9_1 : Spec.P2_9_1 := by
  intro κ _ d T K P gw walls c w ⟨hK, hS, hPSD, _, _, _⟩ hd hT hc
  have hvol : 0 < T.vol := (p1_5_1 d T hT).2.2.2.1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hQ0 : 0 ≤ frob (gradT T w) (K (gradT T w)) := hPSD _
  have hD : Dgal T K w = T.vol * frob (gradT T w) (K (gradT T w)) := rfl
  have hD0 : 0 ≤ Dgal T K w := by rw [hD]; positivity
  have hface : ∀ o ∈ walls, 2 * (area T o / d) * ∑ a ∈ Finset.univ.erase o,
        pairF (eW P gw w a) ((K (gradT T w)).mulVec (normal T o)) - sigmaF T walls c o * Xf T K P gw w o ≤
      Dgal T K w / (c * walls.card) := by
    intro o ho
    have hn0 : (0 : ℝ) < walls.card := by exact_mod_cast Finset.card_pos.2 ⟨o, ho⟩
    have hσv : sigmaF T walls c o * T.vol = c * walls.card * area T o := by
      unfold sigmaF hf
      rw [div_div_eq_mul_div]
      field_simp
    have hnode : ∀ a, sigmaF T walls c o * (2 * pairF (eW P gw w a) ((K (gradT T w)).mulVec (normal T o)) -
        sigmaF T walls c o * frob (outerK (eW P gw w a) (normal T o)) (K (outerK (eW P gw w a) (normal T o)))) ≤
          frob (gradT T w) (K (gradT T w)) := by
      intro a
      rw [← frob_outer]
      exact node_bound K hK hS hPSD _ _ _
    have hcard : (Finset.univ.erase o).card = d := by simp [Finset.card_erase_of_mem]
    have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ.erase o) => hnode a
    rw [Finset.sum_const, hcard, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum] at hsum
    unfold Xf
    rw [hD, le_div_iff₀ (by positivity)]
    generalize (∑ a ∈ Finset.univ.erase o, pairF (eW P gw w a) ((K (gradT T w)).mulVec (normal T o))) = X at *
    generalize (∑ a ∈ Finset.univ.erase o,
      frob (outerK (eW P gw w a) (normal T o)) (K (outerK (eW P gw w a) (normal T o)))) = Y at *
    generalize sigmaF T walls c o = σ at *
    generalize frob (gradT T w) (K (gradT T w)) = Q at *
    calc (2 * (area T o / d) * X - σ * (area T o / d * Y)) * (c * walls.card)
        = (c * walls.card * area T o) * (2 * X - σ * Y) / d := by field_simp
      _ = T.vol * (σ * (2 * X - σ * Y)) / d := by rw [← hσv]; ring
      _ ≤ T.vol * (d * Q) / d := by gcongr
      _ = T.vol * Q := by field_simp
  have hPi : PiW T K P gw walls c w ≤ Dgal T K w / c := by
    unfold PiW
    calc _ ≤ ∑ o ∈ walls, Dgal T K w / (c * walls.card) := Finset.sum_le_sum hface
      _ = walls.card * (Dgal T K w / (c * walls.card)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Dgal T K w / c := by
        by_cases hn : (walls.card : ℝ) = 0
        · rw [hn, zero_mul]; positivity
        · apply le_of_eq
          field_simp
  refine ⟨hPi, fun hc1 => ⟨?_, ?_⟩⟩
  · have : (1 - 1 / c) * Dgal T K w = Dgal T K w - Dgal T K w / c := by ring
    linarith
  · have : 1 / c ≤ 1 := by rw [div_le_one hc]; exact hc1
    exact mul_nonneg (by linarith) hD0

/-! ### P2-9.2: `c ≥ 1` is sharp for one wall element -/

theorem p2_9_2 : Spec.P2_9_2 := by
  intro κ _ d T K P gw o c e ⟨hK, _, _, _, _, _⟩ hd hT hc hc1 hPe hz
  have hvol : 0 < T.vol := (p1_5_1 d T hT).2.2.2.1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hL : 0 < len (T.grad o) := Real.sqrt_pos.2 (grad_dot_pos T hd hT o)
  have hA : 0 < area T o := by unfold area; positivity
  set N := normal T o with hN
  set z := frob (outerK e N) (K (outerK e N)) with hzdef
  set τ := area T o / T.vol with hτ
  set s := -τ / len (T.grad o) with hs
  let w : Fin (d + 1) → κ → ℝ := fun a => gw + e + (if a = o then s else 0) • e
  refine ⟨w, ?_⟩
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
        (gw r + e r) * T.grad a α + (if o = a then s * e r * T.grad o α else 0) := by
      intro a
      by_cases h : a = o
      · subst h; simp [w]; ring
      · simp [w, h, Ne.symm h]
    rw [e1, Finset.sum_congr rfl fun a _ => e2 a, Finset.sum_add_distrib, ← Finset.mul_sum, hgsum,
      Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true, mul_zero, zero_add, Matrix.smul_apply, smul_eq_mul, outerK, hN,
      normal, Pi.smul_apply, hs]
    ring
  have hE : ∀ a ∈ Finset.univ.erase o, eW P gw w a = e := by
    intro a ha
    have h : a ≠ o := Finset.ne_of_mem_erase ha
    unfold eW
    have : w a - gw = e := by funext r; simp [w, h]
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
  have key : T.vol * (area T o / T.vol * (area T o / T.vol * z)) -
      (2 * area T o * (area T o / T.vol * z) - c * area T o / T.vol * (area T o * z)) =
      (c - 1) * (area T o ^ 2 * z / T.vol) := by
    field_simp
    ring
  rw [key]
  exact mul_neg_of_neg_of_pos (by linarith) (by positivity)

/-! ### P2-9.3: the Navier-Stokes `K(w̄)` and the momentum projector -/

theorem p2_9_3 : Spec.P2_9_3 := by
  intro d Pv wb N _ hd3 hμ hκ hR hE hN
  have h42 := p1_4_2 d Pv wb hd3 hμ.le hκ hR hE
  refine ⟨⟨h42.2, fun G H => p1_4_4 d Pv wb G H hE.ne, h42.1, ?_, ?_, ?_⟩, ?_⟩
  · exact Matrix.diagonal_transpose _
  · unfold Spec.momProj
    rw [Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun c => ?_)
    cases c <;> simp
  · exact Matrix.mulVec_zero _
  · obtain ⟨α0, hα0⟩ : ∃ α, N α ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hN (funext hcon)
    let e : State d := fun c => if c = .momentum α0 then 1 else 0
    refine ⟨e, ?_, ?_⟩
    · funext c
      unfold Spec.momProj
      rw [Matrix.mulVec_diagonal]
      cases c <;> simp [e]
    · have hθ : 0 < thetaF wb := by unfold thetaF; linarith
      rw [frob_visc Pv wb _ _ hθ.ne']
      have hGE : ∀ β, outerK e N .energy β = 0 := fun β => by simp [outerK, e]
      have hD : ∀ α β, DvF wb (outerK e N) α β = if α = α0 then N β / thetaF wb else 0 := by
        intro α β
        unfold DvF
        rw [hGE]
        by_cases h : α = α0
        · subst h; simp [outerK, e]
        · simp [outerK, e, h]
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

/-! ### P2-9.4: wall conditions in entropy variables -/

theorem p2_9_4 : Spec.P2_9_4 := by
  intro d g R r T Tw v hR hr hT hTw
  have hp := pressure_prim g hr.ne' v (r * R * T)
  have hv := vel_prim g hr.ne' v (r * R * T)
  have hrho : rho (primState g r v (r * R * T)) = r := rfl
  have hm : ∀ α, entropyVars g (primState g r v (r * R * T)) (.momentum α) = v α / (R * T) := by
    intro α
    simp only [entropyVars, hp, hv, hrho]
    field_simp
  have hE : entropyVars g (primState g r v (r * R * T)) .energy = -1 / (R * T) := by
    simp only [entropyVars, hp, hrho]
    field_simp
  refine ⟨?_, ?_⟩
  · simp only [hm]
    constructor
    · rintro rfl α
      simp
    · intro h
      funext α
      have := h α
      rw [div_eq_zero_iff] at this
      rcases this with h0 | h0
      · exact h0
      · exact absurd h0 (by positivity)
  · rw [hE]
    constructor
    · rintro rfl
      rfl
    · intro h
      have h' : R * T = R * Tw := by
        rw [neg_div, neg_div, neg_inj, one_div, one_div] at h
        exact inv_inj.1 h
      exact mul_left_cancel₀ hR.ne' h'

end CFDLean.JST1.Proofs
