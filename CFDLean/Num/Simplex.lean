import CFDLean.Num.Basic
set_option cleanup.letToHave false -- MC-N: keep the `let` binders of the moved JST definitions and statements

/-! A simplex of `ℝ^d` with its P1 barycentric gradients: simplex calculus (P1-5.1), 3D facet vectors as half cross
products and shared facets (P3-11.2), 2D facet vectors as rotated edges (P3-11.2b), Kuhn path simplices (P3-12.5),
and the 2D median-dual segment (used by P1-5.6).

MC-N: definitions moved verbatim from JST_Paper_Lean `NumCore/Simplex.lean`, `Paper1/Spec/Item11a.lean` (`cross3`),
`Paper1/Spec/Item11b.lean` (`perp2`), `Paper1/Spec/Item12.lean` (`pathSimplex`) and `Paper1/Geometry/Dual2D.lean`
(`rot90`, `dualFacet2`); proofs from `Paper1/Proofs/{MeshAlgebra,Simplex,GeomBase,DualFacets,Geom3,Item11b}.lean`. -/
noncomputable section
open scoped BigOperators
namespace CFDLean.Num

/-- A (possibly degenerate) simplex: `d+1` vertices in `ℝ^d`. -/
structure Simplex (d : ℕ) where
  x : Fin (d + 1) → Vec d

namespace Simplex
variable {d : ℕ}

/-- Edge matrix: column `β` is the edge `x (β+1) - x 0`. -/
def edgeMat (T : Simplex d) : Matrix (Fin d) (Fin d) ℝ := fun α β => T.x β.succ α - T.x 0 α

/-- Nondegenerate simplex. -/
def Nondeg (T : Simplex d) : Prop := T.edgeMat.det ≠ 0

/-- Barycentric gradient `g_a = ∇φ_a`: row `β` of the inverse edge matrix for `a = β+1`, and minus their sum
for `a = 0`. -/
def grad (T : Simplex d) (a : Fin (d + 1)) : Vec d :=
  Fin.cases (-(∑ β, fun α => T.edgeMat⁻¹ β α)) (fun β α => T.edgeMat⁻¹ β α) a

/-- Measure `|T| = |det| / d!`. -/
def vol (T : Simplex d) : ℝ := |T.edgeMat.det| / (Nat.factorial d)

/-- Outward area vector of the facet opposite vertex `o`: `-(d |T|) g_o`. -/
def facet (T : Simplex d) (o : Fin (d + 1)) : Vec d := (-((d : ℝ) * T.vol)) • T.grad o

/-- Centroid. -/
def centroid (T : Simplex d) : Vec d := (1 / ((d : ℝ) + 1)) • ∑ a, T.x a

end Simplex

/-- Cross product in `ℝ³`. -/
def cross3 (u v : Vec 3) : Vec 3 := ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- Rotation of a 2D vector by -90°. -/
def perp2 (v : Vec 2) : Vec 2 := ![v 1, -v 0]

/-- Path simplex of a brick: `x_0 = 0`, `x_{j+1} = x_j + h_{π j} e_{π j}` (a Kuhn tetrahedron). -/
def pathSimplex (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ) : Simplex 3 :=
  ⟨fun j => ∑ i : Fin 3, if i.val < j.val then h (π i) • (Pi.single (π i) (1 : ℝ) : Vec 3) else 0⟩

def rot90 (s : Vec 2) : Vec 2 := ![s 1, -s 0]

def dualFacet2 (T : Simplex 2) (i k : Fin 3) : Vec 2 :=
  let r := rot90 (T.centroid - (1 / 2 : ℝ) • (T.x i + T.x k))
  if 0 ≤ dot r (T.x k - T.x i) then r else -r

end CFDLean.Num

namespace CFDLean.Num.Internal

theorem grad_sum {d : ℕ} (T : Simplex d) : ∑ a, T.grad a = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [Simplex.grad, Fin.cases_zero, Fin.cases_succ]
  exact neg_add_cancel _

namespace SimplexCalc
variable {d : ℕ} (T : Simplex d)

theorem edge_col (β : Fin d) : T.x β.succ - T.x 0 = fun α => T.edgeMat α β := by
  funext α; simp [Simplex.edgeMat]

theorem grad_succ (γ : Fin d) : T.grad γ.succ = fun α => T.edgeMat⁻¹ γ α := by
  simp [Simplex.grad]

theorem grad_zero : T.grad 0 = -(∑ γ, fun α => T.edgeMat⁻¹ γ α) := by
  simp [Simplex.grad]

theorem inv_mul (h : T.Nondeg) (γ β : Fin d) :
    (∑ α, T.edgeMat⁻¹ γ α * T.edgeMat α β) = if γ = β then 1 else 0 := by
  have hu : IsUnit T.edgeMat.det := isUnit_iff_ne_zero.mpr h
  have := congrFun (congrFun (Matrix.nonsing_inv_mul T.edgeMat hu) γ) β
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

theorem mul_inv (h : T.Nondeg) (β α : Fin d) :
    (∑ γ, T.edgeMat β γ * T.edgeMat⁻¹ γ α) = if β = α then 1 else 0 := by
  have hu : IsUnit T.edgeMat.det := isUnit_iff_ne_zero.mpr h
  have := congrFun (congrFun (Matrix.mul_nonsing_inv T.edgeMat hu) β) α
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

/-- `g_a · (x_b - x_0) = δ_ab - δ_a0`. -/
theorem grad_dot_base (h : T.Nondeg) (a b : Fin (d + 1)) :
    dot (T.grad a) (T.x b - T.x 0) = (if a = b then 1 else 0) - (if a = 0 then 1 else 0) := by
  cases b using Fin.cases with
  | zero => simp [dot]
  | succ β =>
    rw [edge_col]
    cases a using Fin.cases with
    | zero =>
      rw [grad_zero]
      simp only [dot, Pi.neg_apply, Finset.sum_apply, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [inv_mul T h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [ite_eq_right (Fin.succ_ne_zero β).symm]
      ring
    | succ γ =>
      rw [grad_succ]
      simp only [dot]
      rw [inv_mul T h]
      simp [Fin.succ_ne_zero, Fin.succ_inj]
end SimplexCalc

open SimplexCalc in
/-- MC-N.P1-5.1 (JST `Paper1.Spec.P1_5_1`, proof `Paper1.Proofs.p1_5_1`). P1-5.1: P1 simplex calculus. -/
theorem _root_.CFDLean.Num.Simplex.calculus :
    ∀ (d : ℕ) (T : Simplex d), T.Nondeg →
      (∑ a, T.grad a = 0) ∧
      (∀ a b c, dot (T.grad a) (T.x b - T.x c) = (if a = b then 1 else 0) - (if a = c then 1 else 0)) ∧
      (∑ a, outer (T.grad a) (T.x a) = 1) ∧ 0 < T.vol ∧ (∑ o, T.facet o = 0) := by
  intro d T h
  refine ⟨grad_sum T, ?_, ?_, ?_, ?_⟩
  · intro a b c
    have e : T.x b - T.x c = (T.x b - T.x 0) - (T.x c - T.x 0) := by abel
    rw [e]
    have hsub : ∀ u v w : Vec d, dot u (v - w) = dot u v - dot u w := by
      intro u v w; simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hsub, grad_dot_base T h, grad_dot_base T h]
    ring
  · -- Σ g_a ⊗ x_a = Σ g_a ⊗ (x_a - x_0) = 1
    have hshift : (∑ a, outer (T.grad a) (T.x a)) = ∑ a, outer (T.grad a) (T.x a - T.x 0) := by
      have : (∑ a, outer (T.grad a) (T.x 0)) = 0 := by
        ext α β
        simp only [outer, Matrix.sum_apply, Matrix.zero_apply, ← Finset.sum_mul]
        have := congrFun (grad_sum T) α
        simp only [Finset.sum_apply, Pi.zero_apply] at this
        rw [this, zero_mul]
      have hsplit : ∀ a, outer (T.grad a) (T.x a - T.x 0) =
          outer (T.grad a) (T.x a) - outer (T.grad a) (T.x 0) := by
        intro a; ext α β; simp [outer, mul_sub]
      simp only [hsplit, Finset.sum_sub_distrib, this, sub_zero]
    rw [hshift, Fin.sum_univ_succ]
    simp only [sub_self, edge_col, grad_succ]
    ext α β
    simp only [outer, Matrix.add_apply, Matrix.sum_apply, Pi.zero_apply, mul_zero, zero_add]
    rw [show (∑ γ : Fin d, T.edgeMat⁻¹ γ α * T.edgeMat β γ) = ∑ γ, T.edgeMat β γ * T.edgeMat⁻¹ γ α from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, mul_inv T h]
    simp [Matrix.one_apply, eq_comm]
  · unfold Simplex.vol
    apply div_pos (abs_pos.mpr h)
    exact_mod_cast Nat.factorial_pos d
  · unfold Simplex.facet
    rw [← Finset.smul_sum, grad_sum, smul_zero]

/-- A vector is fixed by its dot products with the edges `x_a - x_0`: `u = Σ_a (u·(x_a - x_0)) g_a`. -/
theorem vec_expand {d : ℕ} (T : Simplex d) (h : T.Nondeg) (u : Vec d) :
    u = ∑ a, dot u (T.x a - T.x 0) • T.grad a := by
  obtain ⟨-, -, hI, -, -⟩ := Simplex.calculus d T h
  have hs := grad_sum T
  funext α
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : u α = ∑ a, T.grad a α * dot (T.x a) u := by
    have h1 : u α = ∑ β, (1 : Matrix (Fin d) (Fin d) ℝ) α β * u β := by
      simp [Matrix.one_apply]
    rw [h1, ← hI]
    simp only [Matrix.sum_apply, outer, Finset.sum_mul, dot, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e0 : ∑ a, T.grad a α * dot (T.x 0) u = 0 := by
    rw [← Finset.sum_mul]
    have := congrFun hs α
    simp only [Finset.sum_apply, Pi.zero_apply] at this
    rw [this, zero_mul]
  rw [e1, ← sub_zero (∑ a, T.grad a α * dot (T.x a) u), ← e0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : dot u (T.x a - T.x 0) = dot (T.x a) u - dot (T.x 0) u := by
    simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [this]; ring

/-- Uniqueness form: equal edge dot products give equal vectors. -/
theorem vec_eq_of_dots {d : ℕ} (T : Simplex d) (h : T.Nondeg) (u v : Vec d)
    (huv : ∀ a, dot u (T.x a - T.x 0) = dot v (T.x a - T.x 0)) : u = v := by
  rw [vec_expand T h u, vec_expand T h v]
  simp only [huv]

theorem dot_sub_left' {d : ℕ} (u v w : Vec d) : dot (u - v) w = dot u w - dot v w := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dot_smul_l {d : ℕ} (c : ℝ) (u w : Vec d) : dot (c • u) w = c * dot u w := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_neg_l {d : ℕ} (u w : Vec d) : dot (-u) w = -dot u w := by
  simp only [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

set_option maxHeartbeats 2000000 in
/-- The 2D median-dual segment is a signed multiple of `g_k - g_i`. -/
theorem rot_eq (T : Simplex 2) (h : T.Nondeg) (i k : Fin 3) (hik : i ≠ k) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      rot90 (T.centroid - (1 / 2 : ℝ) • (T.x i + T.x k)) =
        (σ * (T.edgeMat.det / 6)) • (T.grad k - T.grad i) := by
  obtain ⟨-, hd, -, -, -⟩ := Simplex.calculus 2 T h
  have key : ∀ σ : ℝ, (∀ a, dot (rot90 (T.centroid - (1 / 2 : ℝ) • (T.x i + T.x k))) (T.x a - T.x 0) =
      σ * (T.edgeMat.det / 6) * dot (T.grad k - T.grad i) (T.x a - T.x 0)) →
      rot90 (T.centroid - (1 / 2 : ℝ) • (T.x i + T.x k)) =
        (σ * (T.edgeMat.det / 6)) • (T.grad k - T.grad i) := by
    intro σ hσ
    apply vec_eq_of_dots T h
    intro a
    rw [hσ, dot_smul_l]
  have hdk : ∀ a, dot (T.grad k - T.grad i) (T.x a - T.x 0) =
      ((if k = a then 1 else 0) - (if k = 0 then 1 else 0)) -
        ((if i = a then 1 else 0) - (if i = 0 then 1 else 0)) := by
    intro a; rw [dot_sub_left', hd, hd]
  fin_cases i <;> fin_cases k <;> simp at hik
  · exact ⟨1, Or.inl rfl, key (1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨-1, Or.inr rfl, key (-1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨-1, Or.inr rfl, key (-1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨1, Or.inl rfl, key (1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨1, Or.inl rfl, key (1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩
  · exact ⟨-1, Or.inr rfl, key (-1) fun a => by
      rw [hdk]; fin_cases a <;>
        simp [rot90, Simplex.centroid, dot, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_fin_two,
          Simplex.edgeMat] <;> ring⟩

theorem dualFacet2_eq (T : Simplex 2) (h : T.Nondeg) (i k : Fin 3) (hik : i ≠ k) :
    dualFacet2 T i k = (T.vol / 3) • (T.grad k - T.grad i) := by
  obtain ⟨-, hd, -, hvol, -⟩ := Simplex.calculus 2 T h
  obtain ⟨σ, hσ, hr⟩ := rot_eq T h i k hik
  have hvol' : T.vol = |T.edgeMat.det| / 2 := by simp [Simplex.vol]
  have hw : dot (T.grad k - T.grad i) (T.x k - T.x i) = 2 := by
    rw [dot_sub_left', hd, hd]; simp [hik, Ne.symm hik]; norm_num
  -- `σ det/6 = ± vol/3`
  have hpm : σ * (T.edgeMat.det / 6) = T.vol / 3 ∨ σ * (T.edgeMat.det / 6) = -(T.vol / 3) := by
    rw [hvol']
    rcases hσ with rfl | rfl <;> rcases abs_choice T.edgeMat.det with hab | hab <;> rw [hab] <;>
      [left; right; right; left] <;> ring
  unfold dualFacet2
  simp only
  rw [hr]
  rcases hpm with hp | hp
  · rw [hp, ite_eq_left]
    rw [dot_smul_l, hw]; positivity
  · rw [hp, ite_eq_right, neg_smul, neg_neg]
    rw [dot_smul_l, hw]; push Not
    have : 0 < T.vol := hvol
    linarith

namespace Geo3

theorem dot_comm' {d : ℕ} (u v : Vec d) : dot u v = dot v u := by
  simp only [dot, mul_comm]

theorem dot_sub_left {d : ℕ} (u v w : Vec d) : dot (u - v) w = dot u w - dot v w := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dot_sub_right {d : ℕ} (u v w : Vec d) : dot u (v - w) = dot u v - dot u w := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dot_neg_left {d : ℕ} (u w : Vec d) : dot (-u) w = -dot u w := by
  simp only [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem dot_neg_right {d : ℕ} (u w : Vec d) : dot u (-w) = -dot u w := by
  simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem dot_single_left {d : ℕ} (p : Fin d) (c : ℝ) (v : Vec d) : dot (Pi.single p c) v = c * v p := by
  simp only [dot, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- A family with the barycentric dot table is the gradient family, and the simplex is nondegenerate. -/
theorem grads_of_dual {d : ℕ} (T : Simplex d) (G : Fin (d + 1) → Vec d)
    (hG : ∀ a j, dot (G a) (T.x j - T.x 0) = (if a = j then 1 else 0) - (if a = 0 then 1 else 0)) :
    T.Nondeg ∧ ∀ a, T.grad a = G a := by
  have hN : T.Nondeg := by
    let M : Matrix (Fin d) (Fin d) ℝ := fun β α => G β.succ α
    have hM : M * T.edgeMat = 1 := by
      ext β γ
      have := hG β.succ γ.succ
      simp only [Fin.succ_inj, Fin.succ_ne_zero, ite_false, sub_zero] at this
      rw [Matrix.mul_apply, Matrix.one_apply, ← this]
      simp only [M, dot, Simplex.edgeMat, Pi.sub_apply]
    have := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  refine ⟨hN, fun a => ?_⟩
  apply vec_eq_of_dots T hN
  intro j
  rw [hG a j, (Simplex.calculus d T hN).2.1 a j 0]

theorem path_coord (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ) (j : Fin 4) (k : Fin 3) :
    (pathSimplex π h).x j (π k) = if k.val < j.val then h (π k) else 0 := by
  simp only [pathSimplex, Finset.sum_apply]
  simp only [apply_ite (fun v : Vec 3 => v (π k)), Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Pi.single_apply, π.injective.eq_iff]
  rw [Fin.sum_univ_three]
  fin_cases k <;> simp

theorem path_x0 (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ) : (pathSimplex π h).x 0 = 0 := by
  funext α
  simp [pathSimplex]

/-- The scaled unit vectors `e_{π i} / h_{π i}`. -/
def sv (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ) (i : Fin 3) : Vec 3 := Pi.single (π i) (h (π i))⁻¹

/-- Candidate gradients of the path simplex. -/
def pathG (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ) : Fin 4 → Vec 3 :=
  ![-sv π h 0, sv π h 0 - sv π h 1, sv π h 1 - sv π h 2, sv π h 2]

theorem sv_dot_x (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ) (hp : ∀ i, 0 < h i) (i : Fin 3) (j : Fin 4) :
    dot (sv π h i) ((pathSimplex π h).x j - (pathSimplex π h).x 0) = if i.val < j.val then 1 else 0 := by
  rw [path_x0, sub_zero, sv, dot_single_left, path_coord]
  split_ifs
  · exact inv_mul_cancel₀ (hp _).ne'
  · exact mul_zero _

theorem sv_dot_sv (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ) (i k : Fin 3) :
    dot (sv π h i) (sv π h k) = if i = k then (h (π i))⁻¹ * (h (π i))⁻¹ else 0 := by
  rw [sv, dot_single_left, sv, Pi.single_apply]
  by_cases hik : i = k
  · subst hik; simp
  · simp [hik, π.injective.eq_iff]

theorem path_grads (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ) (hp : ∀ i, 0 < h i) :
    (pathSimplex π h).Nondeg ∧ ∀ a, (pathSimplex π h).grad a = pathG π h a := by
  apply grads_of_dual
  intro a j
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  fin_cases a <;> fin_cases j <;>
    simp only [pathG, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, dot_sub_left, dot_neg_left,
      sv_dot_x π h hp] <;> simp

theorem cross_dot_left (u v : Vec 3) : dot (cross3 u v) u = 0 := by
  simp only [cross3, dot, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem cross_dot_right (u v : Vec 3) : dot (cross3 u v) v = 0 := by
  simp only [cross3, dot, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- Expansion of a vector in the dual basis of `u, v, w` (polynomial form). -/
theorem lagrange (u v w g : Vec 3) :
    dot g w • cross3 u v + dot g u • cross3 v w + dot g v • cross3 w u = dot (cross3 u v) w • g := by
  funext i
  fin_cases i <;>
  simp only [cross3, dot, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> ring

theorem det_edge3 (T : Simplex 3) :
    T.edgeMat.det = dot (cross3 (T.x 1 - T.x 0) (T.x 2 - T.x 0)) (T.x 3 - T.x 0) := by
  rw [Matrix.det_fin_three]
  simp only [Simplex.edgeMat, cross3, dot, Fin.sum_univ_three, Pi.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  simp
  ring

theorem triple_perm (p : Fin 4 → Vec 3) (o a b c : Fin 4) (hnd : [o, a, b, c].Nodup) :
    dot (cross3 (p b - p a) (p c - p a)) (p o - p a) = dot (cross3 (p 1 - p 0) (p 2 - p 0)) (p 3 - p 0) ∨
    dot (cross3 (p b - p a) (p c - p a)) (p o - p a) = -dot (cross3 (p 1 - p 0) (p 2 - p 0)) (p 3 - p 0) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hoa, hob, hoc⟩, ⟨hab, hac⟩, hbc⟩ := hnd
  fin_cases o <;> fin_cases a <;> (simp at hoa) <;> fin_cases b <;> (simp at hob hab) <;>
    fin_cases c <;> (simp at hoc hac hbc) <;>
  (simp only [cross3, dot, Fin.sum_univ_three, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
   first | exact Or.inl trivial | (left; ring1) | (right; ring1))

theorem facet_cross (T : Simplex 3) (o a b c : Fin 4) (hT : T.Nondeg) (hnd : [o, a, b, c].Nodup) :
    T.facet o = (if 0 < dot (cross3 (T.x b - T.x a) (T.x c - T.x a)) (T.x o - T.x a) then -(1 / 2 : ℝ)
      else 1 / 2) • cross3 (T.x b - T.x a) (T.x c - T.x a) := by
  have habs : |dot (cross3 (T.x b - T.x a) (T.x c - T.x a)) (T.x o - T.x a)| = |T.edgeMat.det| := by
    rw [det_edge3]
    rcases triple_perm T.x o a b c hnd with h | h <;> rw [h]
    rw [abs_neg]
  have hne := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hne
  obtain ⟨⟨hoa, hob, hoc⟩, -, -⟩ := hne
  set u := T.x b - T.x a
  set v := T.x c - T.x a
  set w := T.x o - T.x a
  set D := dot (cross3 u v) w with hD
  have hgrad := (Simplex.calculus 3 T hT).2.1
  have hu : dot (T.grad o) u = 0 := by rw [hgrad]; simp [hob, hoa]
  have hv : dot (T.grad o) v = 0 := by rw [hgrad]; simp [hoc, hoa]
  have hw : dot (T.grad o) w = 1 := by rw [hgrad]; simp [hoa]
  have hL := lagrange u v w (T.grad o)
  rw [hw, hu, hv, zero_smul, zero_smul, add_zero, add_zero, one_smul] at hL
  have hD0 : D ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    exact hT (abs_eq_zero.mp habs.symm)
  have hg : T.grad o = D⁻¹ • cross3 u v := by rw [hL, smul_smul, inv_mul_cancel₀ hD0, one_smul]
  rw [Simplex.facet, Simplex.vol, ← habs, hg, smul_smul]
  congr 1
  norm_num [Nat.factorial]
  split_ifs with hpos
  · rw [abs_of_pos hpos]; field_simp; ring
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp hpos) hD0)]; field_simp; ring

end Geo3

open Geo3 in
/-- MC-N.P3-12.5 (JST `Paper1.Spec.P3_12_5`, proof `Paper1.Proofs.p3_12_5`). P3-12.5: every Kuhn tetrahedron of a brick is nondegenerate and has `g_a · g_b ≤ 0` for `a ≠ b`, so all its dihedral angles are at most 90°. -/
theorem _root_.CFDLean.Num.pathSimplex_nonobtuse :
    ∀ (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ), (∀ i, 0 < h i) →
      (pathSimplex π h).Nondeg ∧
      ∀ a b : Fin 4, a ≠ b → dot ((pathSimplex π h).grad a) ((pathSimplex π h).grad b) ≤ 0 := by
  intro π h hp
  obtain ⟨hN, hg⟩ := path_grads π h hp
  refine ⟨hN, fun a b hab => ?_⟩
  rw [hg, hg]
  have hq : ∀ i, 0 ≤ (h (π i))⁻¹ * (h (π i))⁻¹ := fun i => mul_self_nonneg _
  fin_cases a <;> fin_cases b <;>
    simp_all [pathG, dot_sub_left, dot_neg_left, dot_sub_right, dot_neg_right, sv_dot_sv]

open Geo3 in
/-- MC-N.P3-11.2 (JST `Paper1.Spec.P3_11_2`, proof `Paper1.Proofs.p3_11_2`). P3-11.2 (d = 3): the facet vector opposite `o` is half the cross product of two facet edges, oriented away from `o`; two tetrahedra that share a triangle and lie on opposite sides of it have opposite facet vectors. -/
theorem _root_.CFDLean.Num.Simplex.facet_cross3 :
    (∀ (T : Simplex 3) (o a b c : Fin 4), T.Nondeg → [o, a, b, c].Nodup →
      let nv := cross3 (T.x b - T.x a) (T.x c - T.x a)
      T.facet o = (if 0 < dot nv (T.x o - T.x a) then -(1 / 2 : ℝ) else 1 / 2) • nv) ∧
    (∀ (T T' : Simplex 3) (o a b c o' a' b' c' : Fin 4), T.Nondeg → T'.Nondeg → [o, a, b, c].Nodup →
      [o', a', b', c'].Nodup → T'.x a' = T.x a → T'.x b' = T.x b → T'.x c' = T.x c →
      let nv := cross3 (T.x b - T.x a) (T.x c - T.x a)
      dot nv (T.x o - T.x a) * dot nv (T'.x o' - T.x a) < 0 → T'.facet o' = -T.facet o) := by
  refine ⟨fun T o a b c hT hnd => facet_cross T o a b c hT hnd, ?_⟩
  intro T T' o a b c o' a' b' c' hT hT' hnd hnd' ha hb hc nv hprod
  have h1 := facet_cross T o a b c hT hnd
  have h2 := facet_cross T' o' a' b' c' hT' hnd'
  rw [ha, hb, hc] at h2
  rw [h1, h2]
  simp only [nv] at hprod
  rcases mul_neg_iff.mp hprod with ⟨hp, hn⟩ | ⟨hn, hp⟩
  · rw [ite_eq_left hp, ite_eq_right (not_lt.mpr hn.le), neg_smul, neg_neg]
  · rw [ite_eq_right (not_lt.mpr hn.le), ite_eq_left hp, neg_smul]

namespace Avg11b
open Geo3

/-- Expansion of a vector in the dual basis of `u, w` (2D, polynomial form). -/
theorem lagrange2 (u w g : Vec 2) :
    dot g w • perp2 u - dot g u • perp2 w = dot (perp2 u) w • g := by
  funext i
  fin_cases i <;>
  simp only [perp2, dot, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one] <;> ring

theorem det_edge2 (T : Simplex 2) :
    T.edgeMat.det = -dot (perp2 (T.x 1 - T.x 0)) (T.x 2 - T.x 0) := by
  rw [Matrix.det_fin_two]
  simp only [Simplex.edgeMat, perp2, dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp
  ring

theorem triple_perm2 (p : Fin 3 → Vec 2) (o a b : Fin 3) (hnd : [o, a, b].Nodup) :
    dot (perp2 (p b - p a)) (p o - p a) = dot (perp2 (p 1 - p 0)) (p 2 - p 0) ∨
    dot (perp2 (p b - p a)) (p o - p a) = -dot (perp2 (p 1 - p 0)) (p 2 - p 0) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hoa, hob⟩, hab⟩ := hnd
  fin_cases o <;> fin_cases a <;> (simp at hoa) <;> fin_cases b <;> (simp at hob hab) <;>
  (simp only [perp2, dot, Fin.sum_univ_two, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
   first | exact Or.inl trivial | (left; ring1) | (right; ring1))

theorem facet_perp (T : Simplex 2) (o a b : Fin 3) (hT : T.Nondeg) (hnd : [o, a, b].Nodup) :
    T.facet o = (if 0 < dot (perp2 (T.x b - T.x a)) (T.x o - T.x a) then -1 else 1 : ℝ) •
      perp2 (T.x b - T.x a) := by
  have habs : |dot (perp2 (T.x b - T.x a)) (T.x o - T.x a)| = |T.edgeMat.det| := by
    rw [det_edge2, abs_neg]
    rcases triple_perm2 T.x o a b hnd with h | h <;> rw [h]
    rw [abs_neg]
  have hne := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hne
  obtain ⟨⟨hoa, hob⟩, -⟩ := hne
  set u := T.x b - T.x a
  set w := T.x o - T.x a
  set D := dot (perp2 u) w with hD
  have hgrad := (Simplex.calculus 2 T hT).2.1
  have hu : dot (T.grad o) u = 0 := by rw [hgrad]; simp [hob, hoa]
  have hw : dot (T.grad o) w = 1 := by rw [hgrad]; simp [hoa]
  have hL := lagrange2 u w (T.grad o)
  rw [hw, hu, zero_smul, sub_zero, one_smul] at hL
  have hD0 : D ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    exact hT (abs_eq_zero.mp habs.symm)
  have hg : T.grad o = D⁻¹ • perp2 u := by rw [hL, smul_smul, inv_mul_cancel₀ hD0, one_smul]
  rw [Simplex.facet, Simplex.vol, ← habs, hg, smul_smul]
  congr 1
  norm_num [Nat.factorial]
  split_ifs with hpos
  · rw [abs_of_pos hpos]; field_simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp hpos) hD0)]; field_simp

end Avg11b

section
open Avg11b

/-- MC-N.P3-11.2b (JST `Paper1.Spec.P3_11_2b`, proof `Paper1.Proofs.p3_11_2b`). P3-11.2b (d = 2): the facet vector opposite `o` is the rotated facet edge, pointing away from `o`. -/
theorem _root_.CFDLean.Num.Simplex.facet_perp2 :
    ∀ (T : Simplex 2) (o a b : Fin 3), T.Nondeg → [o, a, b].Nodup →
      T.facet o = (if 0 < dot (perp2 (T.x b - T.x a)) (T.x o - T.x a) then -1 else 1 : ℝ) • perp2 (T.x b - T.x a) := fun T o a b hT hnd => facet_perp T o a b hT hnd

end

end CFDLean.Num.Internal
