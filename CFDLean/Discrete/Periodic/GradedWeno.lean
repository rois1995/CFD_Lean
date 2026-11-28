import CFDLean.Discrete.Periodic.WenoStencil
import CFDLean.Discrete.Periodic.Weno

namespace CFDLean.FV1D.Reconstruction

open Periodic GradedWeno

/-- The same width-dependent arithmetic is used by the native kernels. -/
noncomputable def gradedWeno {I : Type} (m : Mesh1D I) (ε : {e : ℝ // 0 < e}) : Reconstruction m ℝ where
  traces u i :=
    let atFace (prev next : I → I) (j : I) := edge ε.val (gather prev next m.width j) (gather prev next u j)
    (atFace m.grid.prev m.grid.next i, atFace m.grid.next m.grid.prev (m.grid.next i))

theorem ideal_positive {a b d e : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e) :
    let weights := ideal a b d e
    0 < weights.1 ∧ 0 < weights.2.1 ∧ 0 < weights.2.2 := by
  dsimp [ideal]
  exact ⟨by positivity, by positivity, by positivity⟩

/-- Mean of a quadratic on the interval of width h centered at x, in owner-width units. -/
noncomputable def mean (A B C h x : ℝ) := A*(x*x+h*h/12) + B*x + C

theorem candidate_quadratic (A B C l m r z : ℝ) (hl : 0 < l) (hm : 0 < m) (hr : 0 < r) :
    candidate l m r z (mean A B C l (-z-(l+m)/2)) (mean A B C m (-z))
      (mean A B C r (-z+(m+r)/2)) = (A/4+B/2+C, B*B+13/3*A*A) := by
  have h₀ : 2*(mean A B C m (-z) - mean A B C l (-z-(l+m)/2))/(l+m) =
      B-2*A*z-A*(2*l+m)/3 := by
    apply (div_eq_iff (ne_of_gt (by positivity))).2
    unfold mean
    ring
  have h₁ : 2*(mean A B C r (-z+(m+r)/2) - mean A B C m (-z))/(m+r) =
      B-2*A*z+A*(m+2*r)/3 := by
    apply (div_eq_iff (ne_of_gt (by positivity))).2
    unfold mean
    ring
  have ha : 3*((B-2*A*z+A*(m+2*r)/3)-(B-2*A*z-A*(2*l+m)/3))/(2*(l+m+r)) = A := by
    apply (div_eq_iff (ne_of_gt (by positivity))).2
    ring
  simp only [candidate, h₀, h₁, ha]
  apply Prod.ext <;> dsimp [mean] <;> ring

theorem blend_agree {ε x β : ℝ} {d : ℝ × ℝ × ℝ} (hε : 0 < ε) (hβ : 0 ≤ β)
    (hd : 0 < d.1 ∧ 0 < d.2.1 ∧ 0 < d.2.2) : blend ε d (x,β) (x,β) (x,β) = x := by
  obtain ⟨h₀,h₁,h₂⟩ := hd
  unfold blend
  apply (div_eq_iff (ne_of_gt (by dsimp; positivity))).2
  ring

/-- Local polynomial control on arbitrary positive relative widths, including a constant (A=B=0). -/
theorem edge_quadratic_graded {ε a b d e : ℝ} (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (he : 0 < e) (A B C : ℝ) :
    let f := mean A B C
    edge ε ⟨a,b,1,d,e⟩ ⟨f a (-(1+b)/2-(a+b)/2), f b (-(1+b)/2), f 1 0,
      f d ((1+d)/2), f e ((1+d)/2+(d+e)/2)⟩ = A/4+B/2+C := by
  dsimp only [edge]
  simp only [div_one]
  have h₀ := candidate_quadratic A B C a b 1 ((b+1)/2) ha hb one_pos
  have h₁ := candidate_quadratic A B C b 1 d 0 hb one_pos hd
  have h₂ := candidate_quadratic A B C 1 d e ((0-(1+d))/2) one_pos hd he
  ring_nf at h₀ h₁ h₂ ⊢
  rw [h₀, h₁, h₂]
  apply blend_agree hε (by positivity) (ideal_positive ha hb hd he)

theorem edge_constant {ε : ℝ} (hε : 0 < ε) (w : Stencil ℝ)
    (ha : 0 < w.farLeft) (hb : 0 < w.left) (hc : 0 < w.center)
    (hd : 0 < w.right) (he : 0 < w.farRight) (v : ℝ) :
    edge ε w ⟨v,v,v,v,v⟩ = v := by
  have h := edge_quadratic_graded hε (div_pos ha hc) (div_pos hb hc) (div_pos hd hc) (div_pos he hc) 0 0 v
  simpa [edge, mean] using h

theorem gradedWeno_constants {I : Type} (m : Mesh1D I) (ε : {e : ℝ // 0 < e}) :
    (gradedWeno m ε).PreservesConstants := by
  intro v i
  apply Prod.ext <;> apply edge_constant ε.property _ <;> apply m.width_pos

private theorem uniform_candidate (a b c : ℝ) :
    candidate 1 1 1 1 a b c =
      ((2*a-7*b+11*c)/6, 13/12*(a-2*b+c)^2 + (a-4*b+3*c)^2/4) ∧
    candidate 1 1 1 0 a b c =
      ((-a+5*b+2*c)/6, 13/12*(a-2*b+c)^2 + (a-c)^2/4) ∧
    candidate 1 1 1 (-1) a b c =
      ((2*a+5*b-c)/6, 13/12*(a-2*b+c)^2 + (3*a-4*b+c)^2/4) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Prod.ext <;> dsimp [candidate] <;> ring

theorem edge_uniform (ε : {e : ℝ // 0 < e}) {h : ℝ} (hh : 0 < h) (u : Stencil ℝ) :
    edge ε.val ⟨h,h,h,h,h⟩ u = Weno.edge ε u.farLeft u.left u.center u.right u.farRight := by
  rcases u with ⟨a,b,c,d,e⟩
  simp only [edge, div_self hh.ne']
  norm_num only at *
  rw [(uniform_candidate _ _ _).1, (uniform_candidate _ _ _).2.1, (uniform_candidate _ _ _).2.2]
  norm_num [blend, ideal, Weno.edge, Weno.weight, pow_two, add_assoc]

end CFDLean.FV1D.Reconstruction
