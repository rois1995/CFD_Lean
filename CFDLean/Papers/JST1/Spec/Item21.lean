import CFDLean.Papers.JST1.Spec.Item16
set_option cleanup.letToHave false -- keep the `let` binders of the statements (as P1-P5)

/-! Statements of item 21 (P6): the quadrature fact `∫_T φ_i = m_T = |T|/(d+1)` of `prop:consistency`(b) (paper
sha256 `5ec5f9db…`, proof line 975: "since ∇·F_h is constant on T and ∫_T φ_i = m_T"; also used at lines 915 and 1025),
left out of P4-16.1 (decision D1 of `P4-proposal.md`), with `|T|` the Lebesgue measure of the closed simplex and
`T.vol = |det|/d!` its algebraic volume. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num MeasureTheory
namespace CFDLean.JST1.Spec

/-- The closed simplex: the convex hull of the vertices. -/
def hullT {d : ℕ} (T : Simplex d) : Set (Vec d) := convexHull ℝ (Set.range T.x)

/-- Divergence of the P1 interpolant at `x`, row `c`: `Σ_β ∂_β (F_h)_{cβ}(x)` (derivatives along the coordinate
lines). -/
def divP1 {κ : Type} {d : ℕ} (T : Simplex d) (F : Fin (d + 1) → Matrix κ (Fin d) ℝ) (x : Vec d) : κ → ℝ :=
  fun c => ∑ β, deriv (fun s : ℝ => p1Interp T F (x + s • Pi.single β 1) c β) 0

/-- The hat function `φ_i` of node `i` on the cell `T` of a mesh (the barycentric coordinate of the local vertex of
`T` at `i`, and `0` if `i` is not a vertex of `T`). -/
def hatOn {ι C : Type} [DecidableEq ι] {d : ℕ} (M : WMesh ι C d) (i : ι) (T : C) (x : Vec d) : ℝ :=
  ∑ a, if M.vert T a = i then bary (M.simplex T) a x else 0

/-- P6-21.1: for a nondegenerate simplex, the closed simplex (convex hull of the vertices) is the set where all
barycentric coordinates are `≥ 0`, and its Lebesgue measure is the algebraic volume `T.vol = |det(x_β - x_0)|/d!`. -/
def P6_21_1 : Prop :=
  ∀ (d : ℕ) (T : Simplex d), T.Nondeg →
    hullT T = {x : Vec d | ∀ b, 0 ≤ bary T b x} ∧ volume (hullT T) = ENNReal.ofReal T.vol

/-- P6-21.2 (`∫_T φ_i = m_T`): on a nondegenerate simplex every barycentric coordinate is integrable over the closed
simplex and `∫_T φ_b = |T|/(d+1)`. -/
def P6_21_2 : Prop :=
  ∀ (d : ℕ) (T : Simplex d), T.Nondeg → ∀ b : Fin (d + 1),
    IntegrableOn (bary T b) (hullT T) ∧ ∫ x in hullT T, bary T b x = T.vol / ((d : ℝ) + 1)

/-- P6-21.3 (`prop:consistency`(b), "`Σ_k ½(F_i + F_k)·n_ik = ∫_Ω φ_i ∇·F_h`"): on a valid mesh, at a closed vertex
`i`, the mean flux equals `Σ_T ω_T ∫_T φ_i ∇·F_h`, with `F_h` the P1 interpolant of the nodal fluxes on each cell and
`∇·F_h` its divergence (derivatives along the coordinate lines); cells with weight `ω_T` (`ω_T = 1` on a simplex
mesh, the split weights on a mixed mesh). `∫_Ω` is read as this weighted cell sum: it equals `∫_Ω` on a conforming
simplex mesh (cells cover `Ω` and overlap in null sets, not formalized), and on a mixed mesh it is the only meaning
("split by split"). Follows from P6-21.2 and P4-16.1. -/
def P6_21_3 : Prop :=
  ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
    (F : ι → Matrix κ (Fin d) ℝ) (i : ι), M.Valid → M.Closed i →
    (∑ k, ((1 / 2 : ℝ) • (F i + F k)).mulVec (M.n i k)) = fun c =>
      ∑ T, M.ω T * ∫ x in hullT (M.simplex T),
        hatOn M i T x * divP1 (M.simplex T) (fun b => F (M.vert T b)) x c

end CFDLean.JST1.Spec
