import CFDLean.Geometry.MeshBoundary
import CFDLean.Papers.JST1.Mixed.RefCells
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Statements of item 11, stage 1 (P3): `lem:avg` (lines 683-690, proof 957-966): closure from facet balance,
shared facets in 3D, and face balance of the pulling splits. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec
open CFDLean.JST1.RefCell

/-- P3-11.1: on a facet-balanced mesh (any weights), `β` and `B_c` are sums over the boundary facets, and a vertex on
no boundary facet is closed. A conforming mesh (P2-6.3) is facet balanced. -/
def P3_11_1 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d)
    (bd : C × Fin (d + 1) → Bool), M.Valid → 1 ≤ d →
    (M.Conforming bd → M.FacetBalanced bd) ∧
    (M.FacetBalanced bd →
      (∀ i, M.beta i = ∑ p, if bd p ∧ i ∈ M.facetNodes p then (1 / (d : ℝ)) • M.areaVec p else 0) ∧
      (∀ i k, M.B i k = ∑ p, if bd p ∧ i ∈ M.facetNodes p ∧ k ∈ M.facetNodes p then
          ((1 + if i = k then 1 else 0) / ((d : ℝ) * (d + 1))) • M.areaVec p else 0) ∧
      (∀ i, (∀ p, bd p = true → i ∉ M.facetNodes p) → M.Closed i))

/-- P3-11.2 (d = 3): the facet vector opposite `o` is half the cross product of two facet edges, oriented away from
`o`; two tetrahedra that share a triangle and lie on opposite sides of it have opposite facet vectors. -/
def P3_11_2 : Prop :=
  (∀ (T : Simplex 3) (o a b c : Fin 4), T.Nondeg → [o, a, b, c].Nodup →
    let nv := cross3 (T.x b - T.x a) (T.x c - T.x a)
    T.facet o = (if 0 < Num.dot nv (T.x o - T.x a) then -(1 / 2 : ℝ) else 1 / 2) • nv) ∧
  (∀ (T T' : Simplex 3) (o a b c o' a' b' c' : Fin 4), T.Nondeg → T'.Nondeg → [o, a, b, c].Nodup →
    [o', a', b', c'].Nodup → T'.x a' = T.x a → T'.x b' = T.x b → T'.x c' = T.x c →
    let nv := cross3 (T.x b - T.x a) (T.x c - T.x a)
    Num.dot nv (T.x o - T.x a) * Num.dot nv (T'.x o' - T.x a) < 0 → T'.facet o' = -T.facet o)

/-- P3-11.3: the pulling splits (64 of the hexahedron, 12 of the prism, 6 of the pyramid, 4 of the quadrilateral)
use the two diagonals of every quadrilateral face equally often (32:32, 6:6, 3:3, 2:2), and every split uses
exactly one of them. -/
def P3_11_3 : Prop :=
  hex.splits.length = 64 ∧ prism.splits.length = 12 ∧ pyramid.splits.length = 6 ∧
  (hex.quads.all fun q => hex.diagCount q false == 32 && hex.diagCount q true == 32) = true ∧
  (prism.quads.all fun q => prism.diagCount q false == 6 && prism.diagCount q true == 6) = true ∧
  (pyramid.quads.all fun q => pyramid.diagCount q false == 3 && pyramid.diagCount q true == 3) = true ∧
  (hex.splits.all fun s => hex.quads.all fun q =>
      usesEdge (hex.pull s.1 s.2) (q.diag false) != usesEdge (hex.pull s.1 s.2) (q.diag true)) = true ∧
  (prism.splits.all fun s => prism.quads.all fun q =>
      usesEdge (prism.pull s.1 s.2) (q.diag false) != usesEdge (prism.pull s.1 s.2) (q.diag true)) = true ∧
  (pyramid.splits.all fun s => pyramid.quads.all fun q =>
      usesEdge (pyramid.pull s.1 s.2) (q.diag false) != usesEdge (pyramid.pull s.1 s.2) (q.diag true)) = true ∧
  ((List.finRange 4).countP fun v => usesEdge (quadPull v) (0, 2)) = 2 ∧
  ((List.finRange 4).countP fun v => usesEdge (quadPull v) (1, 3)) = 2

end CFDLean.JST1.Spec
