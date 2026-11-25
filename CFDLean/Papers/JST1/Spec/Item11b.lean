import CFDLean.Papers.JST1.Spec.Item11a
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Statements of item 11, stage 2 (P3): `lem:avg` (lines 683-690, proof 957-966), the geometric chain from the
splits of mixed cells to the closure of the averaged operator (d = 3). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec
open CFDLean.JST1.RefCell

/-- P3-11.4 (d = 3): on a mesh of nondegenerate tetrahedra, side balance implies facet balance (each facet vector is
`∓½` of the cross product of its sorted triangle, by P3-11.2). -/
def P3_11_4 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C] (M : WMesh ι C 3)
    (bd : C × Fin 4 → Bool), M.Valid → SideBalanced M bd → M.FacetBalanced bd

/-- Triangles (as vertex lists) of the faces of a reference cell. -/
def cellFaceTris {n : ℕ} (C : Cell3 n) : List (List (Fin n)) :=
  C.quads.flatMap (fun q => q.tris false ++ q.tris true) ++ C.tris

/-- The three faces (vertex triples) of a tetrahedron given as a list. -/
def tetFaces {n : ℕ} (t : List (Fin n)) : List (List (Fin n)) := t.map fun v => t.filter (· != v)

/-- Number of sub-tetrahedra of a split that have the triangle `s` as a face. -/
def faceCount {n : ℕ} (T : List (List (Fin n))) (s : List (Fin n)) : ℕ :=
  T.countP fun t => (tetFaces t).any (sameSimplex s)

/-- `s` lies in a face of the cell (it is one of the face triangles, for one of the two diagonals). -/
def onCellFace {n : ℕ} (C : Cell3 n) (s : List (Fin n)) : Bool := (cellFaceTris C).any (sameSimplex s)

/-- P3-11.5 (pulling splits are pseudomanifolds): in every pulling split of the hexahedron, prism and pyramid, every
face triangle of a sub-tetrahedron is a face of exactly two sub-tetrahedra if it is inside the cell, and of exactly
one if it lies on a face of the cell. -/
def P3_11_5 : Prop :=
  (hex.splits.all fun s => (hex.pull s.1 s.2).all fun t => (tetFaces t).all fun f =>
    faceCount (hex.pull s.1 s.2) f == (if onCellFace hex f then 1 else 2)) = true ∧
  (prism.splits.all fun s => (prism.pull s.1 s.2).all fun t => (tetFaces t).all fun f =>
    faceCount (prism.pull s.1 s.2) f == (if onCellFace prism f then 1 else 2)) = true ∧
  (pyramid.splits.all fun s => (pyramid.pull s.1 s.2).all fun t => (tetFaces t).all fun f =>
    faceCount (pyramid.pull s.1 s.2) f == (if onCellFace pyramid f then 1 else 2)) = true

/-- P3-11.6 (weights on cell faces): with equal weights on the pulling splits, every triangle of a quadrilateral
face of the cell is a sub-tetrahedron face with total weight exactly 1/2 (one diagonal), and every triangular face
with weight 1. This is combinatorial only; the step to side balance (P3-11.4) also needs the geometric premises of
stage 3 (P3-11.7, P3-11.8). -/
def P3_11_6 : Prop :=
  (hex.quads.all fun q => (q.tris false ++ q.tris true).all fun f =>
    2 * (hex.splits.countP fun s => faceCount (hex.pull s.1 s.2) f == 1) == hex.splits.length) = true ∧
  (prism.quads.all fun q => (q.tris false ++ q.tris true).all fun f =>
    2 * (prism.splits.countP fun s => faceCount (prism.pull s.1 s.2) f == 1) == prism.splits.length) = true ∧
  (prism.tris.all fun f => (prism.splits.countP fun s => faceCount (prism.pull s.1 s.2) f == 1) ==
    prism.splits.length) = true ∧
  (pyramid.quads.all fun q => (q.tris false ++ q.tris true).all fun f =>
    2 * (pyramid.splits.countP fun s => faceCount (pyramid.pull s.1 s.2) f == 1) == pyramid.splits.length) = true ∧
  (pyramid.tris.all fun f => (pyramid.splits.countP fun s => faceCount (pyramid.pull s.1 s.2) f == 1) ==
    pyramid.splits.length) = true

/-! 2D (quadrilateral cells). -/

/-- P3-11.2b (d = 2): the facet vector opposite `o` is the rotated facet edge, pointing away from `o`. -/
def P3_11_2b : Prop :=
  ∀ (T : Simplex 2) (o a b : Fin 3), T.Nondeg → [o, a, b].Nodup →
    T.facet o = (if 0 < Num.dot (perp2 (T.x b - T.x a)) (T.x o - T.x a) then -1 else 1 : ℝ) • perp2 (T.x b - T.x a)

/-- P3-11.4b (d = 2): side balance implies facet balance. -/
def P3_11_4b : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype C] (M : WMesh ι C 2)
    (bd : C × Fin 3 → Bool), M.Valid → SideBalanced2 M bd → M.FacetBalanced bd

end CFDLean.JST1.Spec
