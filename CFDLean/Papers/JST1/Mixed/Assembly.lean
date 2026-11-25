import CFDLean.Papers.JST1.Mixed.RefCells
import CFDLean.Geometry.MeshBoundary

/-! Mixed meshes made of affine images of the reference cells (hexahedron, prism, pyramid), each cell averaged over
all its pulling splits with equal weights, and the weighted tetrahedral mesh they assemble to (paper Section
`sec:mixed`, `lem:avg`). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1
namespace Mixed
open RefCell

inductive Kind where
  | hex
  | prism
  | pyr
  deriving DecidableEq

def Kind.n : Kind → ℕ
  | .hex => 8
  | .prism => 6
  | .pyr => 5

def Kind.cell : (k : Kind) → Cell3 k.n
  | .hex => RefCell.hex
  | .prism => RefCell.prism
  | .pyr => RefCell.pyramid

/-- Reference coordinates: unit cube, right prism, square pyramid (base `[0,2]²`, apex `(1,1,2)`). -/
def Kind.ref : (k : Kind) → Fin k.n → Vec 3
  | .hex => ![![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![0, 1, 0], ![0, 0, 1], ![1, 0, 1], ![1, 1, 1], ![0, 1, 1]]
  | .prism => ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1]]
  | .pyr => ![![0, 0, 0], ![2, 0, 0], ![2, 2, 0], ![0, 2, 0], ![1, 1, 2]]

/-- All sub-tetrahedra of all pulling splits (with repetition), and the equal split weight. -/
def Kind.tets (k : Kind) : List (List (Fin k.n)) := k.cell.splits.flatMap fun s => k.cell.pull s.1 s.2
def Kind.w (k : Kind) : ℝ := 1 / (k.cell.splits.length : ℝ)

/-- Cross product and the side of a point relative to an ordered triangle. -/
def cross (u v : Vec 3) : Vec 3 := ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]
def sideOf (xa xb xc x : Vec 3) : ℝ := Num.dot (cross (xb - xa) (xc - xa)) (x - xa)

/-- The vertex of the tetrahedron `t` not in its face `f`. -/
def oppV {n : ℕ} (t f : List (Fin n)) (dflt : Fin n) : Fin n := (t.filter fun v => !f.contains v).getD 0 dflt

/-- A list of four local vertices as a simplex at the positions `X`. -/
def realize {n : ℕ} (X : Fin n → Vec 3) (t : List (Fin n)) (dflt : Fin n) : Simplex 3 :=
  ⟨fun a => X (t.getD a.val dflt)⟩

structure Cell (ι : Type) where
  kind : Kind
  glob : Fin kind.n ↪ ι
  A : Matrix (Fin 3) (Fin 3) ℝ
  b : Vec 3

def Cell.X {ι : Type} (c : Cell ι) (a : Fin c.kind.n) : Vec 3 := c.A.mulVec (c.kind.ref a) + c.b
def Cell.centroid {ι : Type} (c : Cell ι) : Vec 3 := (1 / (c.kind.n : ℝ)) • ∑ a, c.X a

/-- Embedding of a local vertex list into the global vertices (`emb0` if the list is not four distinct vertices;
this never happens for the pulling splits). -/
def tetEmb {ι : Type} (emb0 : Fin 4 ↪ ι) (c : Cell ι) (t : List (Fin c.kind.n)) : Fin 4 ↪ ι :=
  if h : t.length = 4 ∧ t.Nodup then
    ⟨fun a => c.glob (t.get ⟨a.val, by rw [h.1]; exact a.isLt⟩), by
      intro a a' haa
      have h1 := c.glob.injective haa
      have h2 := (List.Nodup.get_inj_iff h.2).1 h1
      exact Fin.ext (by simpa using congrArg Fin.val h2)⟩
  else emb0

structure Mesh (ι Cl : Type) where
  pos : ι → Vec 3
  cell : Cl → Cell ι
  emb0 : Fin 4 ↪ ι

/-- The cells are affine images of their reference cells, with an invertible map. -/
def Mesh.Affine {ι Cl : Type} (M : Mesh ι Cl) : Prop :=
  ∀ c, (M.cell c).A.det ≠ 0 ∧ ∀ a, M.pos ((M.cell c).glob a) = (M.cell c).X a

/-- The assembled weighted tetrahedral mesh: every sub-tetrahedron of every pulling split of every cell. -/
def Mesh.toW {ι Cl : Type} [Fintype Cl] (M : Mesh ι Cl) :
    WMesh ι (Σ c : Cl, Fin (M.cell c).kind.tets.length) 3 where
  pos := M.pos
  vert x := tetEmb M.emb0 (M.cell x.1) ((M.cell x.1).kind.tets.get x.2)
  ω x := (M.cell x.1).kind.w

/-- Face triangles of a cell (both diagonals of its quadrilateral faces) as global vertex sets, with a flag for
quadrilateral faces. -/
def Cell.faceTris {ι : Type} [DecidableEq ι] (c : Cell ι) : List (Finset ι × Bool) :=
  (c.kind.cell.quads.flatMap fun q => (q.tris false ++ q.tris true).map fun f => ((f.map c.glob).toFinset, true)) ++
    c.kind.cell.tris.map fun f => ((f.map c.glob).toFinset, false)

/-- Conformity: every face triangle of a cell is either a boundary triangle (in `bdTris`, of no other cell) or the
face triangle of exactly one other cell, of the same face type (quadrilateral or triangle), and the two cells lie
on opposite sides of it (their centroids, against any ordering `a b c` of the triangle). -/
def Mesh.Conform {ι Cl : Type} [DecidableEq ι] [Fintype Cl] (M : Mesh ι Cl) (bdTris : Finset (Finset ι)) : Prop :=
  ∀ c S fl, (S, fl) ∈ (M.cell c).faceTris →
    (S ∈ bdTris ∧ ∀ c', c' ≠ c → ∀ fl', (S, fl') ∉ (M.cell c').faceTris) ∨
    (S ∉ bdTris ∧ ∃ c', c' ≠ c ∧ (S, fl) ∈ (M.cell c').faceTris ∧
      (∀ c'', c'' ≠ c → ∀ fl'', (S, fl'') ∈ (M.cell c'').faceTris → c'' = c') ∧
      ∀ xa xb xc : ι, S = {xa, xb, xc} →
        sideOf (M.pos xa) (M.pos xb) (M.pos xc) (M.cell c).centroid *
          sideOf (M.pos xa) (M.pos xb) (M.pos xc) (M.cell c').centroid < 0)

end Mixed
end CFDLean.JST1
