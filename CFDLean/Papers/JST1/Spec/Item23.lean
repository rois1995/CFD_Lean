import CFDLean.Papers.JST1.Spec.Item22
set_option cleanup.letToHave false -- keep the `let` binders of the statements (as P1-P7)

/-! Statements of item 23 (P8): two extensions of the counterexample of paper gap G8 (`lem:avg`, paper lines 683-690,
proof 988-998, and the neighbour-fan rule of `prop:splits`, lines 691-700). The neighbour-fan (Kuhn) splits are not
always triangulations of a valid trilinear hexahedron either, and on a conforming mesh of valid hexahedra the closure
fails at an interior vertex. Proposal: `specifications/JST1/P8-proposal.md`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec
open CFDLean.JST1.RefCell CFDLean.JST1.Mixed

/-- A cube with its top face turned about the vertical axis through `(½, ½)` by the angle with `cos θ = -7/25`,
`sin θ = 24/25` (about 106°), vertex numbering of `RefCell.hex`. -/
def kuhnX : Fin 8 → Vec 3 :=
  ![![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![0, 1, 0],
    ![28 / 25, 4 / 25, 1], ![21 / 25, 28 / 25, 1], ![-3 / 25, 21 / 25, 1], ![4 / 25, -3 / 25, 1]]

/-- P8-23.1 (G8 for the neighbour-fan subset of `prop:splits`): `kuhnX` is a valid trilinear hexahedron (vertices
mapped, Jacobian determinant positive on `[0,1]³`), but one of its neighbour-fan (Kuhn) splits is not a triangulation:
two of its sub-tetrahedra share a triangle inside the cell and lie on the same side of it. -/
def P8_23_1 : Prop :=
  (∀ a, trilin kuhnX (Kind.hex.ref a) = kuhnX a) ∧
  (∀ ξ : Vec 3, (∀ α, 0 ≤ ξ α ∧ ξ α ≤ 1) → 0 < (fderiv ℝ (trilin kuhnX) ξ).det) ∧
  ∃ s ∈ RefCell.hex.fanSplits (nbrOf hexEdges), ∃ t ∈ RefCell.hex.pull s.1 s.2, ∃ t' ∈ RefCell.hex.pull s.1 s.2,
    ∃ f ∈ tetFaces t, sameSimplex t t' = false ∧ (tetFaces t').any (sameSimplex f) = true ∧
      onCellFace RefCell.hex f = false ∧
      0 < sideF kuhnX f 0 (kuhnX (oppV t f 0)) * sideF kuhnX f 0 (kuhnX (oppV t' f 0))

/-- Vertices of the `3 × 3 × 3` grid, `g = i + 3j + 9k`: the unit grid, with the top layer `k = 2` turned about the
vertical axis through `(1, 1)` by the angle with `cos θ = 3/5`, `sin θ = 4/5`. -/
def blockPos (g : Fin 27) : Vec 3 :=
  let i : ℝ := (g.val % 3 : ℕ)
  let j : ℝ := (g.val / 3 % 3 : ℕ)
  let k : ℕ := g.val / 9
  if k = 2 then ![1 + 3 / 5 * (i - 1) - 4 / 5 * (j - 1), 1 + 4 / 5 * (i - 1) + 3 / 5 * (j - 1), 2]
  else ![i, j, (k : ℝ)]

/-- Global vertex of the local vertex `a` (numbering of `RefCell.hex`) of the cell `c = ci + 2cj + 4ck` of the
`2 × 2 × 2` block. -/
def blockIdx (c a : Fin 8) : Fin 27 :=
  ⟨((c.val % 2 + ![0, 1, 1, 0, 0, 1, 1, 0] a) + 3 * (c.val / 2 % 2 + ![0, 0, 1, 1, 0, 0, 1, 1] a) +
    9 * (c.val / 4 + ![0, 0, 0, 0, 1, 1, 1, 1] a)) % 27, Nat.mod_lt _ (by norm_num)⟩

theorem blockIdx_inj : ∀ c, Function.Injective (blockIdx c) := by decide

/-- Vertex positions of the cell `c`. -/
def blockX (c a : Fin 8) : Vec 3 := blockPos (blockIdx c a)

/-- The mesh of the eight hexahedra of the block. The cells are not affine (`Mesh.Affine` fails); their affine fields
are `A = 1` and `b` chosen so that `Cell.centroid` (used by the centroid test of `Mesh.Conform`) is the average of the
eight vertices of the cell. -/
def blockMesh : Mesh (Fin 27) (Fin 8) where
  pos := blockPos
  cell c := ⟨.hex, ⟨blockIdx c, blockIdx_inj c⟩, 1, (1 / 8 : ℝ) • ∑ a, blockX c a - ![1 / 2, 1 / 2, 1 / 2]⟩
  emb0 := ⟨Fin.castLE (by norm_num), Fin.castLE_injective (by norm_num)⟩

/-- The face triangles of a cell as vertex sets. -/
def faceSets {ι : Type} [DecidableEq ι] (c : Cell ι) : Finset (Finset ι) := (c.faceTris.map Prod.fst).toFinset

/-- Boundary triangles of a mesh: the face triangles of exactly one cell. -/
def bdTrisOf {ι Cl : Type} [DecidableEq ι] [Fintype Cl] (M : Mesh ι Cl) : Finset (Finset ι) :=
  (Finset.univ.biUnion fun c => faceSets (M.cell c)).filter fun S =>
    (Finset.univ.filter fun c => S ∈ faceSets (M.cell c)).card = 1

/-- P8-23.2 (G8 at an interior vertex): the block is a conforming mesh (`Mesh.Conform`, centroid test with the true
vertex averages) of valid trilinear hexahedra (vertices mapped, Jacobian determinant positive on `[0,1]³` for every
cell; the four lower cells are unit cubes, the four upper cells are twisted); the central vertex `13 = (1, 1, 1)` lies
on no boundary triangle; yet, averaged over the pulling splits, `Σ_k n_ik = (0, 0, 7/30) ≠ 0` there (`β_i = -Σ_k n_ik`):
the closure `Σ_k n_ik = 0` at interior vertices of `lem:avg` fails. The cause is that the pulling splits of the
twisted cells are not triangulations (inverted sub-tetrahedra enter with positive measure `|T|`). The block also fails
the sub-tetrahedron side test `ConformT` of P7-22.2 at 16 shared triangles, so it violates both extra hypotheses of
P7-22.2 while meeting the paper's conformity. -/
def P8_23_2 : Prop :=
  (∀ c a, trilin (blockX c) (Kind.hex.ref a) = blockX c a) ∧
  (∀ c, ∀ ξ : Vec 3, (∀ α, 0 ≤ ξ α ∧ ξ α ≤ 1) → 0 < (fderiv ℝ (trilin (blockX c)) ξ).det) ∧
  blockMesh.Conform (bdTrisOf blockMesh) ∧
  (∀ S ∈ bdTrisOf blockMesh, (13 : Fin 27) ∉ S) ∧
  ∑ k, blockMesh.toW.n 13 k = ![0, 0, 7 / 30]

end CFDLean.JST1.Spec
