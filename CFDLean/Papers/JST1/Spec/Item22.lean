import CFDLean.Papers.JST1.Spec.Item11c
set_option cleanup.letToHave false -- keep the `let` binders of the statements (as P1-P6)

/-! Statements of item 22 (P7): `lem:avg` (paper sha256 `5ec5f9db…`, lines 683-690, proof 988-998) on mixed meshes
whose cells are not affine images of the reference cells (general hexahedra, prisms and pyramids with free vertex
positions), and the counterexample of paper gap G8 (a valid trilinear hexahedron whose pulling splits are not
conforming triangulations). Proposal: `specifications/JST1/P7-proposal.md`. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec
open CFDLean.JST1.RefCell CFDLean.JST1.Mixed

/-- Signed volume (times 6) of a list of four local vertices at the positions `X`. -/
def tetDet {n : ℕ} (X : Fin n → Vec 3) (t : List (Fin n)) (dflt : Fin n) : ℝ := (realize X t dflt).edgeMat.det

/-- Every sub-tetrahedron of every pulling split of a cell of kind `k` with vertex positions `X` is nondegenerate,
and all have one common orientation relative to the reference cell (`σ = ±1`). -/
def SplitOriented (k : Kind) (X : Fin k.n → Vec 3) : Prop :=
  ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ t ∈ k.tets, 0 < σ * tetDet X t (kz k) * tetDet k.ref t (kz k)

/-- Vertex positions of a cell taken from the mesh (no affine map). -/
def cellPos {ι Cl : Type} (M : Mesh ι Cl) (c : Cl) (a : Fin (M.cell c).kind.n) : Vec 3 := M.pos ((M.cell c).glob a)

/-- Every cell of the mesh is split-oriented at its mesh vertex positions. -/
def MeshSplitOriented {ι Cl : Type} (M : Mesh ι Cl) : Prop := ∀ c, SplitOriented (M.cell c).kind (cellPos M c)

/-- Conformity with a sub-tetrahedron side test: as `Mesh.Conform`, but at a face triangle `S` shared by two cells,
every sub-tetrahedron of one cell and every sub-tetrahedron of the other that have `S` as a face lie on opposite
sides of `S` (their vertices off `S`, against any ordering `a b c` of `S`). -/
def ConformT {ι Cl : Type} [DecidableEq ι] [Fintype Cl] (M : Mesh ι Cl) (bdTris : Finset (Finset ι)) : Prop :=
  ∀ c S fl, (S, fl) ∈ (M.cell c).faceTris →
    (S ∈ bdTris ∧ ∀ c', c' ≠ c → ∀ fl', (S, fl') ∉ (M.cell c').faceTris) ∨
    (S ∉ bdTris ∧ ∃ c', c' ≠ c ∧ (S, fl) ∈ (M.cell c').faceTris ∧
      (∀ c'', c'' ≠ c → ∀ fl'', (S, fl'') ∈ (M.cell c'').faceTris → c'' = c') ∧
      ∀ xa xb xc : ι, S = {xa, xb, xc} →
        ∀ t ∈ (M.cell c).kind.tets, ∀ v ∈ t, S ⊆ (t.map (M.cell c).glob).toFinset → (M.cell c).glob v ∉ S →
        ∀ t' ∈ (M.cell c').kind.tets, ∀ v' ∈ t', S ⊆ (t'.map (M.cell c').glob).toFinset →
          (M.cell c').glob v' ∉ S →
          sideOf (M.pos xa) (M.pos xb) (M.pos xc) (cellPos M c v) *
            sideOf (M.pos xa) (M.pos xb) (M.pos xc) (cellPos M c' v') < 0)

/-- P7-22.1 (`lem:avg`, cell level, extends P3-11.7 to free vertex positions): if every pulling sub-tetrahedron of a
cell is nondegenerate with one common orientation, then in every pulling split two different sub-tetrahedra that
share a triangle inside the cell lie on opposite sides of it; and all sub-tetrahedra (of all pulling splits) that
have a given triangle of a cell face as a face lie on one side of it (the convexity clause of P3-11.7, without the
centroid, which need not be on that side for a non-convex cell). -/
def P7_22_1 : Prop :=
  ∀ (k : Kind) (X : Fin k.n → Vec 3), SplitOriented k X →
    ∀ s ∈ k.cell.splits,
      (∀ t ∈ k.cell.pull s.1 s.2, (realize X t (kz k)).Nondeg) ∧
      (∀ t ∈ k.cell.pull s.1 s.2, ∀ t' ∈ k.cell.pull s.1 s.2, ∀ f ∈ tetFaces t,
        sameSimplex t t' = false → (tetFaces t').any (sameSimplex f) = true → onCellFace k.cell f = false →
        sideF X f (kz k) (X (oppV t f (kz k))) * sideF X f (kz k) (X (oppV t' f (kz k))) < 0) ∧
      (∀ t ∈ k.tets, ∀ t' ∈ k.tets, ∀ f ∈ tetFaces t, onCellFace k.cell f = true →
        (tetFaces t').any (sameSimplex f) = true →
        0 < sideF X f (kz k) (X (oppV t f (kz k))) * sideF X f (kz k) (X (oppV t' f (kz k))))

/-- P7-22.2 (`lem:avg`, closure on mixed meshes with general cells, extends P3-11.8): a mesh of hexahedra, prisms and
pyramids with free vertex positions, every cell split-oriented, conforming with the sub-tetrahedron side test, and
averaged over its pulling splits with equal weights, assembles to a valid weighted tetrahedral mesh that is facet
balanced (boundary facets: those whose vertex set is a boundary triangle). -/
def P7_22_2 : Prop :=
  ∀ (ι Cl : Type) [Fintype ι] [DecidableEq ι] [Fintype Cl] [DecidableEq Cl] (M : Mesh ι Cl)
    (bdTris : Finset (Finset ι)), MeshSplitOriented M → ConformT M bdTris →
    M.toW.Valid ∧ M.toW.FacetBalanced (fun p => decide (M.toW.facetNodes p ∈ bdTris))

/-- P7-22.3 (P3-11.8 is a special case of P7-22.2): affine cells are split-oriented, and an affine mesh that is
conforming with the centroid test is conforming with the sub-tetrahedron side test. -/
def P7_22_3 : Prop :=
  ∀ (ι Cl : Type) [Fintype ι] [DecidableEq ι] [Fintype Cl] [DecidableEq Cl] (M : Mesh ι Cl)
    (bdTris : Finset (Finset ι)), M.Affine → MeshSplitOriented M ∧ (M.Conform bdTris → ConformT M bdTris)

/-- The twisted cube: the unit cube (vertex numbering of `RefCell.hex`) with its top face turned about the vertical
axis through `(½, ½)` by the angle with `cos θ = 3/5`, `sin θ = 4/5`. -/
def twistX : Fin 8 → Vec 3 :=
  ![![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![0, 1, 0],
    ![3 / 5, -1 / 5, 1], ![6 / 5, 3 / 5, 1], ![2 / 5, 6 / 5, 1], ![-1 / 5, 2 / 5, 1]]

/-- Trilinear map of a hexahedron with vertex positions `X` on the reference cube `[0,1]³`:
`Σ_a N_a(ξ) X_a`, `N_a(ξ) = Π_α (r_aα ξ_α + (1 - r_aα)(1 - ξ_α))` with `r_a` the reference vertex `a`. -/
def trilin (X : Fin 8 → Vec 3) (ξ : Vec 3) : Vec 3 :=
  ∑ a, (∏ α, (Kind.hex.ref a α * ξ α + (1 - Kind.hex.ref a α) * (1 - ξ α))) • X a

/-- The one-cell mesh of the twisted cube (global vertices `Fin 8`, the affine fields unused), and its boundary
triangles: all face triangles of the cell. -/
def twistMesh : Mesh (Fin 8) Unit where
  pos := twistX
  cell _ := ⟨.hex, Function.Embedding.refl _, 1, 0⟩
  emb0 := ⟨Fin.castLE (by norm_num), Fin.castLE_injective (by norm_num)⟩

def twistBd : Finset (Finset (Fin 8)) := ((twistMesh.cell ()).faceTris.map Prod.fst).toFinset

/-- P7-22.4 (paper gap G8): the twisted cube is a valid trilinear hexahedron (the trilinear map takes the reference
vertices to `twistX` and its Jacobian determinant is positive on `[0,1]³`), but it is not split-oriented. Its
one-cell mesh is conforming in both senses (trivially: all faces are boundary faces), so split orientation is the
only hypothesis of P7-22.2 that fails; and the mesh is not facet balanced, and the boundary formula of `β` that
P3-11.1 derives from facet balance (`β_i = ⅓ Σ` of the boundary facet vectors at `i`, the discrete
`∮_{∂Ω} φ_i N`) fails at some vertex: the closure of `lem:avg` fails on this cell. -/
def P7_22_4 : Prop :=
  (∀ a, trilin twistX (Kind.hex.ref a) = twistX a) ∧
  (∀ ξ : Vec 3, (∀ α, 0 ≤ ξ α ∧ ξ α ≤ 1) → 0 < (fderiv ℝ (trilin twistX) ξ).det) ∧
  ¬ SplitOriented .hex twistX ∧
  twistMesh.Conform twistBd ∧ ConformT twistMesh twistBd ∧
  ¬ twistMesh.toW.FacetBalanced (fun p => decide (twistMesh.toW.facetNodes p ∈ twistBd)) ∧
  ∃ i, twistMesh.toW.beta i ≠ ∑ p, if decide (twistMesh.toW.facetNodes p ∈ twistBd) = true ∧
      i ∈ twistMesh.toW.facetNodes p then (1 / (3 : ℝ)) • twistMesh.toW.areaVec p else 0

end CFDLean.JST1.Spec
