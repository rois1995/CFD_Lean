import CFDLean.Papers.JST1.Mixed.Assembly
import CFDLean.Papers.JST1.Spec.Item11b
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Statements of item 11, stage 3 (P3): the geometric chain of `lem:avg` (lines 683-690, proof 957-966) from
affine cells and their pulling splits to the facet balance of the assembled mesh (review S1 of stage 2). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec
open CFDLean.JST1.RefCell CFDLean.JST1.Mixed

/-- Local vertex `0` of a reference cell. -/
def kz (k : Kind) : Fin k.n := ⟨0, by cases k <;> simp [Kind.n]⟩

/-- Side of `x` against the face `f` (a local vertex list) at the positions `X`. -/
def sideF {n : ℕ} (X : Fin n → Vec 3) (f : List (Fin n)) (z : Fin n) (x : Vec 3) : ℝ :=
  sideOf (X (f.getD 0 z)) (X (f.getD 1 z)) (X (f.getD 2 z)) x

/-- P3-11.7 (geometry of the pulling splits): for every affine image `X = A·ref + b` (`det A ≠ 0`) of a reference
cell and every pulling split: every sub-tetrahedron is nondegenerate; two different sub-tetrahedra that share a
triangle inside the cell lie on opposite sides of it; a sub-tetrahedron with a face on the cell boundary lies on the
side of the cell centroid. -/
def P3_11_7 : Prop :=
  ∀ (k : Kind) (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3), A.det ≠ 0 →
    let X : Fin k.n → Vec 3 := fun a => A.mulVec (k.ref a) + b
    let cen : Vec 3 := (1 / (k.n : ℝ)) • ∑ a, X a
    ∀ s ∈ k.cell.splits,
      (∀ t ∈ k.cell.pull s.1 s.2, (realize X t (kz k)).Nondeg) ∧
      (∀ t ∈ k.cell.pull s.1 s.2, ∀ t' ∈ k.cell.pull s.1 s.2, ∀ f ∈ tetFaces t,
        sameSimplex t t' = false → (tetFaces t').any (sameSimplex f) = true → onCellFace k.cell f = false →
        sideF X f (kz k) (X (oppV t f (kz k))) * sideF X f (kz k) (X (oppV t' f (kz k))) < 0) ∧
      (∀ t ∈ k.cell.pull s.1 s.2, ∀ f ∈ tetFaces t, onCellFace k.cell f = true →
        0 < sideF X f (kz k) (X (oppV t f (kz k))) * sideF X f (kz k) cen)

/-- P3-11.8 (`lem:avg`, closure on mixed meshes): a conforming mesh of affine hexahedra, prisms and pyramids, each
averaged over its pulling splits with equal weights, assembles to a valid weighted tetrahedral mesh that is facet
balanced (boundary facets: those whose vertex set is a boundary triangle). With P3-11.1, `Σ_k n_ik = 0` at every
vertex on no boundary triangle, and P3-14 applies. -/
def P3_11_8 : Prop :=
  ∀ (ι Cl : Type) [Fintype ι] [DecidableEq ι] [Fintype Cl] [DecidableEq Cl] (M : Mesh ι Cl)
    (bdTris : Finset (Finset ι)), M.Affine → M.Conform bdTris →
    M.toW.Valid ∧ M.toW.FacetBalanced (fun p => decide (M.toW.facetNodes p ∈ bdTris))

end CFDLean.JST1.Spec
