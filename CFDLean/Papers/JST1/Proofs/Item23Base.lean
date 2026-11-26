import CFDLean.Papers.JST1.Spec.Item23
import CFDLean.Papers.JST1.Proofs.Item22

/-! Item 23 (P8), part 1: layered cells (closed-form trilinear map and Jacobian), the Kuhn cell and the block cells in
layered form, integer coordinates of the block, centroids, boundary triangles, and the facet data of the block. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs
namespace Ext23

open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec Asm11

/-- A layered hexahedron (vertex numbering of `RefCell.hex`). -/
def layX (bx by' z0 a11 a12 a21 a22 t1 t2 : ℝ) : Fin 8 → Vec 3 :=
  ![![bx, by', z0], ![bx + 1, by', z0], ![bx + 1, by' + 1, z0], ![bx, by' + 1, z0],
    ![a11 * bx + a12 * by' + t1, a21 * bx + a22 * by' + t2, z0 + 1],
    ![a11 * (bx + 1) + a12 * by' + t1, a21 * (bx + 1) + a22 * by' + t2, z0 + 1],
    ![a11 * (bx + 1) + a12 * (by' + 1) + t1, a21 * (bx + 1) + a22 * (by' + 1) + t2, z0 + 1],
    ![a11 * bx + a12 * (by' + 1) + t1, a21 * bx + a22 * (by' + 1) + t2, z0 + 1]]

/-- Its trilinear map in closed form. -/
def layG (bx by' z0 a11 a12 a21 a22 t1 t2 : ℝ) (ξ : Vec 3) : Vec 3 :=
  ![(1 - ξ 2) * (bx + ξ 0) + ξ 2 * (a11 * (bx + ξ 0) + a12 * (by' + ξ 1) + t1),
    (1 - ξ 2) * (by' + ξ 1) + ξ 2 * (a21 * (bx + ξ 0) + a22 * (by' + ξ 1) + t2), z0 + ξ 2]

theorem trilin_lay (bx by' z0 a11 a12 a21 a22 t1 t2 : ℝ) :
    trilin (layX bx by' z0 a11 a12 a21 a22 t1 t2) = layG bx by' z0 a11 a12 a21 a22 t1 t2 := by
  funext ξ
  ext α
  rw [Twist22.trilin_def]
  fin_cases α <;>
    simp [layX, layG, Fin.sum_univ_eight, Fin.prod_univ_three, Kind.ref] <;> ring

theorem vertices_lay (bx by' z0 a11 a12 a21 a22 t1 t2 : ℝ) :
    ∀ a : Fin 8, trilin (layX bx by' z0 a11 a12 a21 a22 t1 t2) (Kind.hex.ref a) =
      layX bx by' z0 a11 a12 a21 a22 t1 t2 a := by
  intro a
  rw [trilin_lay]
  ext α
  fin_cases a <;> fin_cases α <;> simp [layX, layG, Kind.ref]

/-- Its Jacobian matrix. -/
def layJ (bx by' a11 a12 a21 a22 t1 t2 : ℝ) (ξ : Vec 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1 - ξ 2) + ξ 2 * a11, ξ 2 * a12, -(bx + ξ 0) + (a11 * (bx + ξ 0) + a12 * (by' + ξ 1) + t1);
     ξ 2 * a21, (1 - ξ 2) + ξ 2 * a22, -(by' + ξ 1) + (a21 * (bx + ξ 0) + a22 * (by' + ξ 1) + t2);
     0, 0, 1]

theorem hasFDerivAt_lay (bx by' z0 a11 a12 a21 a22 t1 t2 : ℝ) (ξ : Vec 3) :
    HasFDerivAt (layG bx by' z0 a11 a12 a21 a22 t1 t2)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (layJ bx by' a11 a12 a21 a22 t1 t2 ξ))) ξ := by
  rw [hasFDerivAt_pi']
  intro i
  have p0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) ξ
  have p1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) ξ
  have p2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) ξ
  have ux := (hasFDerivAt_const bx ξ).add p0
  have uy := (hasFDerivAt_const by' ξ).add p1
  have w1 := (hasFDerivAt_const 1 ξ).sub p2
  fin_cases i
  · have h := (w1.mul ux).add (p2.mul (((ux.const_mul a11).add (uy.const_mul a12)).add (hasFDerivAt_const t1 ξ)))
    refine h.congr_fderiv ?_
    ext v
    simp [layJ, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    ring
  · have h := (w1.mul uy).add (p2.mul (((ux.const_mul a21).add (uy.const_mul a22)).add (hasFDerivAt_const t2 ξ)))
    refine h.congr_fderiv ?_
    ext v
    simp [layJ, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]
    ring
  · refine ((hasFDerivAt_const z0 ξ).add p2).congr_fderiv ?_
    ext v
    simp [layJ, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three]

theorem det_lay (bx by' z0 a11 a12 a21 a22 t1 t2 : ℝ) (ξ : Vec 3) :
    (fderiv ℝ (trilin (layX bx by' z0 a11 a12 a21 a22 t1 t2)) ξ).det =
      ((1 - ξ 2) + ξ 2 * a11) * ((1 - ξ 2) + ξ 2 * a22) - ξ 2 * a12 * (ξ 2 * a21) := by
  rw [trilin_lay, (hasFDerivAt_lay bx by' z0 a11 a12 a21 a22 t1 t2 ξ).fderiv,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin', Matrix.det_fin_three]
  simp [layJ]

/-- A rotation layer (`c² + s² = 1`, `c > -1`) has a positive Jacobian on the unit cube. -/
theorem det_rot_pos (c s w : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (hc : -1 < c) :
    0 < ((1 - w) + w * c) * ((1 - w) + w * c) - w * (-s) * (w * s) := by
  have e : ((1 - w) + w * c) * ((1 - w) + w * c) - w * (-s) * (w * s) = 1 - 2 * w * (1 - w) * (1 - c) := by
    linear_combination w ^ 2 * hcs
  rw [e]
  nlinarith [sq_nonneg (w - 1 / 2)]

theorem kuhnX_eq : kuhnX = layX 0 0 0 (-7 / 25) (-(24 / 25)) (24 / 25) (-7 / 25) (28 / 25) (4 / 25) := by
  funext a
  ext α
  fin_cases a <;> fin_cases α <;> simp [kuhnX, layX] <;> norm_num

set_option maxHeartbeats 4000000 in
/-- The layered parameters of the block cells: unit cubes below, cells with the turned top layer above. -/
theorem blockX_eq (c : Fin 8) : blockX c =
    if c.val < 4 then layX (c.val % 2 : ℕ) (c.val / 2 % 2 : ℕ) 0 1 0 0 1 0 0
    else layX (c.val % 2 : ℕ) (c.val / 2 % 2 : ℕ) 1 (3 / 5) (-(4 / 5)) (4 / 5) (3 / 5) (6 / 5) (-(2 / 5)) := by
  funext a
  ext α
  fin_cases c <;> fin_cases a <;> fin_cases α <;> simp [blockX, blockIdx, blockPos, layX] <;> norm_num


/-! ### The block: integer coordinates (`5 · blockPos`) -/

def bZ (g : Fin 27) : Z3 :=
  if g.val / 9 = 2 then
    (5 + 3 * ((g.val % 3 : ℕ) - 1 : ℤ) - 4 * ((g.val / 3 % 3 : ℕ) - 1 : ℤ),
      5 + 4 * ((g.val % 3 : ℕ) - 1 : ℤ) + 3 * ((g.val / 3 % 3 : ℕ) - 1 : ℤ), 10)
  else (5 * (g.val % 3 : ℕ), 5 * (g.val / 3 % 3 : ℕ), 5 * (g.val / 9 : ℕ))

set_option maxHeartbeats 4000000 in
theorem blockPos_eq (g : Fin 27) : blockPos g = (1 / 5 : ℝ) • castZ3 (bZ g) := by
  ext α
  fin_cases g <;> fin_cases α <;> simp [blockPos, bZ, castZ3] <;> norm_num

/-- Sum of the integer vertex coordinates of a cell. -/
def sumZ (c : Fin 8) : Z3 := ((List.finRange 8).map fun a => bZ (blockIdx c a)).sum

/-- `8 · 5³` times the side of the point with coordinates `s/40` against the triangle `a b c` (coordinates `/5`). -/
def EZ (a b c s : Z3) : ℤ := dtZ (crsZ (subZ b a) (subZ c a)) (subZ s (8 * a.1, 8 * a.2.1, 8 * a.2.2))

theorem castZ3_sum (l : List Z3) : castZ3 l.sum = (l.map castZ3).sum := by
  induction l with
  | nil => ext i; fin_cases i <;> simp [castZ3]
  | cons x l ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    exact map_add Twist22.castHom x l.sum

theorem centroid_eq (c : Fin 8) :
    (blockMesh.cell c).centroid = (1 / 5 : ℝ) • ((1 / ((8 : ℕ) : ℝ)) • castZ3 (sumZ c)) := by
  have h1 : (blockMesh.cell c).centroid = (1 / ((8 : ℕ) : ℝ)) • ∑ a : Fin 8,
      ((1 : Matrix (Fin 3) (Fin 3) ℝ).mulVec (Kind.hex.ref a) +
        ((1 / 8 : ℝ) • ∑ a, blockX c a - ![1 / 2, 1 / 2, 1 / 2])) := rfl
  have h2 : castZ3 (sumZ c) = ∑ a : Fin 8, castZ3 (bZ (blockIdx c a)) := by
    rw [sumZ, castZ3_sum, List.map_map, List.finRange, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [h1, h2]
  simp only [blockX, blockPos_eq, Matrix.one_mulVec]
  ext α
  fin_cases α <;>
    simp [Fin.sum_univ_eight, Kind.ref, castZ3] <;> ring

theorem side_cen_b (c : Fin 8) (xa xb xc : Fin 27) :
    sideOf (blockMesh.pos xa) (blockMesh.pos xb) (blockMesh.pos xc) (blockMesh.cell c).centroid =
      (1 / 5 : ℝ) ^ 3 * ((1 / ((8 : ℕ) : ℝ)) * (EZ (bZ xa) (bZ xb) (bZ xc) (sumZ c) : ℝ)) := by
  rw [centroid_eq, show blockMesh.pos = blockPos from rfl, blockPos_eq, blockPos_eq, blockPos_eq,
    Twist22.sideOf_smul, sideOf_cen _ _ _ _ 8 (by norm_num)]
  rfl

/-- A boundary triangle belongs to one cell only. -/
theorem bd_unique {ι Cl : Type} [DecidableEq ι] [Fintype Cl] [DecidableEq Cl] (M : Mesh ι Cl) {S : Finset ι}
    (hS : S ∈ bdTrisOf M) {c c' : Cl} (hc : S ∈ faceSets (M.cell c)) (hc' : S ∈ faceSets (M.cell c')) : c' = c := by
  simp only [bdTrisOf, Finset.mem_filter] at hS
  obtain ⟨-, h1⟩ := hS
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
  have m : ∀ y, S ∈ faceSets (M.cell y) → y = x := by
    intro y hy
    have : y ∈ Finset.univ.filter fun c => S ∈ faceSets (M.cell c) := by simp [hy]
    rw [hx] at this
    simpa using this
  rw [m c' hc', m c hc]

theorem mem_faceSets {ι : Type} [DecidableEq ι] (c : Cell ι) {S : Finset ι} {fl : Bool} (h : (S, fl) ∈ c.faceTris) :
    S ∈ faceSets c := by
  simp only [faceSets, List.mem_toFinset, List.mem_map]
  exact ⟨(S, fl), h, rfl⟩

/-! ### The block: facet vectors and the sum at vertex 13 -/

/-- A sub-tetrahedron of the block mesh as a list of local vertices of `Fin 8`. -/
def bT (x : Σ c : Fin 8, Fin (blockMesh.cell c).kind.tets.length) : List (Fin 8) :=
  (blockMesh.cell x.1).kind.tets.get x.2

theorem tet_mem_b (x : Σ c : Fin 8, Fin (blockMesh.cell c).kind.tets.length) :
    bT x ∈ (Kind.hex.tets : List (List (Fin 8))) := List.get_mem _ x.2

theorem vert_b (x : Σ c : Fin 8, Fin (blockMesh.cell c).kind.tets.length) (a : Fin 4) :
    blockMesh.toW.vert x a = blockIdx x.1 ((bT x).getD a 0) := by
  rw [vert_eq]
  dsimp only [blockMesh, bT]
  rfl

def nodesB (c : Fin 8) (t : List (Fin 8)) (o : Fin 4) : Finset (Fin 27) :=
  {blockIdx c (t.getD (o.succAbove 0) 0), blockIdx c (t.getD (o.succAbove 1) 0), blockIdx c (t.getD (o.succAbove 2) 0)}

theorem nodes_b (p : (Σ c : Fin 8, Fin (blockMesh.cell c).kind.tets.length) × Fin 4) :
    blockMesh.toW.facetNodes p = nodesB p.1.1 (bT p.1) p.2 := by
  rw [WMesh.facetNodes, Twist22.erase_eq, Finset.map_insert, Finset.map_insert, Finset.map_singleton, vert_b, vert_b,
    vert_b]
  rfl

/-- `-3200` times the area vector of a facet of a sub-tetrahedron of the cell `c` (weight `1/64`, coordinates `bZ`). -/
def AZB (c : Fin 8) (t : List (Fin 8)) (o : Fin 4) : Z3 :=
  Twist22.smulZ (Int.sign (sideZ (bZ (blockIdx c (t.getD (o.succAbove 0) 0))) (bZ (blockIdx c (t.getD (o.succAbove 1) 0)))
      (bZ (blockIdx c (t.getD (o.succAbove 2) 0))) (bZ (blockIdx c (t.getD o 0)))))
    (crsZ (subZ (bZ (blockIdx c (t.getD (o.succAbove 1) 0))) (bZ (blockIdx c (t.getD (o.succAbove 0) 0))))
      (subZ (bZ (blockIdx c (t.getD (o.succAbove 2) 0))) (bZ (blockIdx c (t.getD (o.succAbove 0) 0)))))

def intSB (c : Fin 8) (Q : List (Fin 8) → Fin 4 → Bool) : Z3 :=
  (Kind.hex.tets.map fun (t : List (Fin 8)) =>
    ((List.finRange 4).map fun o => if Q t o then AZB c t o else 0).sum).sum

/-! ### Fast forms for the kernel checks (see `docs/LEAN_PERFORMANCE.md`, rule 2): no case split on `Kind` inside
the loops; each is tied to the original by `rfl`. -/

/-- The 384 sub-tetrahedra of the pulling splits of the hexahedron, built from `RefCell.hex` directly. -/
def hexTetsF : List (List (Fin 8)) := RefCell.hex.splits.flatMap fun s => RefCell.hex.pull s.1 s.2

theorem hexTets_eq : (Kind.hex.tets : List (List (Fin 8))) = hexTetsF := rfl

/-- The face triangles of the block cell `c`, built from `RefCell.hex` directly. -/
def blockFT (c : Fin 8) : List (Finset (Fin 27) × Bool) :=
  (RefCell.hex.quads.flatMap fun q => (q.tris false ++ q.tris true).map fun f =>
      ((f.map (blockIdx c)).toFinset, true)) ++
    RefCell.hex.tris.map fun f => ((f.map (blockIdx c)).toFinset, false)

theorem blockFT_eq (c : Fin 8) : (blockMesh.cell c).faceTris = blockFT c := rfl

/-- The boundary triangles of the block, from `blockFT`. -/
def bdF : Finset (Finset (Fin 27)) :=
  (Finset.univ.biUnion fun c => (blockFT c |>.map Prod.fst).toFinset).filter fun S =>
    (Finset.univ.filter fun c => S ∈ (blockFT c |>.map Prod.fst).toFinset).card = 1

theorem bdF_eq : bdTrisOf blockMesh = bdF := rfl

end Ext23
end CFDLean.JST1.Proofs
