import CFDLean.Papers.JST1.Spec.Item11c
import CFDLean.Papers.JST1.Proofs.Geom3
import CFDLean.Papers.JST1.Proofs.Chunks

/-! Helpers for item 11, stage 3 (P3): integer versions of the triple products on the reference cells, their
transfer to affine images, and the closed computations on the pulling splits (checked by the kernel). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs

namespace Asm11

open CFDLean.JST1.RefCell CFDLean.JST1.Mixed CFDLean.JST1.Spec

/-! ### Integer triple products -/

abbrev Z3 := ℤ × ℤ × ℤ

def subZ (a b : Z3) : Z3 := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)
def crsZ (u v : Z3) : Z3 :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)
def dtZ (u v : Z3) : ℤ := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2
def sideZ (xa xb xc x : Z3) : ℤ := dtZ (crsZ (subZ xb xa) (subZ xc xa)) (subZ x xa)

/-- Integer reference coordinates. -/
def refZ : (k : Kind) → Fin k.n → Z3
  | .hex => ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1), (0, 1, 1)]
  | .prism => ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1)]
  | .pyr => ![(0, 0, 0), (2, 0, 0), (2, 2, 0), (0, 2, 0), (1, 1, 2)]

/-- Sum of the reference coordinates. -/
def sumZ : Kind → Z3
  | .hex => (4, 4, 4)
  | .prism => (2, 2, 3)
  | .pyr => (5, 5, 2)

/-- `n` times the side of the centroid against `a0 a1 a2` (reference cell). -/
def cenZ (k : Kind) (a0 a1 a2 : Fin k.n) : ℤ :=
  let R := refZ k a0
  dtZ (crsZ (subZ (refZ k a1) R) (subZ (refZ k a2) R))
    (subZ (sumZ k) ((k.n : ℤ) * R.1, (k.n : ℤ) * R.2.1, (k.n : ℤ) * R.2.2))

def castZ3 (z : Z3) : Vec 3 := ![(z.1 : ℝ), z.2.1, z.2.2]

theorem ref_eq (k : Kind) (a : Fin k.n) : k.ref a = castZ3 (refZ k a) := by
  cases k <;> simp only [Kind.n] at a <;> fin_cases a <;> funext i <;> fin_cases i <;> simp [Kind.ref, refZ, castZ3]

theorem sum_ref (k : Kind) : ∑ a, k.ref a = castZ3 (sumZ k) := by
  cases k <;> unfold Kind.n <;> funext i <;> fin_cases i <;>
    simp [Kind.ref, sumZ, castZ3, Fin.sum_univ_succ] <;> norm_num

theorem sideOf_cast (a b c x : Z3) :
    sideOf (castZ3 a) (castZ3 b) (castZ3 c) (castZ3 x) = (sideZ a b c x : ℝ) := by
  simp only [sideOf, cross, Num.dot, Fin.sum_univ_three, castZ3, sideZ, crsZ, dtZ, subZ, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  push_cast
  ring

theorem sideOf_affine (A : Matrix (Fin 3) (Fin 3) ℝ) (b u v w x : Vec 3) :
    sideOf (A.mulVec u + b) (A.mulVec v + b) (A.mulVec w + b) (A.mulVec x + b) = A.det * sideOf u v w x := by
  simp only [sideOf, cross, Num.dot, Fin.sum_univ_three, Matrix.mulVec, dotProduct, Pi.add_apply, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.det_fin_three]
  ring

theorem sideOf_cen (a b c s : Z3) (n : ℕ) (hn : n ≠ 0) :
    sideOf (castZ3 a) (castZ3 b) (castZ3 c) ((1 / (n : ℝ)) • castZ3 s) =
      (1 / (n : ℝ)) * (dtZ (crsZ (subZ b a) (subZ c a)) (subZ s ((n : ℤ) * a.1, (n : ℤ) * a.2.1, (n : ℤ) * a.2.2))
        : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [sideOf, cross, Num.dot, Fin.sum_univ_three, castZ3, crsZ, dtZ, subZ, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  push_cast
  field_simp

/-- Positions of the affine image of a reference cell. -/
def affX (k : Kind) (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3) (a : Fin k.n) : Vec 3 := A.mulVec (k.ref a) + b

theorem side_aff (k : Kind) (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3) (a0 a1 a2 v : Fin k.n) :
    sideOf (affX k A b a0) (affX k A b a1) (affX k A b a2) (affX k A b v) =
      A.det * (sideZ (refZ k a0) (refZ k a1) (refZ k a2) (refZ k v) : ℝ) := by
  simp only [affX]
  rw [sideOf_affine, ref_eq, ref_eq, ref_eq, ref_eq, sideOf_cast]

theorem n_ne_zero (k : Kind) : k.n ≠ 0 := by cases k <;> simp [Kind.n]

theorem cen_aff (k : Kind) (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3) :
    (1 / (k.n : ℝ)) • ∑ a, affX k A b a = A.mulVec ((1 / (k.n : ℝ)) • castZ3 (sumZ k)) + b := by
  have hn : (k.n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (n_ne_zero k)
  have hs : ∑ a, A.mulVec (k.ref a) = A.mulVec (∑ a, k.ref a) := by
    simpa only [Matrix.mulVecLin_apply] using (map_sum (Matrix.mulVecLin A) (fun a => k.ref a) Finset.univ).symm
  simp only [affX, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hs, sum_ref,
    Matrix.mulVec_smul, smul_add]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div, inv_mul_cancel₀ hn, one_smul]

theorem side_cen (k : Kind) (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Vec 3) (a0 a1 a2 : Fin k.n) :
    sideOf (affX k A b a0) (affX k A b a1) (affX k A b a2) ((1 / (k.n : ℝ)) • ∑ a, affX k A b a) =
      A.det * ((1 / (k.n : ℝ)) * (cenZ k a0 a1 a2 : ℝ)) := by
  rw [cen_aff]
  simp only [affX]
  rw [sideOf_affine, ref_eq, ref_eq, ref_eq, sideOf_cen _ _ _ _ _ (n_ne_zero k)]
  rfl

/-! ### P3-11.7: closed computation on the reference cells -/

section Check
variable (k : Kind)

/-- Integer side of the reference vertex `v` against the face `f`. -/
def sF (f : List (Fin k.n)) (v : Fin k.n) : ℤ :=
  sideZ (refZ k (f.getD 0 (kz k))) (refZ k (f.getD 1 (kz k))) (refZ k (f.getD 2 (kz k))) (refZ k v)

/-- `n` times the integer side of the reference centroid against the face `f`. -/
def cF (f : List (Fin k.n)) : ℤ := cenZ k (f.getD 0 (kz k)) (f.getD 1 (kz k)) (f.getD 2 (kz k))

def checkK : Bool :=
  k.cell.splits.all fun s => (k.cell.pull s.1 s.2).all fun t =>
    (sF k (t.take 3) (t.getD 3 (kz k)) != 0) &&
    (tetFaces t).all fun f =>
      ((k.cell.pull s.1 s.2).all fun t' => sameSimplex t t' || !((tetFaces t').any (sameSimplex f)) ||
         onCellFace k.cell f || decide (sF k f (oppV t f (kz k)) * sF k f (oppV t' f (kz k)) < 0)) &&
      (!onCellFace k.cell f || decide (0 < sF k f (oppV t f (kz k)) * cF k f))

end Check

/-! The same checks with the cell data as plain arguments. The kernel then evaluates the case split on `Kind`
(`Kind.cell`, `refZ`) once, in the `rfl` step below, instead of inside every loop iteration; this makes the closed
computations about 40 times faster. -/

section Generic
variable {n : ℕ} (C : Cell3 n) (R : Fin n → Z3) (S : Z3) (z : Fin n)

def cenZg (a0 a1 a2 : Fin n) : ℤ :=
  let P := R a0
  dtZ (crsZ (subZ (R a1) P) (subZ (R a2) P)) (subZ S ((n : ℤ) * P.1, (n : ℤ) * P.2.1, (n : ℤ) * P.2.2))

def sFg (f : List (Fin n)) (v : Fin n) : ℤ := sideZ (R (f.getD 0 z)) (R (f.getD 1 z)) (R (f.getD 2 z)) (R v)

def cFg (f : List (Fin n)) : ℤ := cenZg R S (f.getD 0 z) (f.getD 1 z) (f.getD 2 z)

def checkKg : Bool :=
  C.splits.all fun s => (C.pull s.1 s.2).all fun t =>
    (sFg R z (t.take 3) (t.getD 3 z) != 0) &&
    (tetFaces t).all fun f =>
      ((C.pull s.1 s.2).all fun t' => sameSimplex t t' || !((tetFaces t').any (sameSimplex f)) ||
         onCellFace C f || decide (sFg R z f (oppV t f z) * sFg R z f (oppV t' f z) < 0)) &&
      (!onCellFace C f || decide (0 < sFg R z f (oppV t f z) * cFg R S z f))

/-- The check of `checkKg` for one split. -/
def checkKf (s : Fin n × List Bool) : Bool :=
  (C.pull s.1 s.2).all fun t =>
    (sFg R z (t.take 3) (t.getD 3 z) != 0) &&
    (tetFaces t).all fun f =>
      ((C.pull s.1 s.2).all fun t' => sameSimplex t t' || !((tetFaces t').any (sameSimplex f)) ||
         onCellFace C f || decide (sFg R z f (oppV t f z) * sFg R z f (oppV t' f z) < 0)) &&
      (!onCellFace C f || decide (0 < sFg R z f (oppV t f z) * cFg R S z f))

theorem checkKg_f : checkKg C R S z = C.splits.all (checkKf C R S z) := rfl

end Generic

/-- Reference coordinates of the three cells as plain functions. -/
def hexR : Fin 8 → Z3 := ![(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1), (0, 1, 1)]
def prismR : Fin 6 → Z3 := ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1)]
def pyrR : Fin 5 → Z3 := ![(0, 0, 0), (2, 0, 0), (2, 2, 0), (0, 2, 0), (1, 1, 2)]

/-- The sub-tetrahedra of all pulling splits of a cell, built from the cell directly (fast form of `Kind.tets`). -/
def tetsOf {n : ℕ} (C : Cell3 n) : List (List (Fin n)) := C.splits.flatMap fun s => C.pull s.1 s.2

theorem hexTets_eq : (Kind.hex.tets : List (List (Fin 8))) = tetsOf RefCell.hex := rfl
theorem prismTets_eq : (Kind.prism.tets : List (List (Fin 6))) = tetsOf RefCell.prism := rfl
theorem pyrTets_eq : (Kind.pyr.tets : List (List (Fin 5))) = tetsOf RefCell.pyramid := rfl

theorem checkK_hex0 :
    ((RefCell.hex.splits.drop (8 * 0)).take 8).all (checkKf RefCell.hex hexR (4, 4, 4) 0) = true := by
  decide +kernel
theorem checkK_hex1 :
    ((RefCell.hex.splits.drop (8 * 1)).take 8).all (checkKf RefCell.hex hexR (4, 4, 4) 0) = true := by
  decide +kernel
theorem checkK_hex2 :
    ((RefCell.hex.splits.drop (8 * 2)).take 8).all (checkKf RefCell.hex hexR (4, 4, 4) 0) = true := by
  decide +kernel
theorem checkK_hex3 :
    ((RefCell.hex.splits.drop (8 * 3)).take 8).all (checkKf RefCell.hex hexR (4, 4, 4) 0) = true := by
  decide +kernel
theorem checkK_hex4 :
    ((RefCell.hex.splits.drop (8 * 4)).take 8).all (checkKf RefCell.hex hexR (4, 4, 4) 0) = true := by
  decide +kernel
theorem checkK_hex5 :
    ((RefCell.hex.splits.drop (8 * 5)).take 8).all (checkKf RefCell.hex hexR (4, 4, 4) 0) = true := by
  decide +kernel
theorem checkK_hex6 :
    ((RefCell.hex.splits.drop (8 * 6)).take 8).all (checkKf RefCell.hex hexR (4, 4, 4) 0) = true := by
  decide +kernel
theorem checkK_hex7 :
    ((RefCell.hex.splits.drop (8 * 7)).take 8).all (checkKf RefCell.hex hexR (4, 4, 4) 0) = true := by
  decide +kernel

/-- The hexahedron in chunks of 8 splits (`all_of_chunks`), one declaration each. -/
theorem checkK_hex : checkK .hex = true := by
  rw [show checkK .hex = checkKg RefCell.hex hexR (4, 4, 4) 0 from rfl, checkKg_f]
  refine all_of_chunks _ _ 8 8 (by decide +kernel) fun i hi => ?_
  interval_cases i
  exacts [checkK_hex0, checkK_hex1, checkK_hex2, checkK_hex3, checkK_hex4, checkK_hex5, checkK_hex6, checkK_hex7]
theorem checkK_prism : checkK .prism = true := by
  rw [show checkK .prism = checkKg RefCell.prism prismR (2, 2, 3) 0 from rfl]
  decide +kernel
theorem checkK_pyr : checkK .pyr = true := by
  rw [show checkK .pyr = checkKg RefCell.pyramid pyrR (5, 5, 2) 0 from rfl]
  decide +kernel

theorem checkK_all (k : Kind) : checkK k = true := by
  cases k
  · exact checkK_hex
  · exact checkK_prism
  · exact checkK_pyr

/-! ### P3-11.8: closed computation of the facet sides of one cell over all its pulling splits -/

/-- `v` is one of `a0 a1 a2`. -/
def inF {n : ℕ} (a0 a1 a2 v : Fin n) : Bool := v == a0 || v == a1 || v == a2

/-- Signed contribution of the sub-tetrahedron `t` to the triangle `a0 a1 a2` (zero unless it is a face of `t`). -/
def termZ (k : Kind) (a0 a1 a2 : Fin k.n) (t : List (Fin k.n)) : ℤ :=
  if t.contains a0 && t.contains a1 && t.contains a2 then
    (t.map fun v => if inF a0 a1 a2 v then 0 else Int.sign (sideZ (refZ k a0) (refZ k a1) (refZ k a2) (refZ k v))).sum
  else 0

/-- Triangles of quadrilateral faces of a reference cell. -/
def quadTris {n : ℕ} (C : Cell3 n) : List (List (Fin n)) := C.quads.flatMap fun q => q.tris false ++ q.tris true

def quadAny (k : Kind) (a0 a1 a2 : Fin k.n) : Bool :=
  (quadTris k.cell).any fun f => f.contains a0 && f.contains a1 && f.contains a2
def triAny (k : Kind) (a0 a1 a2 : Fin k.n) : Bool :=
  k.cell.tris.any fun f => f.contains a0 && f.contains a1 && f.contains a2

/-- Twice the total weight of the face `a0 a1 a2` times the number of splits. -/
def shareZ (k : Kind) (a0 a1 a2 : Fin k.n) : ℤ :=
  if quadAny k a0 a1 a2 then k.cell.splits.length else if triAny k a0 a1 a2 then 2 * k.cell.splits.length else 0

def localOK (k : Kind) : Bool :=
  (List.finRange k.n).all fun a0 => (List.finRange k.n).all fun a1 => (List.finRange k.n).all fun a2 =>
    a0 == a1 || a0 == a2 || a1 == a2 ||
      (!(quadAny k a0 a1 a2 && triAny k a0 a1 a2) &&
        2 * (k.tets.map (termZ k a0 a1 a2)).sum == shareZ k a0 a1 a2 * Int.sign (cenZ k a0 a1 a2))

section Generic
variable {n : ℕ} (C : Cell3 n) (R : Fin n → Z3) (S : Z3)

def termZg (a0 a1 a2 : Fin n) (t : List (Fin n)) : ℤ :=
  if t.contains a0 && t.contains a1 && t.contains a2 then
    (t.map fun v => if inF a0 a1 a2 v then 0 else Int.sign (sideZ (R a0) (R a1) (R a2) (R v))).sum
  else 0
def quadAnyg (a0 a1 a2 : Fin n) : Bool :=
  (quadTris C).any fun f => f.contains a0 && f.contains a1 && f.contains a2
def triAnyg (a0 a1 a2 : Fin n) : Bool :=
  C.tris.any fun f => f.contains a0 && f.contains a1 && f.contains a2
def shareZg (a0 a1 a2 : Fin n) : ℤ :=
  if quadAnyg C a0 a1 a2 then C.splits.length else if triAnyg C a0 a1 a2 then 2 * C.splits.length else 0

/-- The check for the triangles with first vertex `a0`. -/
def localOKa (a0 : Fin n) : Bool :=
  (List.finRange n).all fun a1 => (List.finRange n).all fun a2 =>
    a0 == a1 || a0 == a2 || a1 == a2 ||
      (!(quadAnyg C a0 a1 a2 && triAnyg C a0 a1 a2) &&
        2 * ((tetsOf C).map (termZg R a0 a1 a2)).sum == shareZg C a0 a1 a2 * Int.sign (cenZg R S a0 a1 a2))

def localOKg : Bool := (List.finRange n).all (localOKa C R S)

end Generic

/-! The hexahedron check, split by the first vertex: eight smaller kernel computations (lower peak memory). -/

theorem localOK_hex0 : localOKa RefCell.hex hexR (4, 4, 4) 0 = true := by decide +kernel
theorem localOK_hex1 : localOKa RefCell.hex hexR (4, 4, 4) 1 = true := by decide +kernel
theorem localOK_hex2 : localOKa RefCell.hex hexR (4, 4, 4) 2 = true := by decide +kernel
theorem localOK_hex3 : localOKa RefCell.hex hexR (4, 4, 4) 3 = true := by decide +kernel
theorem localOK_hex4 : localOKa RefCell.hex hexR (4, 4, 4) 4 = true := by decide +kernel
theorem localOK_hex5 : localOKa RefCell.hex hexR (4, 4, 4) 5 = true := by decide +kernel
theorem localOK_hex6 : localOKa RefCell.hex hexR (4, 4, 4) 6 = true := by decide +kernel
theorem localOK_hex7 : localOKa RefCell.hex hexR (4, 4, 4) 7 = true := by decide +kernel

theorem localOK_hex : localOK .hex = true := by
  rw [show localOK .hex = localOKg RefCell.hex hexR (4, 4, 4) from rfl, localOKg, List.all_eq_true]
  intro a0 _
  fin_cases a0
  · exact localOK_hex0
  · exact localOK_hex1
  · exact localOK_hex2
  · exact localOK_hex3
  · exact localOK_hex4
  · exact localOK_hex5
  · exact localOK_hex6
  · exact localOK_hex7
theorem localOK_prism : localOK .prism = true := by
  rw [show localOK .prism = localOKg RefCell.prism prismR (2, 2, 3) from rfl]
  decide +kernel
theorem localOK_pyr : localOK .pyr = true := by
  rw [show localOK .pyr = localOKg RefCell.pyramid pyrR (5, 5, 2) from rfl]
  decide +kernel

theorem localOK_all (k : Kind) : localOK k = true := by
  cases k
  · exact localOK_hex
  · exact localOK_prism
  · exact localOK_pyr

end Asm11

end CFDLean.JST1.Proofs
