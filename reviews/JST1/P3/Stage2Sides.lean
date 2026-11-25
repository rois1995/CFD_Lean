import Paper1.Spec.Item11b
open Paper1.RefCell Paper1.Spec

/-! Reviewer's probe: on the reference geometries (unit cube, right prism, square pyramid; integer coordinates),
every interior triangle of every pulling split has its two sub-tetrahedra on opposite sides, and no sub-tetrahedron
is degenerate. This is the geometric premise of the step "face balance ⇒ SideBalanced" that stage 2 leaves in a
docstring. Exact integer arithmetic. -/

abbrev P3 := Int × Int × Int
def sub (a b : P3) : P3 := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)
def crs (u v : P3) : P3 := (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)
def dt (u v : P3) : Int := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

/-- Triple product of the triangle `f` (as listed) against the point `x`. -/
def side {n : ℕ} [NeZero n] (X : Fin n → P3) (f : List (Fin n)) (x : P3) : Int :=
  let a := X (f.getD 0 0); let b := X (f.getD 1 0); let c := X (f.getD 2 0)
  dt (crs (sub b a) (sub c a)) (sub x a)

def oppV {n : ℕ} [NeZero n] (t f : List (Fin n)) : Fin n := (t.filter fun v => !f.contains v).getD 0 0

/-- In split `T`: every tet nondegenerate, and every non-cell-face triangle has its tets on opposite sides. -/
def splitOK {n : ℕ} [NeZero n] (C : Cell3 n) (X : Fin n → P3) (T : List (List (Fin n))) : Bool :=
  T.all (fun t => side X ((tetFaces t).getD 0 []) (X (oppV t ((tetFaces t).getD 0 []))) != 0) &&
  T.all fun t => (tetFaces t).all fun f => onCellFace C f ||
    T.all fun t' => !(tetFaces t').any (sameSimplex f) || sameSimplex t t' ||
      decide (side X f (X (oppV t f)) * side X f (X (oppV t' f)) < 0)

def hexX : Fin 8 → P3 := ![(0,0,0),(1,0,0),(1,1,0),(0,1,0),(0,0,1),(1,0,1),(1,1,1),(0,1,1)]
def prismX : Fin 6 → P3 := ![(0,0,0),(1,0,0),(0,1,0),(0,0,1),(1,0,1),(0,1,1)]
def pyrX : Fin 5 → P3 := ![(0,0,0),(2,0,0),(2,2,0),(0,2,0),(1,1,2)]

#eval hex.splits.all fun s => splitOK hex hexX (hex.pull s.1 s.2)
#eval prism.splits.all fun s => splitOK prism prismX (prism.pull s.1 s.2)
#eval pyramid.splits.all fun s => splitOK pyramid pyrX (pyramid.pull s.1 s.2)
-- total volume of each split equals the cell volume (6 × volume, integer): fills without gaps if no overlap
def vol6 {n : ℕ} [NeZero n] (X : Fin n → P3) (t : List (Fin n)) : Int :=
  let f := [t.getD 1 0, t.getD 2 0, t.getD 3 0]; (side X f (X (t.getD 0 0))).natAbs
#eval (hex.splits.map fun s => ((hex.pull s.1 s.2).map (vol6 hexX)).sum).eraseDups
#eval (prism.splits.map fun s => ((prism.pull s.1 s.2).map (vol6 prismX)).sum).eraseDups
#eval (pyramid.splits.map fun s => ((pyramid.pull s.1 s.2).map (vol6 pyrX)).sum).eraseDups
