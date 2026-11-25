import Mathlib
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Reference cells of mixed meshes and their pulling splits, as finite combinatorial data (paper Section
`sec:mixed`, `lem:avg`, `prop:splits`). A tetrahedron (or triangle) is a list of local vertices. -/
namespace CFDLean.JST1
namespace RefCell

/-- A quadrilateral face, given cyclically `a b c d`. Its diagonals are `ac` (`false`) and `bd` (`true`). -/
structure Quad (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  d : Fin n
  deriving DecidableEq

variable {n : ℕ}

def Quad.mem (q : Quad n) (v : Fin n) : Bool := v == q.a || v == q.b || v == q.c || v == q.d
def Quad.diag (q : Quad n) (δ : Bool) : Fin n × Fin n := if δ then (q.b, q.d) else (q.a, q.c)
def Quad.tris (q : Quad n) (δ : Bool) : List (List (Fin n)) :=
  if δ then [[q.a, q.b, q.d], [q.b, q.c, q.d]] else [[q.a, q.b, q.c], [q.a, q.c, q.d]]

/-- A 3D reference cell: its quadrilateral and triangular faces. -/
structure Cell3 (n : ℕ) where
  quads : List (Quad n)
  tris : List (List (Fin n))

/-- All Boolean lists of length `k`. -/
def allBools : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBools k).flatMap fun l => [false :: l, true :: l]

/-- Pulling split with apex `v` and a diagonal choice `ch` (one Boolean per quadrilateral face): every face without
`v` is triangulated (quadrilaterals by the chosen diagonal) and joined to `v`. -/
def Cell3.pull (C : Cell3 n) (v : Fin n) (ch : List Bool) : List (List (Fin n)) :=
  ((List.range C.quads.length).zip C.quads).flatMap (fun jq =>
      if jq.2.mem v then [] else (jq.2.tris (ch.getD jq.1 false)).map fun t => v :: t) ++
    (C.tris.filter fun t => !(t.contains v)).map fun t => v :: t

/-- The pulling splits, each once: the choice is `false` on faces that contain the apex (unused there). -/
def Cell3.splits (C : Cell3 n) : List (Fin n × List Bool) :=
  (List.finRange n).flatMap fun v =>
    ((allBools C.quads.length).filter fun ch =>
      ((List.range C.quads.length).zip C.quads).all fun jq => !(jq.2.mem v) || !(ch.getD jq.1 false)).map
      fun ch => (v, ch)

/-- A split uses the edge `xy` if one of its sub-simplices contains both vertices. -/
def usesEdge (T : List (List (Fin n))) (e : Fin n × Fin n) : Bool := T.any fun t => t.contains e.1 && t.contains e.2

/-- Number of pulling splits that use the diagonal `δ` of the quadrilateral face `q`. -/
def Cell3.diagCount (C : Cell3 n) (q : Quad n) (δ : Bool) : ℕ :=
  C.splits.countP fun s => usesEdge (C.pull s.1 s.2) (q.diag δ)

/-- Hexahedron `0..7` (`0..3` bottom, `4..7` top, `i+4` above `i`). -/
def hex : Cell3 8 where
  quads := [⟨0, 1, 2, 3⟩, ⟨4, 5, 6, 7⟩, ⟨0, 1, 5, 4⟩, ⟨1, 2, 6, 5⟩, ⟨2, 3, 7, 6⟩, ⟨3, 0, 4, 7⟩]
  tris := []

/-- Prism `0 1 2` bottom, `3 4 5` top. -/
def prism : Cell3 6 where
  quads := [⟨0, 1, 4, 3⟩, ⟨1, 2, 5, 4⟩, ⟨2, 0, 3, 5⟩]
  tris := [[0, 1, 2], [3, 4, 5]]

/-- Pyramid with base `0 1 2 3` and apex `4`. -/
def pyramid : Cell3 5 where
  quads := [⟨0, 1, 2, 3⟩]
  tris := [[0, 1, 4], [1, 2, 4], [2, 3, 4], [3, 0, 4]]

/-- 2D: the quadrilateral `0 1 2 3`; pulling split with apex `v`: the edges without `v` joined to `v`. -/
def quadPull (v : Fin 4) : List (List (Fin 4)) :=
  ([[(0 : Fin 4), 1], [1, 2], [2, 3], [3, 0]].filter fun e => !(e.contains v)).map fun e => v :: e

/-- Edge neighbours from an edge list. -/
def nbrOf (es : List (Fin n × Fin n)) (v w : Fin n) : Bool :=
  es.any fun e => (e.1 == v && e.2 == w) || (e.1 == w && e.2 == v)

def hexEdges : List (Fin 8 × Fin 8) :=
  [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4), (0, 4), (1, 5), (2, 6), (3, 7)]
def prismEdges : List (Fin 6 × Fin 6) := [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (0, 3), (1, 4), (2, 5)]
def pyramidEdges : List (Fin 5 × Fin 5) := [(0, 1), (1, 2), (2, 3), (3, 0), (0, 4), (1, 4), (2, 4), (3, 4)]

/-- Neighbour-fan rule: a face without the apex that contains exactly one edge neighbour `w` of the apex is
fanned through `w` (the chosen diagonal contains `w`). -/
def Cell3.nbrFan (C : Cell3 n) (nbr : Fin n → Fin n → Bool) (s : Fin n × List Bool) : Bool :=
  ((List.range C.quads.length).zip C.quads).all fun jq =>
    let q := jq.2
    let ws := [q.a, q.b, q.c, q.d].filter fun w => nbr s.1 w
    if q.mem s.1 then true
    else match ws with
      | [w] => (let e := q.diag (s.2.getD jq.1 false); e.1 == w || e.2 == w)
      | _ => true

/-- The neighbour-fan subset of the pulling splits. -/
def Cell3.fanSplits (C : Cell3 n) (nbr : Fin n → Fin n → Bool) : List (Fin n × List Bool) :=
  C.splits.filter (C.nbrFan nbr)

/-- Opposite vertex of the hexahedron (body diagonal). -/
def hexOpp (v : Fin 8) : Fin 8 := ![6, 7, 4, 5, 2, 3, 0, 1] v

/-- Generators of the 48 symmetries of the cube, as vertex permutations (rotations about z and x, mirror x). -/
def hexRz : Fin 8 → Fin 8 := ![1, 2, 3, 0, 5, 6, 7, 4]
def hexRx : Fin 8 → Fin 8 := ![3, 2, 6, 7, 0, 1, 5, 4]
def hexMx : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

/-- Sliver tetrahedra of a hexahedron thin in the vertical direction: an apex on one horizontal face and the three
corners of the other horizontal face that are not above (or below) it. -/
def hexSliver (v : Fin 8) : List (Fin 8) :=
  let top : List (Fin 8) := [4, 5, 6, 7]
  let bot : List (Fin 8) := [0, 1, 2, 3]
  let v' : Fin 8 := ⟨(v.val + 4) % 8, Nat.mod_lt _ (by norm_num)⟩
  v :: ((if v.val < 4 then top else bot).filter fun w => w != v')

/-- Same sub-simplex up to the order of its vertices. -/
def sameSimplex (s t : List (Fin n)) : Bool := s.length == t.length && s.all fun x => t.contains x

def containsSimplex (T : List (List (Fin n))) (t : List (Fin n)) : Bool := T.any fun s => sameSimplex s t

/-- Same split up to the order of its sub-simplices. -/
def sameSplit (T U : List (List (Fin n))) : Bool :=
  T.length == U.length && T.all (containsSimplex U) && U.all (containsSimplex T)

/-- Image of a split under a vertex map. -/
def mapSplit (σ : Fin n → Fin n) (T : List (List (Fin n))) : List (List (Fin n)) := T.map (List.map σ)

end RefCell
end CFDLean.JST1
