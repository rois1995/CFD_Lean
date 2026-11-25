import CFDLean.Papers.JST1.Spec.Item11a
import CFDLean.Geometry.Simplex

/-! Statements of item 12 (P3): `prop:splits` (lines 691-699, proof 968-982). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology
namespace CFDLean.JST1.Spec
open CFDLean.JST1.RefCell

/-- P3-12.1: half of the 64 pulling splits of a hexahedron contain a sliver (thin vertical direction), and each of
the 8 slivers is in exactly 4 splits, so it has weight 1/16 in the mean. -/
def P3_12_1 : Prop :=
  (hex.splits.countP fun s => (List.finRange 8).any fun v => containsSimplex (hex.pull s.1 s.2) (hexSliver v)) = 32 ∧
  ((List.finRange 8).all fun v =>
    hex.splits.countP (fun s => containsSimplex (hex.pull s.1 s.2) (hexSliver v)) == 4) = true

/-- The sliver of the brick `[0,a]×[0,b]×[0,h]`: the corner `(0,0,0)` and the three top corners not above it. -/
def sliverBrick (a b h : ℝ) : Simplex 3 := ⟨![![0, 0, 0], ![a, 0, h], ![a, b, h], ![0, b, h]]⟩

/-- Cosine of the dihedral angle between the faces opposite `p` and `q`: `-g_p·g_q/(|g_p||g_q|)`. -/
def cosDih {d : ℕ} (T : Simplex d) (p q : Fin (d + 1)) : ℝ :=
  -Num.dot (T.grad p) (T.grad q) / (len (T.grad p) * len (T.grad q))

/-- P3-12.2: as the thickness tends to zero, two dihedral angles of the sliver tend to 180° (cosine → -1). -/
def P3_12_2 : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    Tendsto (fun h => cosDih (sliverBrick a b h) 1 3) (𝓝[>] 0) (𝓝 (-1)) ∧
    Tendsto (fun h => cosDih (sliverBrick a b h) 0 2) (𝓝[>] 0) (𝓝 (-1))

/-- P3-12.3: a weighted sum of non-negative element forms with weight at least 1/16 on one element is at least 1/16
of that element's form (stated for the values at one argument). -/
def P3_12_3 : Prop :=
  ∀ (σ : Type) [Fintype σ] (ω q : σ → ℝ) (t : σ), (∀ s, 0 ≤ ω s) → (∀ s, 0 ≤ q s) → 1 / 16 ≤ ω t →
    q t / 16 ≤ ∑ s, ω s * q s

/-- P3-12.4: the neighbour-fan subset of the hexahedron has 8 splits; each has every tetrahedron on the body diagonal
of its apex, the apex and the opposite vertex give the same triangulation (4 Kuhn triangulations), it is face
balanced (4:4), and it is mapped to itself by the generators of the cube symmetries. On prisms and pyramids it
contains all pulling splits. -/
def P3_12_4 : Prop :=
  (hex.fanSplits (nbrOf hexEdges)).length = 8 ∧
  ((hex.fanSplits (nbrOf hexEdges)).all fun s =>
    (hex.pull s.1 s.2).all fun t => t.contains s.1 && t.contains (hexOpp s.1)) = true ∧
  ((hex.fanSplits (nbrOf hexEdges)).all fun s => (hex.fanSplits (nbrOf hexEdges)).any fun s' =>
    s'.1 == hexOpp s.1 && sameSplit (hex.pull s.1 s.2) (hex.pull s'.1 s'.2)) = true ∧
  (hex.quads.all fun q =>
    ((hex.fanSplits (nbrOf hexEdges)).countP fun s => usesEdge (hex.pull s.1 s.2) (q.diag false)) == 4 &&
    ((hex.fanSplits (nbrOf hexEdges)).countP fun s => usesEdge (hex.pull s.1 s.2) (q.diag true)) == 4) = true ∧
  ([hexRz, hexRx, hexMx].all fun σ => (hex.fanSplits (nbrOf hexEdges)).all fun s =>
    (hex.fanSplits (nbrOf hexEdges)).any fun s' =>
      sameSplit (mapSplit σ (hex.pull s.1 s.2)) (hex.pull s'.1 s'.2)) = true ∧
  (prism.fanSplits (nbrOf prismEdges)).length = prism.splits.length ∧
  (pyramid.fanSplits (nbrOf pyramidEdges)).length = pyramid.splits.length

/-- P3-12.5: every Kuhn tetrahedron of a brick is nondegenerate and has `g_a · g_b ≤ 0` for `a ≠ b`, so all its
dihedral angles are at most 90°. -/
def P3_12_5 : Prop :=
  ∀ (π : Equiv.Perm (Fin 3)) (h : Fin 3 → ℝ), (∀ i, 0 < h i) →
    (pathSimplex π h).Nondeg ∧
    ∀ a b : Fin 4, a ≠ b → Num.dot ((pathSimplex π h).grad a) ((pathSimplex π h).grad b) ≤ 0

end CFDLean.JST1.Spec
