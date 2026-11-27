import CFDLean.Discrete.Periodic.Grid

/-! FVN geometry: a fixed periodic 1D mesh is a periodic grid plus one positive width per cell. The face indexed by
`i` points from cell `i` to `next i`. In 1D the centroid of a cell is its midpoint, so the width is the only geometric
input. The state `U : I → S` stays separate from the mesh. -/
noncomputable section
namespace CFDLean.Periodic

/-- A fixed periodic 1D mesh over the cell index type `I`: the periodic grid and one width per cell. -/
structure Mesh1D (I : Type*) where
  /-- The periodic connectivity: face `i` points from cell `i` to `grid.next i`. -/
  grid : Grid I
  /-- The width of each cell. -/
  width : I → ℝ
  /-- Geometric validity: every cell has positive width. -/
  width_pos : ∀ i, 0 < width i

namespace Mesh1D

variable {I : Type*}

/-- Distance between the centroids of cell `i` and cell `next i`. -/
def spacing (m : Mesh1D I) (i : I) : ℝ :=
  (m.width i + m.width (m.grid.next i)) / 2

/-- The uniform mesh: every cell has width `dx`. -/
def uniform (g : Grid I) (dx : ℝ) (hdx : 0 < dx) : Mesh1D I where
  grid := g
  width := fun _ => dx
  width_pos := fun _ => hdx

/-- Mesh ratio `θ`: at every face `i`, `θ · max (w i) (w (next i)) ≤ w i + w (next i)`. -/
def MeshRatio (m : Mesh1D I) (θ : ℝ) : Prop :=
  ∀ i, θ * max (m.width i) (m.width (m.grid.next i)) ≤ m.width i + m.width (m.grid.next i)

end Mesh1D

end CFDLean.Periodic
