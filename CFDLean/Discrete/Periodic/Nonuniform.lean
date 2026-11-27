import CFDLean.Discrete.Periodic.Mesh1D
import CFDLean.Discrete.Periodic.Rusanov

/-! FVN: the flux-form update on a non-uniform periodic 1D mesh, FVN-C, and the first-order step (FVN-K, FVN-U(a)).

`update` is reconstruction-independent. It takes a face-flux function `h : I → S`, where `h i` is the flux through
the face from cell `i` to `next i`, and each cell divides the flux difference by its own width. Conservation (FVN-C)
is a property of `update` alone. First order and MUSCL are two producers of face fluxes: the first-order step feeds
`update` with `H (U i) (U (next i))`. -/
noncomputable section
namespace CFDLean.FV1D.Nonuniform

open Periodic
open scoped BigOperators

variable {S I : Type*} [AddCommGroup S] [Module ℝ S]

/-- Flux-form update for a given face-flux function `h`. Both faces of cell `i` use the same `h`. -/
def update (m : Mesh1D I) (dt : ℝ) (h U : I → S) (i : I) : S :=
  U i - (dt / m.width i) • (h i - h (m.grid.prev i))

/-- First-order step: the face flux is the two-point flux `H` of the old states on either side of the face. -/
def firstOrderStep (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (U : I → S) (i : I) : S :=
  update m dt (fun j => H (U j) (U (m.grid.next j))) U i

/-- FVN-C: the width-weighted sum is conserved for every face-flux function. -/
theorem update_weighted_sum [Fintype I] (m : Mesh1D I) (dt : ℝ) (h U : I → S) :
    ∑ i, m.width i • update m dt h U i = ∑ i, m.width i • U i := by
  have cell : ∀ i, m.width i • update m dt h U i =
      m.width i • U i - dt • (h i - h (m.grid.prev i)) := by
    intro i
    rw [update, smul_sub, smul_smul, mul_div_cancel₀ dt (m.width_pos i).ne']
  have reindex : ∑ i, h (m.grid.prev i) = ∑ i, h i :=
    Fintype.sum_equiv m.grid.next.symm _ _ (fun _ => rfl)
  simp only [cell]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_sub_distrib, reindex]
  simp

/-- FVN-C (first order): the first-order step conserves the width-weighted sum, for every two-point flux `H`. -/
theorem firstOrderStep_weighted_sum [Fintype I] (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (U : I → S) :
    ∑ i, m.width i • firstOrderStep m H dt U i = ∑ i, m.width i • U i :=
  update_weighted_sum m dt _ U

/-- FVN-K (first order): a constant state is a fixed point for every two-point flux `H`. -/
theorem firstOrderStep_constant (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (C : S) :
    firstOrderStep m H dt (fun _ => C) = fun _ => C := by
  funext i
  simp [firstOrderStep, update]

/-- FVN-U(a): on the uniform mesh with the FV1D Rusanov face, the first-order step is `FV1D.step`. -/
theorem firstOrderStep_uniform (g : Grid I) (F : S → S) (a : S → S → ℝ) (dx : ℝ) (hdx : 0 < dx) (dt : ℝ)
    (U : I → S) (i : I) :
    firstOrderStep (Mesh1D.uniform g dx hdx) (FV1D.face F a) dt U i = FV1D.step g F a dx dt U i :=
  rfl

end CFDLean.FV1D.Nonuniform
