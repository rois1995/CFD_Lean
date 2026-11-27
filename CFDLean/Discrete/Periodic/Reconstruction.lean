import CFDLean.Discrete.Periodic.Nonuniform

/-! Reconstruction on a fixed periodic mesh, consumed by the existing conservative flux update. -/
namespace CFDLean.FV1D

open Periodic
open scoped BigOperators

/-- At face `i`, return the interior trace from cell `i` followed by the trace from `m.grid.next i`.
Indexing by the mesh lets a method restrict its geometry, for example to a uniform mesh. -/
structure Reconstruction {I : Type*} (m : Mesh1D I) (S : Type*) where
  traces : (I → S) → I → S × S

namespace Reconstruction

variable {I S : Type*} {m : Mesh1D I}

/-- A property of a reconstruction that can be checked independently of the flux. -/
def PreservesConstants (R : Reconstruction m S) : Prop :=
  ∀ (c : S) (i : I), R.traces (fun _ => c) i = (c, c)

variable [AddCommGroup S] [Module ℝ S]

/-- Feed one oriented numerical flux per face into the existing FVN update. -/
noncomputable def step (R : Reconstruction m S) (H : S → S → S) (dt : ℝ) (U : I → S) : I → S :=
  Nonuniform.update m dt (fun i => let (l, r) := R.traces U i; H l r) U

theorem step_weighted_sum [Fintype I] (R : Reconstruction m S) (H : S → S → S) (dt : ℝ) (U : I → S) :
    ∑ i, m.width i • R.step H dt U i = ∑ i, m.width i • U i :=
  Nonuniform.update_weighted_sum m dt _ U

theorem step_constant (R : Reconstruction m S) (hR : R.PreservesConstants) (H : S → S → S)
    (dt : ℝ) (c : S) : R.step H dt (fun _ => c) = fun _ => c := by
  funext i
  simp [step, Nonuniform.update, hR c]

end Reconstruction
end CFDLean.FV1D
