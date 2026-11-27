import CFDLean.Discrete.Periodic.Nonuniform

/-! Checks for the reconstruction-independent layer of FVN (task 1): each public theorem applied to its own
hypotheses, the one-cell grid `ZMod 1` (where `next i = prev i = i`) and the step with `dt = 0`. -/
noncomputable section
namespace CFDLean.FV1D.Nonuniform.Checks

open Periodic
open scoped BigOperators

variable {S I : Type*} [AddCommGroup S] [Module ℝ S]

example [Fintype I] (m : Mesh1D I) (dt : ℝ) (h U : I → S) :
    ∑ i, m.width i • update m dt h U i = ∑ i, m.width i • U i :=
  update_weighted_sum m dt h U

example [Fintype I] (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (U : I → S) :
    ∑ i, m.width i • firstOrderStep m H dt U i = ∑ i, m.width i • U i :=
  firstOrderStep_weighted_sum m H dt U

example (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (C : S) :
    firstOrderStep m H dt (fun _ => C) = fun _ => C :=
  firstOrderStep_constant m H dt C

example (g : Grid I) (F : S → S) (a : S → S → ℝ) (dx : ℝ) (hdx : 0 < dx) (dt : ℝ) (U : I → S) (i : I) :
    firstOrderStep (Mesh1D.uniform g dx hdx) (FV1D.face F a) dt U i = FV1D.step g F a dx dt U i :=
  firstOrderStep_uniform g F a dx hdx dt U i

/-- Review focus 1: the one-cell grid needs no extra hypothesis for FVN-C. -/
example (m : Mesh1D (ZMod 1)) (H : S → S → S) (dt : ℝ) (U : ZMod 1 → S) :
    ∑ i, m.width i • firstOrderStep m H dt U i = ∑ i, m.width i • U i :=
  firstOrderStep_weighted_sum m H dt U

/-- Review focus 1: the one-cell grid needs no extra hypothesis for FVN-K. -/
example (m : Mesh1D (ZMod 1)) (H : S → S → S) (dt : ℝ) (C : S) :
    firstOrderStep m H dt (fun _ => C) = fun _ => C :=
  firstOrderStep_constant m H dt C

/-- Review focus 2: with `dt = 0` the first-order step returns its input. -/
example (m : Mesh1D I) (H : S → S → S) (U : I → S) : firstOrderStep m H 0 U = U := by
  funext i
  simp [firstOrderStep, update]

end CFDLean.FV1D.Nonuniform.Checks
