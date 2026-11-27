import CFDLean.Exec.ReconstructedKernel
import CFDLean.Exec.NonuniformRefinement
import CFDLean.Discrete.Periodic.GradedWeno

noncomputable section
namespace CFDLean.Exec

open Periodic
/-- Connectivity of the native array, including arrays shorter than the reconstruction stencil. -/
def arrayGrid (n : Nat) : Grid (Fin n) :=
  ⟨⟨nextIdx, prevIdx, prevIdx_nextIdx, nextIdx_prevIdx⟩⟩

/-- On real inputs the native Burgers WENO forward stage is the mesh-indexed reconstruction step. -/
theorem burgersWenoStep_refines (ε : {x : ℝ // 0 < x}) (dt : ℝ) (w u : Array ℝ)
    (hw : w.size = u.size) (hp : ∀ i : Fin w.size, 0 < w[i]) (i : Fin u.size) :
    let m : Mesh1D (Fin u.size) := ⟨arrayGrid u.size, fun j => widthAt w j.val,
      fun j => by rw [widthAt_of_lt _ (hw.symm ▸ j.isLt)]; exact hp ⟨j.val, hw.symm ▸ j.isLt⟩⟩
    (burgersWenoStep ε.val dt w u)[i.val]?.getD 0 =
      (CFDLean.FV1D.Reconstruction.gradedWeno m ε).step
        (FV1D.face FV1D.burgers Scalar.half) dt (fun j => u[j]) i := by
  simp [burgersWenoStep, reconstructedStep, wenoCell, CFDLean.FV1D.Reconstruction.step,
    CFDLean.FV1D.Reconstruction.gradedWeno, CFDLean.FV1D.Nonuniform.update, arrayGrid,
    Grid.prev, FV1D.burgers, smul_eq_mul, i.isLt]

/-- Representation for arbitrary intermediate arrays on the fixed width mesh. -/
private theorem wenoStage_represents {n : Nat} (widths : Array ℝ) (hw : widths.size = n)
    (hp : ∀ i : Fin widths.size, 0 < widths[i]) (ε : {x : ℝ // 0 < x}) (dt : ℝ)
    {u : Array ℝ} {v : Fin n → ℝ} (h : Represents u v) :
    let mesh : Mesh1D (Fin n) := ⟨arrayGrid n, fun j => widthAt widths j.val,
      fun j => by rw [widthAt_of_lt _ (hw.symm ▸ j.isLt)]; exact hp ⟨j.val, hw.symm ▸ j.isLt⟩⟩
    Represents (burgersWenoStep ε.val dt widths u) ((CFDLean.FV1D.Reconstruction.gradedWeno mesh ε).step
      (FV1D.face FV1D.burgers Scalar.half) dt v) := by
  obtain ⟨hs, hu⟩ := h
  subst hs
  have hf : v = fun i => u[i] := funext fun i => (hu i).symm
  subst v
  have size : (burgersWenoStep ε.val dt widths u).size = u.size := Array.size_ofFn
  refine ⟨size, fun i => ?_⟩
  have hi : i.val < (burgersWenoStep ε.val dt widths u).size := by rw [size]; exact i.isLt
  simpa only [getElem?_pos (burgersWenoStep ε.val dt widths u) i.val hi, Option.getD_some] using
    burgersWenoStep_refines ε dt widths u hw hp i

/-- Every stage reconstructs from the preceding field before the SSP convex combinations. -/
theorem burgersWenoSsprk3_refines {n : Nat} (widths : Array ℝ) (hw : widths.size = n)
    (hp : ∀ i : Fin widths.size, 0 < widths[i]) (ε : {x : ℝ // 0 < x}) (dt : ℝ)
    {u : Array ℝ} {v : Fin n → ℝ} (h : Represents u v) :
    let mesh : Mesh1D (Fin n) := ⟨arrayGrid n, fun j => widthAt widths j.val,
      fun j => by rw [widthAt_of_lt _ (hw.symm ▸ j.isLt)]; exact hp ⟨j.val, hw.symm ▸ j.isLt⟩⟩
    Represents (burgersWenoSsprk3 ε.val dt widths u) (Time.SSP.ssprk3
      ((CFDLean.FV1D.Reconstruction.gradedWeno mesh ε).step (FV1D.face FV1D.burgers Scalar.half) dt) v) :=
  axpby_refines _ _ h (wenoStage_represents widths hw hp ε dt (axpby_refines _ _ h
    (wenoStage_represents widths hw hp ε dt (wenoStage_represents widths hw hp ε dt h))))

end CFDLean.Exec
