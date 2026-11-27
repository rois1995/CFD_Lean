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

end CFDLean.Exec
