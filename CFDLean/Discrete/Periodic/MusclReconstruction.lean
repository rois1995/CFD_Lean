import CFDLean.Discrete.Periodic.Reconstruction
import CFDLean.Discrete.Periodic.NonuniformMuscl

namespace CFDLean.FV1D.Reconstruction

open Periodic

variable {I S : Type*} [AddCommGroup S] [Module ℝ S]

/-- The accepted FVN MUSCL traces, including the geometry-dependent scaling of both slopes. -/
noncomputable def muscl (m : Mesh1D I) (lim : S → S → S) : Reconstruction m S where
  traces U i := (Nonuniform.leftState m lim U i, Nonuniform.rightState m lim U i)

theorem muscl_step (m : Mesh1D I) (lim H : S → S → S) (dt : ℝ) (U : I → S) :
    (muscl m lim).step H dt U = Nonuniform.musclStep m H lim dt U := rfl

theorem muscl_constants (m : Mesh1D I) (lim : S → S → S) (h : lim 0 0 = 0) :
    (muscl m lim).PreservesConstants := by
  intro c i
  simp [muscl, Nonuniform.leftState, Nonuniform.rightState, Nonuniform.slope,
    Nonuniform.backDiff, Nonuniform.fwdDiff, h]

end CFDLean.FV1D.Reconstruction
