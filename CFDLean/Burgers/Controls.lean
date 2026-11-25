import CFDLean.Burgers.Schemes.RusanovForwardEuler

noncomputable section
namespace CFDLean.Burgers.Controls

open CFDLean.Burgers
open CFDLean.Burgers.Schemes.RusanovForwardEuler

example : physicalFlux 2 = 2 := by
  norm_num [physicalFlux]

example : Rusanov.eval 3 3 = physicalFlux 3 := by
  simpa [Rusanov.numericalFlux] using Rusanov.consistent 3

example (dx dt c : ℝ) :
    @step_preserves_constant 4 (by infer_instance) dx dt c =
      @step_preserves_constant 4 (by infer_instance) dx dt c := rfl

end CFDLean.Burgers.Controls
