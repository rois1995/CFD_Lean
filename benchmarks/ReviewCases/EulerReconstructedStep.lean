import CFDLean.Exec.EulerReconstruction
import ReviewCases.E1.ExactStep

namespace ReviewCases.EulerReconstructedStep
open CFDLean.Exec FV1D
open scoped ReviewCases.E1

private def u : Array (EulerState ℚ) := #[triple 1 (-3) 5, triple 1 (-2) 3, triple 1 (-1) 3]
private def w : Array ℚ := #[1,1,1]
private def valid (q : EulerState ℚ) : Bool := decide (0 < q 0 ∧ 0 < pressure 1 2 2 q)
private def pairedFallback (method : EulerReconstruction) (i : Fin u.size) : Bool :=
  let raw := eulerCell method (1/1000000) (fun _ => true) w u i
  let selected := eulerCell method (1/1000000) valid w u i
  !valid raw.1 && valid raw.2 && decide (∀ k, selected.1 k = u[i] k ∧ selected.2 k = u[i] k)

#guard u.all valid
#guard pairedFallback .minmod ⟨1, by decide⟩
#guard pairedFallback .weno ⟨0, by decide⟩

end ReviewCases.EulerReconstructedStep
