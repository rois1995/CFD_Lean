import CFDLean.Exec.EulerTraces
import ReviewCases.E1.ExactStep

namespace ReviewCases.EulerTraces

open CFDLean.Exec CFDLean.Exec.EulerTraces
open CFDLean.Exec.FV1D (EulerState triple pressure)
open scoped ReviewCases.E1

private def sample (u : EulerState ℚ) := #[u 0, u 1, u 2]
private def a := triple (1 : ℚ) (-3) 5
private def b := triple (1 : ℚ) (-2) 3
private def c := triple (1 : ℚ) (-1) 3

#guard [a, b, c].all fun q => decide (admissible 2 q)
#guard sample (slope Scalar.minmod a b c) == #[0, 1, 0]
#guard pressure 1 2 2 (raw b (slope Scalar.minmod a b c)).1 == -1/8
#guard pressure 1 2 2 (raw b (slope Scalar.minmod a b c)).2 == 15/8
#guard sample (select 2 b (slope Scalar.minmod a b c)).1 == sample b
#guard sample (select 2 b (slope Scalar.minmod a b c)).2 == sample b

-- A constant-pressure contact with increasing densities retains both reconstructed traces.
private def contact (r : ℚ) := triple r (2*r) (1+2*r)
private def wave := #[contact 2, contact 3, contact 1]
#guard sample (faceStates Scalar.minmod 2 wave ⟨0, by decide⟩).1 == sample (contact (5/2))
#guard sample (faceStates Scalar.minmod 2 wave ⟨2, by decide⟩).2 == sample (contact (3/2))
#guard sample (faceStates Scalar.minmod 2 #[b] 0).1 == sample b
#guard sample (faceStates Scalar.minmod 2 #[b] 0).2 == sample b

end ReviewCases.EulerTraces
