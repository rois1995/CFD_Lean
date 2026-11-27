import CFDLean.Exec.E1.ExactStep

namespace ReviewCases.E1
export CFDLean.Exec.E1 (cast_step)

scoped instance ratScalar : CFDLean.Exec.Scalar ℚ := CFDLean.Exec.E1.ratScalar

-- Different periodic neighbours at index zero distinguish the two face orientations.
#guard CFDLean.Exec.eulerStepArray (3 : ℚ) 1 #[1, 2, 0] == #[5/6, 13/12, 13/12]
#guard CFDLean.Exec.eulerStepArray (1 : ℚ) 1 #[7/3] == #[7/3]

end ReviewCases.E1
