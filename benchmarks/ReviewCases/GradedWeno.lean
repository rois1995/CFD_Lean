import CFDLean.Discrete.Periodic.GradedWeno
import Mathlib.Data.Rat.Defs

namespace ReviewCases.GradedWeno
open CFDLean.GradedWeno

-- Independent moment solves on cells with periodic widths (1,2,3,4,5,6) and means (1,2,4,3,1,0).
example : edge (1 : ℚ) ⟨4,5,6,1,2⟩ ⟨3,1,0,1,2⟩ =
    18404544825410991576178677 / 30404425815732402608015224 := by decide +kernel
example : edge (1 : ℚ) ⟨3,2,1,6,5⟩ ⟨4,2,1,0,1⟩ =
    289716345724523430316611 / 401443434426759937064444 := by decide +kernel

end ReviewCases.GradedWeno
