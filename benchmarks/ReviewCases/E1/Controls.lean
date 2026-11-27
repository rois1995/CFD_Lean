import ReviewCases.E1.Budget

namespace ReviewCases.E1

open CFDLean.Exec

-- Singleton seam, constant state, zero timestep, then a nonconstant exactly representable update.
#guard checkStep 1 0.125 #[3] 0
#guard checkStep 1 0.125 #[2, 2, 2] 0
#guard checkStep 1 0 #[1, -2, 3] 0
#guard checkStep 1 0.125 #[1, -2, 4] 0

-- Exact result: (5/6, 13/12, 13/12). The middle cell has the largest observed error.
private def rounded : Array Float := #[1, 2, 0]
private def largest : Rat := 1 / 6755399441055744
#guard (eulerStepArray (3 : Rat) 1 #[1, 2, 0]) == #[5/6, 13/12, 13/12]
#guard checkStep 3 1 rounded largest
#guard !(checkStep 3 1 rounded (largest/2))
#guard !(checkStep 3 1 rounded 0)

-- The native tiny flux rounds away. Exact fluxes can involve products of two subnormals.
private def tiny : Float := Float.ofBits 1
#guard !(checkStep 1 1 #[tiny, 0, 0] 0)
#guard checkStep 1 1 #[tiny, 0, 0] ((2 : Rat)^(-2148 : Int))

#guard !(checkStep 1 0 #[] 0)
#guard !(checkStep 0 0 #[1] 0)
#guard !(checkStep (-1) 0 #[1] 0)
#guard !(checkStep 1 (-1) #[1] 0)
#guard !(checkStep 1 0 #[1] (-1))
#guard !(checkStep 1 0 #[Float.ofBits 0x7ff8000000000000] 1)
#guard !(checkStep (Float.ofBits 0x7ff0000000000000) 0 #[1] 1)
-- Finite inputs can overflow inside the kernel, even at dt = 0.
#guard !(checkStep 1 0 #[Float.ofBits 0x7fefffffffffffff, 0] 1)

end ReviewCases.E1
