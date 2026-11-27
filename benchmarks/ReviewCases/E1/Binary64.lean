import CFDLean.Exec.E1.Binary64

namespace ReviewCases.E1
export CFDLean.Exec.E1 (value value_isSome)

-- Native controls supplement the classifier theorem with independently chosen IEEE encodings.
#guard value (Float.ofBits 0) == some 0
#guard value (Float.ofBits 0x8000000000000000) == some 0
#guard value (Float.ofBits 1) == some ((2 : Rat) ^ (-1074 : Int))
#guard value (Float.ofBits 0x0010000000000000) == some ((2 : Rat) ^ (-1022 : Int))
#guard value (Float.ofBits 0xbff8000000000000) == some (-3/2)
#guard value (Float.ofBits 0x7fefffffffffffff) == some (((2 : Rat)^53 - 1) * 2^971)
#guard (value (Float.ofBits 0xfff0000000000000)).isNone
#guard (value (Float.ofBits 0x7ff8000000000000)).isNone

end ReviewCases.E1
