import Init.Data.Float
import Init.Data.Rat

/-! Exact finite-value interpretation of the pinned Lean binary64 model for the E1 proposal. -/
namespace ReviewCases.E1

private def unpackedValue : Float.Model.UnpackedFloat → Option Rat
  | .zero _ => some 0
  | .finite sign mantissa exponent _ =>
    let magnitude := (mantissa : Rat) * (2 : Rat) ^ exponent
    some (match sign with | .positive => magnitude | .negative => -magnitude)
  | .infinity _ | .notANumber => none

/-- The exponent and the implicit normal bit are recovered by Lean's binary64 unpacker. -/
def value (x : Float) : Option Rat := unpackedValue x.toModel.unpack

theorem value_isSome (x : Float) : (value x).isSome = x.isFinite := by
  change (unpackedValue x.toModel.unpack).isSome = x.toModel.unpack.isFinite
  cases x.toModel.unpack <;> rfl

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
