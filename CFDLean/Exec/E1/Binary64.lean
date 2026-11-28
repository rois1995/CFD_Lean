import Init.Data.Float
import Init.Data.Rat

/-! Exact finite-value interpretation of the pinned Lean binary64 model for the E1 proposal. -/
namespace CFDLean.Exec.E1

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

end CFDLean.Exec.E1
