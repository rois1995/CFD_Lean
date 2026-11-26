import CFDLean.Exec.RealScalar
import CFDLean.Exec.LimiterKernel

/-! Burgers E0c: the real-number sign test of the limiter kernel, `0 < x` with classical decidability. With this
instance and `CFDLean.Exec.RealScalar` the limiter kernel is a (noncomputable) function on arrays of real numbers.
This module is a trusted input of the E0c statements. -/
noncomputable section
namespace CFDLean.Exec

/-- The specification sign test: `isPos x` is `true` exactly when `0 < x`. -/
noncomputable instance instScalarSignReal : ScalarSign ℝ where
  isPos x := decide (0 < x)

end CFDLean.Exec
