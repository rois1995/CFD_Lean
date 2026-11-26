import CFDLean.Verification.BurgersE0cChallenge

/-! Burgers E0c challenge for `lake comparator` (configuration: `Challenges/BurgersE0c.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.BurgersE0cVerify` and states one trusted
E0c statement of `CFDLean.Verification.BurgersE0cChallenge`. That module imports Mathlib, the executable kernels, the
real-number instance and the real sign test (the object under verification), and nothing else. `sorry` is the hole
that the comparator asks the solution module to fill. No module imports this one, it is not part of the `CFDLean`
library, and `KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.BurgersE0cVerify

open CFDLean.Verification.BurgersE0cChallenge

theorem real_sign_is_standard : RealSignIsStandard := sorry

theorem kernel_slope_is_limiter : KernelSlopeIsLimiter := sorry

theorem limiter_euler_step_refines : LimiterEulerStepRefines := sorry

theorem limiter_ssprk3_step_refines : LimiterSSPRK3StepRefines := sorry

theorem limiter_ssprk3_run_refines : LimiterSSPRK3RunRefines := sorry

theorem limiter_ssprk3_run_sum : LimiterSSPRK3RunSum := sorry

theorem limiter_ssprk3_run_bounds : LimiterSSPRK3RunBounds := sorry

theorem limiter_ssprk3_run_total_variation : LimiterSSPRK3RunTotalVariation := sorry

end CFDLean.Verification.BurgersE0cVerify
