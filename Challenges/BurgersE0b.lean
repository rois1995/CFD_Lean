import CFDLean.Verification.BurgersE0bChallenge

/-! Burgers E0b challenge for `lake comparator` (configuration: `Challenges/BurgersE0b.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.BurgersE0bVerify` and states one trusted
E0b statement of `CFDLean.Verification.BurgersE0bChallenge`. That module imports Mathlib, the two executable kernels
and the real-number instance (the object under verification), and nothing else. `sorry` is the hole that the
comparator asks the solution module to fill. No module imports this one, it is not part of the `CFDLean` library, and
`KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.BurgersE0bVerify

open CFDLean.Verification.BurgersE0bChallenge

theorem kernel_minmod_is_minmod : KernelMinmodIsMinmod := sorry

theorem muscl_euler_step_refines : MusclEulerStepRefines := sorry

theorem muscl_ssprk3_step_refines : MusclSSPRK3StepRefines := sorry

theorem muscl_ssprk3_run_refines : MusclSSPRK3RunRefines := sorry

theorem muscl_ssprk3_run_bounds : MusclSSPRK3RunBounds := sorry

theorem muscl_ssprk3_run_sum : MusclSSPRK3RunSum := sorry

theorem muscl_ssprk3_run_total_variation : MusclSSPRK3RunTotalVariation := sorry

end CFDLean.Verification.BurgersE0bVerify
