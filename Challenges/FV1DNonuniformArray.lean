import CFDLean.Verification.FV1DNonuniformArrayChallenge

/-! FVNA challenge for `lake comparator` (configuration: `Challenges/FV1DNonuniformArray.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.FV1DNonuniformArrayVerify` and states one
trusted FVNA statement (FVNA-M, FVNA-T) of `CFDLean.Verification.FV1DNonuniformArrayChallenge`. That module imports
Mathlib, the executable kernels (`Kernel`, `MusclKernel`, `LimiterKernel`, `FV1D`, `NonuniformKernel`), the
real-number instance and the real sign test (the object under verification), and nothing else. `sorry` is the hole
that the comparator asks the solution module to fill. No module imports this one, it is not part of the `CFDLean`
library, and `KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.FV1DNonuniformArrayVerify

open CFDLean.Verification.FV1DNonuniformArrayChallenge

theorem muscl_euler_step_refines : MusclEulerStepRefines := sorry

theorem muscl_ssprk2_step_refines : MusclSSPRK2StepRefines := sorry

theorem muscl_ssprk3_step_refines : MusclSSPRK3StepRefines := sorry

theorem first_order_weighted_sum : FirstOrderWeightedSum := sorry

theorem muscl_euler_weighted_sum : MusclEulerWeightedSum := sorry

theorem muscl_ssprk2_weighted_sum : MusclSSPRK2WeightedSum := sorry

theorem muscl_ssprk3_weighted_sum : MusclSSPRK3WeightedSum := sorry

theorem euler_first_order_weighted_sum : EulerFirstOrderWeightedSum := sorry

theorem first_order_bounds : FirstOrderBounds := sorry

theorem first_order_total_variation : FirstOrderTotalVariation := sorry

theorem muscl_euler_run_stable : MusclEulerRunStable := sorry

theorem muscl_ssprk2_run_stable : MusclSSPRK2RunStable := sorry

theorem muscl_ssprk3_run_stable : MusclSSPRK3RunStable := sorry

end CFDLean.Verification.FV1DNonuniformArrayVerify
