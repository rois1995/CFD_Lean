import CFDLean.Verification.BurgersE0Challenge

/-! Burgers E0 challenge for `lake comparator` (configuration: `Challenges/BurgersE0.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.BurgersE0Verify` and states one trusted
E0 statement of `CFDLean.Verification.BurgersE0Challenge`. That module imports Mathlib, the executable kernel and its
real-number instance (the object under verification), and nothing else. `sorry` is the hole that the comparator asks
the solution module to fill. No module imports this one, it is not part of the `CFDLean` library, and
`KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.BurgersE0Verify

open CFDLean.Verification.BurgersE0Challenge

theorem real_scalar_is_standard : RealScalarIsStandard := sorry

theorem kernel_flux_is_rusanov : KernelFluxIsRusanov := sorry

theorem euler_step_refines : EulerStepRefines := sorry

theorem ssprk3_step_refines : SSPRK3StepRefines := sorry

theorem ssprk3_run_refines : SSPRK3RunRefines := sorry

theorem sum_diagnostic : SumDiagnostic := sorry

theorem total_variation_diagnostic : TotalVariationDiagnostic := sorry

theorem ssprk3_run_bounds : SSPRK3RunBounds := sorry

theorem ssprk3_run_sum : SSPRK3RunSum := sorry

theorem ssprk3_run_total_variation : SSPRK3RunTotalVariation := sorry

end CFDLean.Verification.BurgersE0Verify
