import CFDLean.Verification.FV1DNonuniformChallenge

/-! FVN challenge for `lake comparator` (configuration: `Challenges/FV1DNonuniform.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.FV1DNonuniformVerify` and states one
trusted FVN statement of `CFDLean.Verification.FV1DNonuniformChallenge`, which imports only Mathlib. `sorry` is the
hole that the comparator asks the solution module to fill. This module imports no implementation module. No module
imports it, it is not part of the `CFDLean` library, and `KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.FV1DNonuniformVerify

open CFDLean.Verification.FV1DNonuniformChallenge

theorem first_order_bounds {I : Type*} : FirstOrderBounds I := sorry

theorem first_order_total_variation {I : Type*} [Fintype I] : FirstOrderTotalVariation I := sorry

theorem reconstruction_bounds {I : Type*} : ReconstructionBounds I := sorry

theorem muscl_bounds {I : Type*} : MusclBounds I := sorry

theorem muscl_total_variation {I : Type*} [Fintype I] : MusclTotalVariation I := sorry

theorem muscl_euler_multi_step {I : Type*} [Fintype I] : MusclEulerMultiStep I := sorry

theorem muscl_ssprk2_multi_step {I : Type*} [Fintype I] : MusclSSPRK2MultiStep I := sorry

theorem muscl_ssprk3_multi_step {I : Type*} [Fintype I] : MusclSSPRK3MultiStep I := sorry

theorem mesh_ratio_overshoot : MeshRatioOvershoot := sorry

end CFDLean.Verification.FV1DNonuniformVerify
