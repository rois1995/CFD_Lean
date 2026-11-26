import CFDLean.Verification.BurgersB3bChallenge

/-! Burgers B3b challenge for `lake comparator` (configuration: `Challenges/BurgersB3b.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.BurgersB3bVerify` and states one trusted
B3b statement of `CFDLean.Verification.BurgersB3bChallenge`, which imports only Mathlib. `sorry` is the hole that the
comparator asks the solution module to fill. This module imports no implementation module. No module imports it, it is
not part of the `CFDLean` library, and `KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.BurgersB3bVerify

open CFDLean.Verification.BurgersB3bChallenge

theorem limiter_factor_forms : LimiterFactorForms := sorry

theorem limiter_bounds : LimiterBounds := sorry

theorem muscl_euler_bounded_multi_step {I : Type*} [Fintype I] : MusclEulerBoundedMultiStep I := sorry

theorem muscl_ssprk2_bounded_multi_step {I : Type*} [Fintype I] : MusclSSPRK2BoundedMultiStep I := sorry

theorem muscl_ssprk3_bounded_multi_step {I : Type*} [Fintype I] : MusclSSPRK3BoundedMultiStep I := sorry

theorem unlimited_overshoot : UnlimitedOvershoot := sorry

end CFDLean.Verification.BurgersB3bVerify
