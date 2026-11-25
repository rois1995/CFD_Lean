import CFDLean.Verification.BurgersB2Challenge

/-! Burgers B2 challenge for `lake comparator` (configuration: `Challenges/BurgersB2.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.BurgersB2Verify` and states one trusted
B2 statement of `CFDLean.Verification.BurgersB2Challenge`, which imports only Mathlib. `sorry` is the hole that the
comparator asks the solution module to fill. This module imports no implementation module. No module imports it, it is
not part of the `CFDLean` library, and `KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.BurgersB2Verify

open CFDLean.Verification.BurgersB2Challenge

theorem ssprk2_convex {V : Type*} [AddCommGroup V] [Module ℝ V] : SSPRK2Convex V := sorry

theorem ssprk3_convex {V : Type*} [AddCommGroup V] [Module ℝ V] : SSPRK3Convex V := sorry

theorem euler_multi_step {I : Type*} [Fintype I] : EulerMultiStep I := sorry

theorem ssprk2_multi_step {I : Type*} [Fintype I] : SSPRK2MultiStep I := sorry

theorem ssprk3_multi_step {I : Type*} [Fintype I] : SSPRK3MultiStep I := sorry

theorem ssprk2_conservation {I : Type*} [Fintype I] : SSPRK2Conservation I := sorry

theorem ssprk3_conservation {I : Type*} [Fintype I] : SSPRK3Conservation I := sorry

end CFDLean.Verification.BurgersB2Verify
