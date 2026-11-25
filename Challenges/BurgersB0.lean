import CFDLean.Verification.BurgersB0Challenge

/-! Burgers B0 challenge for `lake comparator` (configuration: `Challenges/BurgersB0.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.BurgersB0Verify` and states one trusted
B0 statement of `CFDLean.Verification.BurgersB0Challenge`, which imports only Mathlib. `sorry` is the hole that the
comparator asks the solution module to fill. This module imports no implementation module. No module imports it, it is
not part of the `CFDLean` library, and `KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.BurgersB0Verify

open CFDLean.Verification.BurgersB0Challenge

theorem rusanov_consistency : RusanovConsistency := sorry

theorem periodic_conservation {I : Type*} [Fintype I] : PeriodicConservation I := sorry

theorem constant_rhs {I : Type*} : ConstantRhs I := sorry

theorem forward_euler_sum {I : Type*} [Fintype I] : ForwardEulerSum I := sorry

end CFDLean.Verification.BurgersB0Verify
