import CFDLean.Verification.BurgersB1Challenge

/-! Burgers B1 challenge for `lake comparator` (configuration: `Challenges/BurgersB1.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.BurgersB1Verify` and states one trusted
B1 statement of `CFDLean.Verification.BurgersB1Challenge`, which imports only Mathlib. `sorry` is the hole that the
comparator asks the solution module to fill. This module imports no implementation module. No module imports it, it is
not part of the `CFDLean` library, and `KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.BurgersB1Verify

open CFDLean.Verification.BurgersB1Challenge

theorem rusanov_monotone : RusanovMonotone := sorry

theorem harten_total_variation {I : Type*} [Fintype I] : HartenTotalVariation I := sorry

theorem incremental_bounds {I : Type*} : IncrementalBounds I := sorry

theorem rusanov_total_variation {I : Type*} [Fintype I] : RusanovTotalVariation I := sorry

theorem rusanov_bounds {I : Type*} : RusanovBounds I := sorry

end CFDLean.Verification.BurgersB1Verify
