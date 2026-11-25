import CFDLean.Verification.BurgersB3Challenge

/-! Burgers B3 challenge for `lake comparator` (configuration: `Challenges/BurgersB3.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.BurgersB3Verify` and states one trusted
B3 statement of `CFDLean.Verification.BurgersB3Challenge`, which imports only Mathlib. `sorry` is the hole that the
comparator asks the solution module to fill. This module imports no implementation module. No module imports it, it is
not part of the `CFDLean` library, and `KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.BurgersB3Verify

open CFDLean.Verification.BurgersB3Challenge

theorem minmod_properties : MinmodProperties := sorry

theorem rusanov_lipschitz : RusanovLipschitz := sorry

theorem muscl_euler_multi_step {I : Type*} [Fintype I] : MusclEulerMultiStep I := sorry

theorem muscl_ssprk2_multi_step {I : Type*} [Fintype I] : MusclSSPRK2MultiStep I := sorry

theorem muscl_ssprk3_multi_step {I : Type*} [Fintype I] : MusclSSPRK3MultiStep I := sorry

theorem muscl_euler_conservation {I : Type*} [Fintype I] : MusclEulerConservation I := sorry

theorem muscl_ssprk2_conservation {I : Type*} [Fintype I] : MusclSSPRK2Conservation I := sorry

theorem muscl_ssprk3_conservation {I : Type*} [Fintype I] : MusclSSPRK3Conservation I := sorry

end CFDLean.Verification.BurgersB3Verify
