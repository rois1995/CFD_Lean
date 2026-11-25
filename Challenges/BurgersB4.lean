import CFDLean.Verification.BurgersB4Challenge

/-! Burgers B4 challenge for `lake comparator` (configuration: `Challenges/BurgersB4.comparator.json`).

Each theorem below has the name of one bridge theorem of `CFDLean.Verification.BurgersB4Verify` and states one trusted
B4 statement of `CFDLean.Verification.BurgersB4Challenge`, which imports only Mathlib. `sorry` is the hole that the
comparator asks the solution module to fill. This module imports no implementation module. No module imports it, it is
not part of the `CFDLean` library, and `KernelAudit.lean` does not load it. -/
set_option warningAsError false

namespace CFDLean.Verification.BurgersB4Verify

open CFDLean.Verification.BurgersB4Challenge

theorem entropy_conservative_flux_properties : EntropyConservativeFluxProperties := sorry

theorem rusanov_entropy_stable : RusanovEntropyStable := sorry

theorem cell_entropy_inequality {I : Type*} : CellEntropyInequality I := sorry

theorem entropy_production_nonpos {I : Type*} [Fintype I] : EntropyProductionNonpos I := sorry

theorem rusanov_energy_production {I : Type*} [Fintype I] : RusanovEnergyProduction I := sorry

end CFDLean.Verification.BurgersB4Verify
