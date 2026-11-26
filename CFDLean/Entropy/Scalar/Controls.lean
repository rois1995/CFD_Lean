import CFDLean.Entropy.Scalar.Burgers

/-! Exact small controls for Burgers B4. -/
noncomputable section
namespace CFDLean.Burgers.EntropyControls

open CFDLean.Burgers CFDLean.Scalar

example : EntropyConservativeFlux.eval 1 2 = 7 / 6 := by norm_num [EntropyConservativeFlux.eval]

example : Rusanov.eval 1 2 = 1 / 4 := by norm_num [Rusanov.eval, Rusanov.waveSpeed, physicalFlux]

-- The Rusanov flux is strictly entropy dissipative on the pair (1, 2): (2 - 1) · 1/4 < 2³/6 - 1³/6.
example : (entropyVariable 2 - entropyVariable 1) * Rusanov.eval 1 2 < entropyPotential 2 - entropyPotential 1 := by
  norm_num [entropyVariable, entropyPotential, Rusanov.eval, Rusanov.waveSpeed, physicalFlux]

-- The central flux (f(a) + f(b))/2 is not entropy stable: it fails on the pair (1, 2), where 5/4 > 7/6.
example : ¬ EntropyStable entropyVariable entropyPotential ⟨fun a b => (physicalFlux a + physicalFlux b) / 2⟩ := by
  intro h
  have h1 := h 1 2
  norm_num [entropyVariable, entropyPotential, physicalFlux] at h1

example : EntropyStable entropyVariable entropyPotential EntropyConservativeFlux.numericalFlux :=
  EntropyConservativeFlux.entropyConservative.entropyStable

end CFDLean.Burgers.EntropyControls
