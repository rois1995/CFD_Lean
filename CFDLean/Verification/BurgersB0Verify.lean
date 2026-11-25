import CFDLean.Verification.BurgersB0Challenge
import CFDLean.Burgers

noncomputable section
namespace CFDLean.Verification.BurgersB0Verify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Burgers.Core

theorem rusanov_consistency :
    CFDLean.Verification.BurgersB0Challenge.RusanovConsistency := by
  intro u
  exact Rusanov.consistent u

theorem periodic_conservation {I : Type*} [Fintype I] :
    CFDLean.Verification.BurgersB0Challenge.PeriodicConservation I := by
  intro next dx numericalFlux u hdx
  let g : PeriodicGrid I := ⟨next⟩
  let nf : NumericalFlux := ⟨numericalFlux⟩
  have h := FiniteVolume.rhs_sum_zero g dx hdx nf u
  simpa [CFDLean.Verification.BurgersB0Challenge.rhs,
    CFDLean.Verification.BurgersB0Challenge.interfaceFlux,
    CFDLean.Verification.BurgersB0Challenge.prev,
    FiniteVolume.rhs, FiniteVolume.interfaceFlux,
    PeriodicGrid.prev, g, nf] using h

theorem constant_rhs {I : Type*} :
    CFDLean.Verification.BurgersB0Challenge.ConstantRhs I := by
  intro next dx physical numericalFlux hcons c i
  let g : PeriodicGrid I := ⟨next⟩
  let law : ScalarConservationLaw := ⟨physical⟩
  let nf : NumericalFlux := ⟨numericalFlux⟩
  have hc : Consistent law nf := by
    intro u
    exact hcons u
  have h := FiniteVolume.rhs_constant g dx c law nf hc i
  simpa [CFDLean.Verification.BurgersB0Challenge.rhs,
    CFDLean.Verification.BurgersB0Challenge.interfaceFlux,
    CFDLean.Verification.BurgersB0Challenge.prev,
    FiniteVolume.rhs, FiniteVolume.interfaceFlux,
    PeriodicGrid.prev, g, law, nf] using h

theorem forward_euler_sum {I : Type*} [Fintype I] :
    CFDLean.Verification.BurgersB0Challenge.ForwardEulerSum I := by
  intro dt L u hL
  exact Time.step_sum dt L u hL

end CFDLean.Verification.BurgersB0Verify
