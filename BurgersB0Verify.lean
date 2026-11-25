import BurgersB0Challenge
import CFDLean.Burgers

noncomputable section
namespace CFDLean.BurgersB0Verify

open scoped BigOperators
open CFDLean.Burgers
open CFDLean.Burgers.Core

theorem rusanov_consistency :
    BurgersB0Challenge.RusanovConsistency := by
  intro u
  simpa [BurgersB0Challenge.rusanov, BurgersB0Challenge.rusanovWaveSpeed,
    BurgersB0Challenge.burgersFlux, Rusanov.eval, Rusanov.waveSpeed, physicalFlux] using
    Rusanov.consistent u

theorem periodic_conservation {I : Type*} [Fintype I] :
    BurgersB0Challenge.PeriodicConservation I := by
  intro next dx hdx numericalFlux u
  let g : PeriodicGrid I := ⟨next⟩
  let nf : NumericalFlux := ⟨numericalFlux⟩
  have h := FiniteVolume.rhs_sum_zero g dx hdx nf u
  simpa [BurgersB0Challenge.rhs, BurgersB0Challenge.interfaceFlux,
    BurgersB0Challenge.prev, FiniteVolume.rhs, FiniteVolume.interfaceFlux,
    PeriodicGrid.prev, g, nf] using h

theorem constant_rhs {I : Type*} :
    BurgersB0Challenge.ConstantRhs I := by
  intro next dx physical numericalFlux hcons c i
  let g : PeriodicGrid I := ⟨next⟩
  let law : ScalarConservationLaw := ⟨physical⟩
  let nf : NumericalFlux := ⟨numericalFlux⟩
  have hc : Consistent law nf := by
    intro u
    exact hcons u
  have h := FiniteVolume.rhs_constant g dx c law nf hc i
  simpa [BurgersB0Challenge.rhs, BurgersB0Challenge.interfaceFlux,
    BurgersB0Challenge.prev, FiniteVolume.rhs, FiniteVolume.interfaceFlux,
    PeriodicGrid.prev, g, law, nf] using h

theorem forward_euler_sum {I : Type*} [Fintype I] :
    BurgersB0Challenge.ForwardEulerSum I := by
  intro dt L u hL
  have h := Time.step_sum dt L u hL
  simpa [BurgersB0Challenge.forwardEuler, Time.step] using h

end CFDLean.BurgersB0Verify
