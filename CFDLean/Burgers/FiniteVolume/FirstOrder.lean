import CFDLean.Burgers.Core.NumericalFlux
import CFDLean.Burgers.Core.PeriodicGrid

noncomputable section
namespace CFDLean.Burgers.FiniteVolume

open Core

variable {I : Type*}

def interfaceFlux (g : PeriodicGrid I) (numFlux : NumericalFlux)
    (u : I → ℝ) (i : I) : ℝ :=
  numFlux.eval (u i) (u (g.next i))

def rhs (g : PeriodicGrid I) (dx : ℝ) (numFlux : NumericalFlux)
    (u : I → ℝ) (i : I) : ℝ :=
  -(interfaceFlux g numFlux u i - interfaceFlux g numFlux u (g.prev i)) / dx

theorem rhs_constant (g : PeriodicGrid I) (dx c : ℝ)
    (law : ScalarConservationLaw) (numFlux : NumericalFlux)
    (hcons : Consistent law numFlux) (i : I) :
    rhs g dx numFlux (fun _ => c) i = 0 := by
  simp [rhs, interfaceFlux, hcons c]

end CFDLean.Burgers.FiniteVolume
