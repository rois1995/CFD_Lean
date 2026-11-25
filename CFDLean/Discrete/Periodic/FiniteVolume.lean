import CFDLean.Schemes.Scalar.NumericalFlux
import CFDLean.Discrete.Periodic.Grid

noncomputable section
namespace CFDLean.Scalar.FiniteVolume

open Periodic

variable {I : Type*}

def interfaceFlux (g : Grid I) (numFlux : NumericalFlux)
    (u : I → ℝ) (i : I) : ℝ :=
  numFlux.eval (u i) (u (g.next i))

def rhs (g : Grid I) (dx : ℝ) (numFlux : NumericalFlux)
    (u : I → ℝ) (i : I) : ℝ :=
  -(interfaceFlux g numFlux u i - interfaceFlux g numFlux u (g.prev i)) / dx

theorem rhs_constant (g : Grid I) (dx c : ℝ)
    (law : ConservationLaw) (numFlux : NumericalFlux)
    (hcons : Consistent law numFlux) (i : I) :
    rhs g dx numFlux (fun _ => c) i = 0 := by
  simp [rhs, interfaceFlux, hcons c]

end CFDLean.Scalar.FiniteVolume
