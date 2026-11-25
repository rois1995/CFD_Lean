import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field

noncomputable section
namespace CFDLean.BurgersB0Challenge

open scoped BigOperators

def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

def Consistent (physicalFlux : ℝ → ℝ) (numericalFlux : ℝ → ℝ → ℝ) : Prop :=
  ∀ u, numericalFlux u u = physicalFlux u

def RusanovConsistency : Prop :=
  ∀ u, rusanov u u = burgersFlux u

variable {I : Type*}

def prev (next : I ≃ I) : I → I := next.symm

def interfaceFlux (next : I ≃ I) (numericalFlux : ℝ → ℝ → ℝ)
    (u : I → ℝ) (i : I) : ℝ :=
  numericalFlux (u i) (u (next i))

def rhs (next : I ≃ I) (dx : ℝ) (numericalFlux : ℝ → ℝ → ℝ)
    (u : I → ℝ) (i : I) : ℝ :=
  -(interfaceFlux next numericalFlux u i -
      interfaceFlux next numericalFlux u (prev next i)) / dx

def PeriodicConservation (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (dx : ℝ) (hdx : dx ≠ 0)
    (numericalFlux : ℝ → ℝ → ℝ) (u : I → ℝ),
    ∑ i, rhs next dx numericalFlux u i = 0

def ConstantRhs (I : Type*) : Prop :=
  ∀ (next : I ≃ I) (dx : ℝ) (physicalFlux : ℝ → ℝ)
    (numericalFlux : ℝ → ℝ → ℝ),
    Consistent physicalFlux numericalFlux →
    ∀ c i, rhs next dx numericalFlux (fun _ : I => c) i = 0

def forwardEuler (dt : ℝ) (L : (I → ℝ) → I → ℝ) (u : I → ℝ) : I → ℝ :=
  fun i => u i + dt * L u i

def ForwardEulerSum (I : Type*) [Fintype I] : Prop :=
  ∀ (dt : ℝ) (L : (I → ℝ) → I → ℝ) (u : I → ℝ),
    (∑ i, L u i = 0) →
    ∑ i, forwardEuler dt L u i = ∑ i, u i

end CFDLean.BurgersB0Challenge
