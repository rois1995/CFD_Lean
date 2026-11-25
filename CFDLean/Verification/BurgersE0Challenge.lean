import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Function.Iterate
import CFDLean.Exec.Kernel
import CFDLean.Exec.RealScalar

/-! Trusted Burgers E0 statements (`specifications/Burgers-E0.md`). The statements are about the executable array
kernel `CFDLean.Exec.Kernel` with the real-number arithmetic of `CFDLean.Exec.RealScalar`; these two modules are the
object under verification and are imported here. Everything else comes from Mathlib and is restated in this file: the
mathematical scheme on `n` periodic cells (`Fin n`, cyclic indices `i + 1` and `i - 1`), the SSPRK3 step, and the
relation between an array and a cell function. No mathematical implementation module is imported. -/
noncomputable section
namespace CFDLean.Verification.BurgersE0Challenge

open scoped BigOperators
open CFDLean.Exec

/-- E0-K: the real instance of the kernel arithmetic is the standard real arithmetic. On the left are the fields of the
instance that the kernel uses; on the right are the operations and literals of Mathlib. -/
def RealScalarIsStandard : Prop :=
  ∀ x y : ℝ,
    Scalar.toAdd.add x y = x + y ∧ Scalar.toSub.sub x y = x - y ∧ Scalar.toMul.mul x y = x * y ∧
    Scalar.toDiv.div x y = x / y ∧ Scalar.toNeg.neg x = -x ∧ (Scalar.toZero.zero : ℝ) = 0 ∧
    Scalar.abs x = |x| ∧ Scalar.max x y = max x y ∧
    (Scalar.two : ℝ) = 2 ∧ (Scalar.half : ℝ) = 1 / 2 ∧ (Scalar.third : ℝ) = 1 / 3 ∧
    (Scalar.twoThirds : ℝ) = 2 / 3 ∧ (Scalar.quarter : ℝ) = 1 / 4 ∧ (Scalar.threeQuarters : ℝ) = 3 / 4

/-- Burgers physical flux `f(u) = u² / 2`. -/
def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

/-- Rusanov wave speed `a(uL, uR) = max(|uL|, |uR|)`. -/
def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

/-- Rusanov (local Lax-Friedrichs) flux for Burgers. -/
def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

/-- E0-R: the kernel flux with real arithmetic is the Rusanov flux. -/
def KernelFluxIsRusanov : Prop :=
  ∀ uL uR : ℝ, Scalar.rusanov uL uR = rusanov uL uR

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Three-stage SSP Runge-Kutta step over a one-step map `E`: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

end Generic

/-- One Forward-Euler step of the first-order finite-volume scheme with the Rusanov flux on `n` periodic cells:
`v_i = u_i - (dt/dx) (F(u_i, u_{i+1}) - F(u_{i-1}, u_i))`, indices modulo `n`. -/
def eulerStep {n : ℕ} [NeZero n] (dx dt : ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => u i + dt * (-(rusanov (u i) (u (i + 1)) - rusanov (u (i - 1)) (u i)) / dx)

/-- The array `a` stores the cell values of `u`: it has `n` entries and entry `i` is `u i`. -/
def Represents {n : ℕ} (a : Array ℝ) (u : Fin n → ℝ) : Prop :=
  a.size = n ∧ ∀ (i : Fin n) (hi : i.val < a.size), a[i.val] = u i

/-- E0-S: the kernel Euler step computes the mathematical Euler step. -/
def EulerStepRefines : Prop :=
  ∀ (n : ℕ) [NeZero n] (dx dt : ℝ) (a : Array ℝ) (u : Fin n → ℝ),
    Represents a u → Represents (eulerStepArray dx dt a) (eulerStep dx dt u)

/-- E0-S: the kernel SSPRK3 step computes the mathematical SSPRK3 step. -/
def SSPRK3StepRefines : Prop :=
  ∀ (n : ℕ) [NeZero n] (dx dt : ℝ) (a : Array ℝ) (u : Fin n → ℝ),
    Represents a u → Represents (ssprk3StepArray dx dt a) (ssprk3 (eulerStep dx dt) u)

/-- E0-N: `k` kernel SSPRK3 steps compute `k` mathematical SSPRK3 steps. -/
def SSPRK3RunRefines : Prop :=
  ∀ (n : ℕ) [NeZero n] (dx dt : ℝ) (a : Array ℝ) (u : Fin n → ℝ) (k : ℕ),
    Represents a u → Represents (run (ssprk3StepArray dx dt) k a) ((ssprk3 (eulerStep dx dt))^[k] u)

/-- E0-D: the kernel sum diagnostic is the sum of the cell values. -/
def SumDiagnostic : Prop :=
  ∀ (n : ℕ) (a : Array ℝ) (u : Fin n → ℝ), Represents a u → sumArray a = ∑ i, u i

/-- E0-D: the kernel total-variation diagnostic is the periodic total variation `Σ_i |u_{i+1} - u_i|`. -/
def TotalVariationDiagnostic : Prop :=
  ∀ (n : ℕ) [NeZero n] (a : Array ℝ) (u : Fin n → ℝ),
    Represents a u → totalVariationArray a = ∑ i, |u (i + 1) - u i|

/-- Every entry of the array is between `m` and `M`. -/
def EntriesBetween (m M : ℝ) (a : Array ℝ) : Prop :=
  ∀ (i : ℕ) (hi : i < a.size), m ≤ a[i] ∧ a[i] ≤ M

/-- E0-T: with `dx > 0`, `dt ≥ 0`, entries between `m` and `M` and `2 · dt · max(|m|, |M|) ≤ dx`, every entry is
between `m` and `M` after `k` kernel SSPRK3 steps. -/
def SSPRK3RunBounds : Prop :=
  ∀ (dx dt m M : ℝ) (a : Array ℝ) (k : ℕ),
    0 < dx → 0 ≤ dt → 2 * (dt * max |m| |M|) ≤ dx → EntriesBetween m M a →
    EntriesBetween m M (run (ssprk3StepArray dx dt) k a)

/-- E0-T: with `dx ≠ 0`, `k` kernel SSPRK3 steps keep the sum of the entries. -/
def SSPRK3RunSum : Prop :=
  ∀ (dx dt : ℝ) (a : Array ℝ) (k : ℕ), dx ≠ 0 →
    sumArray (run (ssprk3StepArray dx dt) k a) = sumArray a

/-- E0-T: under the hypotheses of the bounds statement, `k` kernel SSPRK3 steps do not increase the total variation
of the entries. -/
def SSPRK3RunTotalVariation : Prop :=
  ∀ (dx dt m M : ℝ) (a : Array ℝ) (k : ℕ),
    0 < dx → 0 ≤ dt → 2 * (dt * max |m| |M|) ≤ dx → EntriesBetween m M a →
    totalVariationArray (run (ssprk3StepArray dx dt) k a) ≤ totalVariationArray a

end CFDLean.Verification.BurgersE0Challenge
