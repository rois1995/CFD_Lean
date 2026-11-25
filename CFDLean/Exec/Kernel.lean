/-! Burgers E0-K, the kernel: an executable array implementation of the first-order periodic Rusanov finite-volume scheme for the
1D Burgers equation with Forward Euler, SSPRK2 and SSPRK3 in Shu-Osher form. Generic over the arithmetic `α`; the
`Float` instance is for execution, the `ℝ` instance (`CFDLean.Exec.RealScalar`) is for the specification. No Mathlib. -/
namespace CFDLean.Exec

/-- The arithmetic that the kernel uses. The SSP coefficients are fields so that the `ℝ` instance gives them as the
literals `1 / 2`, `1 / 3`, ... of the mathematical scheme. -/
class Scalar (α : Type) extends Add α, Sub α, Mul α, Div α, Neg α, Zero α where
  abs : α → α
  max : α → α → α
  two : α
  half : α
  third : α
  twoThirds : α
  quarter : α
  threeQuarters : α

-- The parent projections are instances of low priority. A type with its own arithmetic (`Float`, `ℝ`) keeps it:
-- `x / y` on `ℝ` is the Mathlib division also in a module that imports a `Scalar ℝ` instance.
attribute [instance 10] Scalar.toAdd Scalar.toSub Scalar.toMul Scalar.toDiv Scalar.toNeg Scalar.toZero

namespace Scalar

variable {α : Type} [Scalar α]

/-- Burgers flux `u² / 2`. -/
def burgersFlux (u : α) : α := u * u / two

/-- Rusanov (local Lax-Friedrichs) numerical flux. -/
def rusanov (uL uR : α) : α :=
  (burgersFlux uL + burgersFlux uR) / two - Scalar.max (abs uL) (abs uR) / two * (uR - uL)

end Scalar

open Scalar

variable {α : Type} [Scalar α]

theorem succ_mod_lt {n : Nat} (i : Fin n) : (i.val + 1) % n < n := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)

theorem pred_mod_lt {n : Nat} (i : Fin n) : (i.val + n - 1) % n < n :=
  Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.2)

/-- One Forward-Euler step of the periodic Rusanov scheme; entry `i` is
`u[i] + dt * (-(F(u[i], u[i+1]) - F(u[i-1], u[i])) / dx)` with periodic indices. Same size as `u`. -/
def eulerStepArray (dx dt : α) (u : Array α) : Array α :=
  Array.ofFn fun i : Fin u.size =>
    u[i] + dt * (-(rusanov u[i] (u[(i.val + 1) % u.size]'(succ_mod_lt i)) -
      rusanov (u[(i.val + u.size - 1) % u.size]'(pred_mod_lt i)) u[i]) / dx)

/-- Entrywise `a * x[i] + b * y[i]`. The result has size `min x.size y.size` (extra entries are dropped). -/
def axpby (a : α) (x : Array α) (b : α) (y : Array α) : Array α :=
  Array.zipWith (fun p q => a * p + b * q) x y

/-- SSPRK2 in Shu-Osher form: `½ u + ½ E(E u)`. -/
def ssprk2StepArray (dx dt : α) (u : Array α) : Array α :=
  axpby half u half (eulerStepArray dx dt (eulerStepArray dx dt u))

/-- SSPRK3 in Shu-Osher form: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3StepArray (dx dt : α) (u : Array α) : Array α :=
  axpby third u twoThirds
    (eulerStepArray dx dt (axpby threeQuarters u quarter (eulerStepArray dx dt (eulerStepArray dx dt u))))

/-- `n` steps of `step` (tail recursive; same recursion as `Nat.iterate`). -/
def run {β : Type} (step : β → β) : Nat → β → β
  | 0, u => u
  | n + 1, u => run step n (step u)

/-- Sum of the entries. -/
def sumArray (u : Array α) : α := u.sum

/-- Largest entry (`0` for the empty array). -/
def maxArray (u : Array α) : α :=
  if h : 0 < u.size then u.foldl Scalar.max u[0] else 0

/-- Smallest entry (`0` for the empty array), via `min a b = -max (-a) (-b)`. -/
def minArray (u : Array α) : α :=
  if h : 0 < u.size then u.foldl (fun a b => -Scalar.max (-a) (-b)) u[0] else 0

/-- Periodic total variation `Σ |u[(i+1) % n] - u[i]|`. -/
def totalVariationArray (u : Array α) : α :=
  (Array.ofFn fun i : Fin u.size => abs ((u[(i.val + 1) % u.size]'(succ_mod_lt i)) - u[i])).sum

instance : Scalar Float where
  zero := 0
  abs := Float.abs
  max a b := if a ≤ b then b else a
  two := 2
  half := 0.5
  third := 1 / 3
  twoThirds := 2 / 3
  quarter := 0.25
  threeQuarters := 0.75

end CFDLean.Exec
