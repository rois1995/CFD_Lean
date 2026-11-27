import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import CFDLean.Exec.Kernel
import CFDLean.Exec.RealScalar
import CFDLean.Exec.MusclKernel
import CFDLean.Exec.LimiterKernel
import CFDLean.Exec.RealScalarSign
import CFDLean.Exec.FV1D
import CFDLean.Exec.NonuniformKernel

/-! Trusted FVNA statements (`specifications/FV1D-nonuniform-array.md`: FVNA-M and FVNA-T). The statements are about
the executable non-uniform kernels `CFDLean.Exec.NonuniformKernel` (which use `CFDLean.Exec.LimiterKernel`,
`CFDLean.Exec.MusclKernel`, `CFDLean.Exec.FV1D` and `CFDLean.Exec.Kernel`) with the real-number arithmetic of
`CFDLean.Exec.RealScalar` and the real sign test of `CFDLean.Exec.RealScalarSign`; these seven modules are the object
under verification and are imported here. Everything else comes from Mathlib and is restated in this file: the slope
function of each limiter in classical form, the FVN MUSCL step on `n` periodic cells of the non-uniform mesh, the
SSPRK2 and SSPRK3 steps, the relation between an array and a cell function, the bounds of the entries of an array and
the mesh ratio of a width array. No mathematical implementation module is imported.

Cells are the residues `ZMod n`: the right neighbour of cell `j` is `j + 1` and the left neighbour `j - 1`, with
`n - 1 + 1 = 0` (the seam). Array entry `i` stores periodic cell `(i : ZMod n)`. The mesh is a cell function `w` of
positive widths (the FVN mesh `mesh widths` when `widths` stores `w`); face `j` lies between cell `j` and cell `j + 1`
and `δ j = (w j + w (j + 1)) / 2` is the distance between their centroids. In the array statements, `prevIdx i` and
`nextIdx i` (kernel `CFDLean.Exec.MusclKernel`) are the periodic left and right neighbours `(i + n - 1) % n` and
`(i + 1) % n` of array index `i`. The kernel diagnostics `sumArray` (the sum of the entries) and
`totalVariationArray` (the periodic total variation `Σ_i |u[(i + 1) % n] - u[i]|`) come from `CFDLean.Exec.Kernel`,
as in the E0, E0b and E0c statements. `run step k u` is `k` applications of `step` to `u`. -/
noncomputable section
namespace CFDLean.Verification.FV1DNonuniformArrayChallenge

open CFDLean.Exec

/-! ### Burgers flux and slope functions -/

/-- Burgers physical flux `f(u) = u² / 2`. -/
def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

/-- Rusanov wave speed `a(uL, uR) = max(|uL|, |uR|)`. -/
def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

/-- Rusanov (local Lax-Friedrichs) flux for Burgers: `(f(uL) + f(uR)) / 2 - a(uL, uR) / 2 · (uR - uL)`. -/
def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

/-- Sign of `a`, used only for `a ≠ 0`. -/
def sgn (a : ℝ) : ℝ := if 0 < a then 1 else -1

/-- The slope function of each limiter, in classical form. `none` is the unlimited central slope `(a + b) / 2`. All
others are zero unless `a` and `b` have the same strict sign. `a` is the backward and `b` the forward difference. -/
def slopeOf : Limiter → ℝ → ℝ → ℝ
  | .none, a, b => (a + b) / 2
  | .minmod, a, b => if 0 < a ∧ 0 < b then min a b else if a < 0 ∧ b < 0 then max a b else 0
  | .mc, a, b => if 0 < a * b then sgn a * min (|a + b| / 2) (min (2 * |a|) (2 * |b|)) else 0
  | .superbee, a, b => if 0 < a * b then sgn a * max (min (2 * |a|) |b|) (min |a| (2 * |b|)) else 0
  | .vanLeer, a, b => if 0 < a * b then 2 * (a * b) / (a + b) else 0
  | .vanAlbada, a, b => if 0 < a * b then a * b * (a + b) / (a ^ 2 + b ^ 2) else 0

/-- The bound constant `θ` of each limiter (`|slope| ≤ θ|a|`, `|slope| ≤ θ|b|`); the mesh ratio of FVNA-T (c) uses
it. It is not used for `none`. -/
def thetaOf : Limiter → ℝ
  | .none => 0
  | .minmod => 1
  | .mc => 2
  | .superbee => 2
  | .vanLeer => 2
  | .vanAlbada => 5 / 4

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Two-stage SSP Runge-Kutta step over a one-step map `E`: `½ u + ½ E(E u)`. -/
def ssprk2 (E : V → V) (u : V) : V := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • E (E u)

/-- Three-stage SSP Runge-Kutta step over a one-step map `E`: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

end Generic

/-! ### The FVN MUSCL step on the non-uniform periodic mesh -/

section Mesh

variable {n : ℕ}

/-- Distance between the centroids of cells `j` and `j + 1`: `δ j = (w j + w (j + 1)) / 2`. -/
def spacing (w : ZMod n → ℝ) (j : ZMod n) : ℝ := (w j + w (j + 1)) / 2

/-- Backward difference of cell `j`, rescaled to its width: `back j = (w j / δ (j - 1)) · (u j - u (j - 1))`. -/
def backDiff (w u : ZMod n → ℝ) (j : ZMod n) : ℝ := w j / spacing w (j - 1) * (u j - u (j - 1))

/-- Forward difference of cell `j`, rescaled to its width: `fwd j = (w j / δ j) · (u (j + 1) - u j)`. -/
def fwdDiff (w u : ZMod n → ℝ) (j : ZMod n) : ℝ := w j / spacing w j * (u (j + 1) - u j)

/-- Slope of cell `j` for the slope function `φ`: `s j = φ(back j, fwd j)`. -/
def slope (φ : ℝ → ℝ → ℝ) (w u : ZMod n → ℝ) (j : ZMod n) : ℝ := φ (backDiff w u j) (fwdDiff w u j)

/-- Left state at face `j`, reconstructed in cell `j`: `u j + (1/2) · s j`. -/
def leftState (φ : ℝ → ℝ → ℝ) (w u : ZMod n → ℝ) (j : ZMod n) : ℝ := u j + 1 / 2 * slope φ w u j

/-- Right state at face `j`, reconstructed in cell `j + 1`: `u (j + 1) - (1/2) · s (j + 1)`. -/
def rightState (φ : ℝ → ℝ → ℝ) (w u : ZMod n → ℝ) (j : ZMod n) : ℝ :=
  u (j + 1) - 1 / 2 * slope φ w u (j + 1)

/-- One Forward-Euler step of the Burgers MUSCL-Rusanov scheme on the mesh `w` with the slope function `φ`:
`v j = u j - (dt / w j) · (F(left j, right j) - F(left (j - 1), right (j - 1)))`. -/
def musclStep (φ : ℝ → ℝ → ℝ) (w : ZMod n → ℝ) (dt : ℝ) (u : ZMod n → ℝ) : ZMod n → ℝ :=
  fun j => u j - dt / w j *
    (rusanov (leftState φ w u j) (rightState φ w u j) - rusanov (leftState φ w u (j - 1)) (rightState φ w u (j - 1)))

/-- The array `a` stores the cell function `u` on `n` periodic cells: it has `n` entries and entry `i` is
`u (i : ZMod n)`. -/
def Represents (a : Array ℝ) (u : ZMod n → ℝ) : Prop :=
  a.size = n ∧ ∀ (i : ℕ) (hi : i < a.size), a[i] = u (i : ZMod n)

end Mesh

/-! ### Array predicates -/

/-- Every entry of the array is between `m` and `M`. -/
def EntriesBetween (m M : ℝ) (a : Array ℝ) : Prop :=
  ∀ (i : ℕ) (hi : i < a.size), m ≤ a[i] ∧ a[i] ≤ M

/-- Mesh ratio `θ` of the width array: at every face `i` (between cells `i` and `i + 1`, periodic),
`θ · max(w[i], w[i+1]) ≤ w[i] + w[i+1]`. -/
def MeshRatio (widths : Array ℝ) (θ : ℝ) : Prop :=
  ∀ i : Fin widths.size, θ * max widths[i] widths[nextIdx i] ≤ widths[i] + widths[nextIdx i]

/-- The width-weighted sum `∑ i, w[i] * u[i]` of two arrays of the same size (the kernel sum of the entrywise
products). -/
def weightedSum (widths u : Array ℝ) : ℝ := sumArray (Array.zipWith (· * ·) widths u)

/-! ### FVNA-M: the MUSCL kernels compute the FVN MUSCL steps -/

/-- FVNA-M (Forward Euler): for every limiter `L`, also `none`, every `n ≥ 1`, a width array storing positive widths
`w` and an array storing `u`, the non-uniform MUSCL kernel computes the FVN MUSCL step on `w` with the slope function
of `L`, in every cell. -/
def MusclEulerStepRefines : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dt : ℝ) (widths a : Array ℝ) (w u : ZMod n → ℝ),
    Represents widths w → (∀ j, 0 < w j) → Represents a u →
    Represents (nuLimiterEulerStepArray L dt widths a) (musclStep (slopeOf L) w dt u)

/-- FVNA-M (SSPRK2): the same for the SSPRK2 kernel and the SSPRK2 combination of the FVN MUSCL step. -/
def MusclSSPRK2StepRefines : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dt : ℝ) (widths a : Array ℝ) (w u : ZMod n → ℝ),
    Represents widths w → (∀ j, 0 < w j) → Represents a u →
    Represents (nuLimiterSsprk2StepArray L dt widths a) (ssprk2 (musclStep (slopeOf L) w dt) u)

/-- FVNA-M (SSPRK3): the same for the SSPRK3 kernel and the SSPRK3 combination of the FVN MUSCL step. -/
def MusclSSPRK3StepRefines : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dt : ℝ) (widths a : Array ℝ) (w u : ZMod n → ℝ),
    Represents widths w → (∀ j, 0 < w j) → Represents a u →
    Represents (nuLimiterSsprk3StepArray L dt widths a) (ssprk3 (musclStep (slopeOf L) w dt) u)

/-! ### FVNA-T (a): conservation of the width-weighted sum -/

/-- FVNA-T (a), Burgers first order: for `n ≥ 1` and arrays `widths`, `u` of size `n` with positive widths, the
first-order kernel with the real Burgers model keeps `∑ i, w[i] * u[i]`. -/
def FirstOrderWeightedSum : Prop :=
  ∀ (n : ℕ) [NeZero n] (dt : ℝ) (widths u : Array ℝ), widths.size = n → u.size = n →
    (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) →
    weightedSum widths (FV1D.nonuniformStepArray FV1D.burgers (1 / 2) dt widths u) = weightedSum widths u

/-- FVNA-T (a), Burgers MUSCL Forward Euler: for every limiter `L`, also `none`, the kernel keeps
`∑ i, w[i] * u[i]`. -/
def MusclEulerWeightedSum : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dt : ℝ) (widths u : Array ℝ), widths.size = n → u.size = n →
    (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) →
    weightedSum widths (nuLimiterEulerStepArray L dt widths u) = weightedSum widths u

/-- FVNA-T (a), Burgers MUSCL SSPRK2: for every limiter `L`, also `none`, the kernel keeps `∑ i, w[i] * u[i]`. -/
def MusclSSPRK2WeightedSum : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dt : ℝ) (widths u : Array ℝ), widths.size = n → u.size = n →
    (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) →
    weightedSum widths (nuLimiterSsprk2StepArray L dt widths u) = weightedSum widths u

/-- FVNA-T (a), Burgers MUSCL SSPRK3: for every limiter `L`, also `none`, the kernel keeps `∑ i, w[i] * u[i]`. -/
def MusclSSPRK3WeightedSum : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dt : ℝ) (widths u : Array ℝ), widths.size = n → u.size = n →
    (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) →
    weightedSum widths (nuLimiterSsprk3StepArray L dt widths u) = weightedSum widths u

/-- FVNA-T (a), Euler first order: for every `γ`, the first-order kernel with the real Euler model (the FVA model
`FV1D.euler` with the real `|·|`, `√` and `max`; a state is `(ρ, ρu, E)` as `Fin 3 → ℝ`) keeps
`∑ i, w[i] * U[i] k` separately for each conserved quantity `k`: density (`k = 0`), x-momentum (`k = 1`) and total
energy (`k = 2`). -/
def EulerFirstOrderWeightedSum : Prop :=
  ∀ (n : ℕ) [NeZero n] (γ dt : ℝ) (widths : Array ℝ) (U : Array (FV1D.EulerState ℝ)), widths.size = n →
    U.size = n → (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) → ∀ k : Fin 3,
    weightedSum widths
        ((FV1D.nonuniformStepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1 / 2) dt widths U).map (fun s => s k)) =
      weightedSum widths (U.map (fun s => s k))

/-! ### FVNA-T (b): first-order Burgers bounds and total variation -/

/-- FVNA-T (b), bounds: for `n ≥ 1`, arrays `widths`, `u` of size `n` with positive widths, `dt ≥ 0` and every entry
of `u` in `[m, M]`, if the FVN-B cell condition `dt · (a (i-1) + a i) ≤ w[i]` holds in every cell `i`, with
`a i = max(|u[i]|, |u[i+1]|)` the Rusanov speed of face `i`, then every entry of the first-order Burgers kernel output
is in `[m, M]`. -/
def FirstOrderBounds : Prop :=
  ∀ (n : ℕ) [NeZero n] (dt m M : ℝ) (widths u : Array ℝ) (hw : widths.size = n) (hu : u.size = n),
    (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) → 0 ≤ dt → EntriesBetween m M u →
    (∀ i : Fin u.size,
      dt * (rusanovWaveSpeed u[prevIdx i] u[i] + rusanovWaveSpeed u[i] u[nextIdx i]) ≤ widths[i]) →
    EntriesBetween m M (FV1D.nonuniformStepArray FV1D.burgers (1 / 2) dt widths u)

/-- FVNA-T (b), total variation: for `n ≥ 1`, arrays `widths`, `u` of size `n` with positive widths and `dt ≥ 0`, if
the FVN-B face condition `dt · a i ≤ min(w[i], w[i+1])` holds at every face `i`, the first-order Burgers kernel does
not increase the total variation. -/
def FirstOrderTotalVariation : Prop :=
  ∀ (n : ℕ) [NeZero n] (dt : ℝ) (widths u : Array ℝ) (hw : widths.size = n) (hu : u.size = n),
    (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) → 0 ≤ dt →
    (∀ i : Fin u.size, dt * rusanovWaveSpeed u[i] u[nextIdx i] ≤ min widths[i] widths[nextIdx i]) →
    totalVariationArray (FV1D.nonuniformStepArray FV1D.burgers (1 / 2) dt widths u) ≤ totalVariationArray u

/-! ### FVNA-T (c): MUSCL bounds and total variation over `k` steps -/

/-- FVNA-T (c), Forward Euler: for a limiter `L ≠ none`, `n ≥ 1`, arrays `widths`, `u` of size `n` with positive
widths and mesh ratio `θ_L`, `dt ≥ 0`, every entry of `u` in `[m, M]` and `8 · dt · max(|m|, |M|) ≤ w[i]` for every
`i`: after `k` steps of the MUSCL kernel, for every `k`, every entry is in `[m, M]` and the total variation is not
larger than that of `u`. -/
def MusclEulerRunStable : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dt m M : ℝ) (widths u : Array ℝ) (k : ℕ), widths.size = n → u.size = n →
    (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) → L ≠ Limiter.none → MeshRatio widths (thetaOf L) →
    0 ≤ dt → EntriesBetween m M u → (∀ (i : ℕ) (hi : i < widths.size), 8 * dt * max |m| |M| ≤ widths[i]) →
    EntriesBetween m M (run (nuLimiterEulerStepArray L dt widths) k u) ∧
      totalVariationArray (run (nuLimiterEulerStepArray L dt widths) k u) ≤ totalVariationArray u

/-- FVNA-T (c), SSPRK2: the statement of `MusclEulerRunStable` for the SSPRK2 kernel. -/
def MusclSSPRK2RunStable : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dt m M : ℝ) (widths u : Array ℝ) (k : ℕ), widths.size = n → u.size = n →
    (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) → L ≠ Limiter.none → MeshRatio widths (thetaOf L) →
    0 ≤ dt → EntriesBetween m M u → (∀ (i : ℕ) (hi : i < widths.size), 8 * dt * max |m| |M| ≤ widths[i]) →
    EntriesBetween m M (run (nuLimiterSsprk2StepArray L dt widths) k u) ∧
      totalVariationArray (run (nuLimiterSsprk2StepArray L dt widths) k u) ≤ totalVariationArray u

/-- FVNA-T (c), SSPRK3: the statement of `MusclEulerRunStable` for the SSPRK3 kernel. -/
def MusclSSPRK3RunStable : Prop :=
  ∀ (L : Limiter) (n : ℕ) [NeZero n] (dt m M : ℝ) (widths u : Array ℝ) (k : ℕ), widths.size = n → u.size = n →
    (∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) → L ≠ Limiter.none → MeshRatio widths (thetaOf L) →
    0 ≤ dt → EntriesBetween m M u → (∀ (i : ℕ) (hi : i < widths.size), 8 * dt * max |m| |M| ≤ widths[i]) →
    EntriesBetween m M (run (nuLimiterSsprk3StepArray L dt widths) k u) ∧
      totalVariationArray (run (nuLimiterSsprk3StepArray L dt widths) k u) ≤ totalVariationArray u

end CFDLean.Verification.FV1DNonuniformArrayChallenge
