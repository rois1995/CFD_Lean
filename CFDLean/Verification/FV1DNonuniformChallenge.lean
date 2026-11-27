import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

/-! Trusted FVN statements for the scalar claims (`specifications/FV1D-nonuniform.md`: FVN-B, FVN-R, FVN-M,
FVN-MB and the control FVN-X). This file imports only Mathlib and restates every definition it uses.

A periodic 1D mesh is given by `next : I ≃ I`, the successor of the cells (`next.symm` is the predecessor), and one
width `w i` per cell, with `0 < w i` for every cell. The face indexed by `i` points from cell `i` to cell `next i`.
`δ i = (w i + w (next i)) / 2` is the distance between the centroids of cells `i` and `next i`. A face-flux function
`h` gives the flux `h i` through face `i`. `T^[n]` is `n` applications of `T`. Sums and scalar multiples of cell
functions are pointwise. -/
noncomputable section
namespace CFDLean.Verification.FV1DNonuniformChallenge

open scoped BigOperators

/-! ### Burgers flux and slope functions -/

/-- Burgers physical flux `f(u) = u² / 2`. -/
def burgersFlux (u : ℝ) : ℝ := u ^ 2 / 2

/-- Rusanov wave speed `a(uL, uR) = max(|uL|, |uR|)`. -/
def rusanovWaveSpeed (uL uR : ℝ) : ℝ := max |uL| |uR|

/-- Rusanov (local Lax-Friedrichs) flux for Burgers: `(f(uL) + f(uR)) / 2 - a(uL, uR) / 2 · (uR - uL)`. -/
def rusanov (uL uR : ℝ) : ℝ :=
  (burgersFlux uL + burgersFlux uR) / 2 -
    rusanovWaveSpeed uL uR / 2 * (uR - uL)

/-- The unlimited slope: the central difference `(a + b) / 2`. -/
def centralSlope (a b : ℝ) : ℝ := (a + b) / 2

/-- Sign of `a`, used only for `a ≠ 0`. -/
def sgn (a : ℝ) : ℝ := if 0 < a then 1 else -1

/-- Minmod: the argument of smaller absolute value when both have the same strict sign, else zero. -/
def minmod (a b : ℝ) : ℝ :=
  if 0 < a ∧ 0 < b then min a b else if a < 0 ∧ b < 0 then max a b else 0

/-- Monotonized central (MC): `sgn(a) min(|a + b|/2, 2|a|, 2|b|)` when `ab > 0`, else zero. -/
def mc (a b : ℝ) : ℝ :=
  if 0 < a * b then sgn a * min (|a + b| / 2) (min (2 * |a|) (2 * |b|)) else 0

/-- Superbee: `sgn(a) max(min(2|a|, |b|), min(|a|, 2|b|))` when `ab > 0`, else zero. -/
def superbee (a b : ℝ) : ℝ :=
  if 0 < a * b then sgn a * max (min (2 * |a|) |b|) (min |a| (2 * |b|)) else 0

/-- Van Leer (harmonic mean): `2ab / (a + b)` when `ab > 0`, else zero. -/
def vanLeer (a b : ℝ) : ℝ :=
  if 0 < a * b then 2 * (a * b) / (a + b) else 0

/-- Van Albada: `ab(a + b) / (a² + b²)` when `ab > 0`, else zero. -/
def vanAlbada (a b : ℝ) : ℝ :=
  if 0 < a * b then a * b * (a + b) / (a ^ 2 + b ^ 2) else 0

/-- The slope `σ = φ(a, b)` has the sign of `a` and of `b`, and `|σ| ≤ θ|a|`, `|σ| ≤ θ|b|`. -/
def SlopeBounded (θ : ℝ) (φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ φ a b * a ∧ 0 ≤ φ a b * b ∧ |φ a b| ≤ θ * |a| ∧ |φ a b| ≤ θ * |b|

/-- A two-point flux `H` is monotone: nondecreasing in the left state and nonincreasing in the right state. -/
def MonotoneFlux (H : ℝ → ℝ → ℝ) : Prop :=
  (∀ a a' b, a ≤ a' → H a b ≤ H a' b) ∧ (∀ a b b', b ≤ b' → H a b' ≤ H a b)

/-- Lipschitz certificate of a two-point flux `H` on states between `m` and `M`: constant `KL` in the left state and
`KR` in the right state. -/
def LipschitzOnBounds (H : ℝ → ℝ → ℝ) (m M KL KR : ℝ) : Prop :=
  (∀ a a' b, m ≤ a → a ≤ M → m ≤ a' → a' ≤ M → m ≤ b → b ≤ M → |H a b - H a' b| ≤ KL * |a - a'|) ∧
  (∀ a b b', m ≤ a → a ≤ M → m ≤ b → b ≤ M → m ≤ b' → b' ≤ M → |H a b - H a b'| ≤ KR * |b - b'|)

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Two-stage SSP Runge-Kutta step over a one-step map `E`: `½ u + ½ E(E u)`. -/
def ssprk2 (E : V → V) (u : V) : V := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • E (E u)

/-- Three-stage SSP Runge-Kutta step over a one-step map `E`: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def ssprk3 (E : V → V) (u : V) : V :=
  (1 / 3 : ℝ) • u + (2 / 3 : ℝ) • E ((3 / 4 : ℝ) • u + (1 / 4 : ℝ) • E (E u))

end Generic

/-! ### Mesh, reconstruction and steps -/

variable {I : Type*}

/-- Total variation on the periodic grid: `Σ_i |u (next i) - u i|`. -/
def totalVariation [Fintype I] (next : I ≃ I) (u : I → ℝ) : ℝ :=
  ∑ i, |u (next i) - u i|

/-- Distance between the centroids of cells `i` and `next i`: `δ i = (w i + w (next i)) / 2`. -/
def spacing (next : I ≃ I) (w : I → ℝ) (i : I) : ℝ := (w i + w (next i)) / 2

/-- Mesh ratio `θ`: at every face `i`, `θ · max(w i, w (next i)) ≤ w i + w (next i)`. -/
def MeshRatio (next : I ≃ I) (w : I → ℝ) (θ : ℝ) : Prop :=
  ∀ i, θ * max (w i) (w (next i)) ≤ w i + w (next i)

/-- Backward difference of cell `i`, rescaled to its width: `back i = (w i / δ (prev i)) · (u i - u (prev i))`. -/
def backDiff (next : I ≃ I) (w : I → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  w i / spacing next w (next.symm i) * (u i - u (next.symm i))

/-- Forward difference of cell `i`, rescaled to its width: `fwd i = (w i / δ i) · (u (next i) - u i)`. -/
def fwdDiff (next : I ≃ I) (w : I → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  w i / spacing next w i * (u (next i) - u i)

/-- Slope of cell `i` for the slope function `φ`: `s i = φ(back i, fwd i)`. -/
def slope (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  φ (backDiff next w u i) (fwdDiff next w u i)

/-- Left state at face `i`, reconstructed in cell `i`: `u i + (1/2) · s i`. -/
def leftState (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  u i + 1 / 2 * slope φ next w u i

/-- Right state at face `i`, reconstructed in cell `next i`: `u (next i) - (1/2) · s (next i)`. -/
def rightState (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (u : I → ℝ) (i : I) : ℝ :=
  u (next i) - 1 / 2 * slope φ next w u (next i)

/-- Flux-form update for the face-flux function `h`: `u i - (dt / w i) · (h i - h (prev i))`. -/
def update (next : I ≃ I) (w : I → ℝ) (dt : ℝ) (h u : I → ℝ) (i : I) : ℝ :=
  u i - dt / w i * (h i - h (next.symm i))

/-- First-order step with the two-point flux `H`: face flux `H (u i) (u (next i))`. -/
def firstOrderStep (H : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (dt : ℝ) (u : I → ℝ) : I → ℝ :=
  update next w dt (fun j => H (u j) (u (next j))) u

/-- MUSCL Forward-Euler step with the two-point flux `H` and the slope function `φ`: face flux
`H (leftState i) (rightState i)`. -/
def musclStep (H : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (dt : ℝ) (u : I → ℝ) : I → ℝ :=
  update next w dt (fun j => H (leftState φ next w u j) (rightState φ next w u j)) u

/-- Burgers face speed at face `j`: `a j = max(|u j|, |u (next j)|)`. -/
def faceSpeed (next : I ≃ I) (u : I → ℝ) (j : I) : ℝ := rusanovWaveSpeed (u j) (u (next j))

/-! ### FVN-B: first-order Burgers -/

/-- FVN-B (a): if `dt ≥ 0`, `m ≤ u j ≤ M` for all `j` and `dt · (a (prev i) + a i) ≤ w i` at every cell, every output
of the first-order Burgers step is in `[m, M]`. -/
def FirstOrderBounds (I : Type*) : Prop :=
  ∀ (next : I ≃ I) (w : I → ℝ) (dt m M : ℝ) (u : I → ℝ),
    (∀ i, 0 < w i) → 0 ≤ dt → (∀ j, m ≤ u j ∧ u j ≤ M) →
    (∀ i, dt * (faceSpeed next u (next.symm i) + faceSpeed next u i) ≤ w i) →
    ∀ i, m ≤ firstOrderStep rusanov next w dt u i ∧ firstOrderStep rusanov next w dt u i ≤ M

/-- FVN-B (b): if `dt ≥ 0` and `dt · a i ≤ min(w i, w (next i))` at every face, the first-order Burgers step does not
increase the total variation. -/
def FirstOrderTotalVariation (I : Type*) [Fintype I] : Prop :=
  ∀ (next : I ≃ I) (w : I → ℝ) (dt : ℝ) (u : I → ℝ),
    (∀ i, 0 < w i) → 0 ≤ dt →
    (∀ i, dt * faceSpeed next u i ≤ min (w i) (w (next i))) →
    totalVariation next (firstOrderStep rusanov next w dt u) ≤ totalVariation next u

/-! ### FVN-R: reconstruction bounds -/

/-- FVN-R: if `φ` is `SlopeBounded θ`, the mesh ratio `θ` holds and `m ≤ u j ≤ M` for all `j`, the left and right
states of every face are in `[m, M]`. -/
def ReconstructionBounds (I : Type*) : Prop :=
  ∀ (θ : ℝ) (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (m M : ℝ) (u : I → ℝ),
    (∀ i, 0 < w i) → SlopeBounded θ φ → MeshRatio next w θ → (∀ j, m ≤ u j ∧ u j ≤ M) →
    ∀ i, (m ≤ leftState φ next w u i ∧ leftState φ next w u i ≤ M) ∧
      (m ≤ rightState φ next w u i ∧ rightState φ next w u i ≤ M)

/-! ### FVN-M: scalar MUSCL -/

/-- FVN-M (a): for a monotone two-point flux `H` with the Lipschitz certificate `KL`, `KR` on `[m, M]`, `φ`
`SlopeBounded θ`, mesh ratio `θ`, `dt ≥ 0` and `m ≤ u j ≤ M` for all `j`, if at every cell
`dt · ((KL + KR) / w i + θ · (KR / (w i + w (next i)) + KL / (w (prev i) + w i))) ≤ 1`, every output of the MUSCL
step is in `[m, M]`. -/
def MusclBounds (I : Type*) : Prop :=
  ∀ (H : ℝ → ℝ → ℝ) (KL KR θ : ℝ) (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (dt m M : ℝ) (u : I → ℝ),
    (∀ i, 0 < w i) → MonotoneFlux H → LipschitzOnBounds H m M KL KR → SlopeBounded θ φ → MeshRatio next w θ →
    0 ≤ dt → (∀ j, m ≤ u j ∧ u j ≤ M) →
    (∀ i, dt * ((KL + KR) / w i + θ * (KR / (w i + w (next i)) + KL / (w (next.symm i) + w i))) ≤ 1) →
    ∀ i, m ≤ musclStep H φ next w dt u i ∧ musclStep H φ next w dt u i ≤ M

/-- FVN-M (b): under the hypotheses of FVN-M (a) with the face condition
`dt · (KR / w i + KL / w (next i) + θ · (KL + KR) / (w i + w (next i))) ≤ 1` at every face, the MUSCL step does not
increase the total variation. -/
def MusclTotalVariation (I : Type*) [Fintype I] : Prop :=
  ∀ (H : ℝ → ℝ → ℝ) (KL KR θ : ℝ) (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (dt m M : ℝ) (u : I → ℝ),
    (∀ i, 0 < w i) → MonotoneFlux H → LipschitzOnBounds H m M KL KR → SlopeBounded θ φ → MeshRatio next w θ →
    0 ≤ dt → (∀ j, m ≤ u j ∧ u j ≤ M) →
    (∀ i, dt * (KR / w i + KL / w (next i) + θ * (KL + KR) / (w i + w (next i))) ≤ 1) →
    totalVariation next (musclStep H φ next w dt u) ≤ totalVariation next u

/-! ### FVN-MB: Burgers MUSCL -/

/-- A time-stepping map `T` (given the slope function, the mesh and `dt`) is multi-step stable when: for every
`θ`-bounded slope function, every mesh with positive widths and mesh ratio `θ`, `dt ≥ 0`, bounds `m ≤ u j ≤ M` of the
initial state and `8 · dt · max(|m|, |M|) ≤ w i` at every cell, the state after `n` steps has the same bounds and no
larger total variation, for every `n`. -/
def MultiStepStable (I : Type*) [Fintype I]
    (T : (ℝ → ℝ → ℝ) → (I ≃ I) → (I → ℝ) → ℝ → (I → ℝ) → I → ℝ) : Prop :=
  ∀ (θ : ℝ) (φ : ℝ → ℝ → ℝ) (next : I ≃ I) (w : I → ℝ) (dt : ℝ) (u : I → ℝ) (m M : ℝ) (n : ℕ),
    (∀ i, 0 < w i) → SlopeBounded θ φ → MeshRatio next w θ → 0 ≤ dt →
    (∀ i, 8 * dt * max |m| |M| ≤ w i) → (∀ j, m ≤ u j ∧ u j ≤ M) →
    (∀ j, m ≤ (T φ next w dt)^[n] u j ∧ (T φ next w dt)^[n] u j ≤ M) ∧
      totalVariation next ((T φ next w dt)^[n] u) ≤ totalVariation next u

/-- FVN-MB: Burgers MUSCL-Rusanov with Forward Euler. -/
def MusclEulerMultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I (fun φ next w dt => musclStep rusanov φ next w dt)

/-- FVN-MB: Burgers MUSCL-Rusanov with SSPRK2. -/
def MusclSSPRK2MultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I (fun φ next w dt => ssprk2 (musclStep rusanov φ next w dt))

/-- FVN-MB: Burgers MUSCL-Rusanov with SSPRK3. -/
def MusclSSPRK3MultiStep (I : Type*) [Fintype I] : Prop :=
  MultiStepStable I (fun φ next w dt => ssprk3 (musclStep rusanov φ next w dt))

/-! ### FVN-X: the mesh ratio is needed -/

/-- The FVN-X widths `(1, 3, 1, 1)` on four periodic cells. -/
def widthData : ZMod 4 → ℝ := ![1, 3, 1, 1]

/-- The FVN-X state `(0, 1, 6/5, 0)`. -/
def stateData : ZMod 4 → ℝ := ![0, 1, 6 / 5, 0]

/-- FVN-X (under FVN-R): on four periodic cells (successor `i ↦ i + 1`) with widths `(1, 3, 1, 1)`, the state
`(0, 1, 6/5, 0)` lies in `[0, 6/5]`, the mesh ratio holds for `θ = 5/4` and fails for `θ = 2`, and at cell 1
`back = 3/2` and `fwd = 3/10`. The left state at face 1 is `23/20` (minmod) and `61/52` (van Albada), inside
`[0, 6/5]`, and `5/4` (van Leer), `13/10` (MC, superbee) and `29/20` (unlimited), above `6/5`. -/
def MeshRatioOvershoot : Prop :=
  (∀ j, 0 ≤ stateData j ∧ stateData j ≤ 6 / 5) ∧
    MeshRatio (Equiv.addRight (1 : ZMod 4)) widthData (5 / 4) ∧
    ¬ MeshRatio (Equiv.addRight (1 : ZMod 4)) widthData 2 ∧
    backDiff (Equiv.addRight (1 : ZMod 4)) widthData stateData 1 = 3 / 2 ∧
    fwdDiff (Equiv.addRight (1 : ZMod 4)) widthData stateData 1 = 3 / 10 ∧
    leftState minmod (Equiv.addRight (1 : ZMod 4)) widthData stateData 1 = 23 / 20 ∧
    leftState vanAlbada (Equiv.addRight (1 : ZMod 4)) widthData stateData 1 = 61 / 52 ∧
    leftState vanLeer (Equiv.addRight (1 : ZMod 4)) widthData stateData 1 = 5 / 4 ∧
    leftState mc (Equiv.addRight (1 : ZMod 4)) widthData stateData 1 = 13 / 10 ∧
    leftState superbee (Equiv.addRight (1 : ZMod 4)) widthData stateData 1 = 13 / 10 ∧
    leftState centralSlope (Equiv.addRight (1 : ZMod 4)) widthData stateData 1 = 29 / 20

end CFDLean.Verification.FV1DNonuniformChallenge
