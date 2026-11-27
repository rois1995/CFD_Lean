import CFDLean.Exec.LimiterKernel
import CFDLean.Exec.FV1D

/-! FVNA, the non-uniform kernels: executable array implementations of the periodic finite-volume steps on a
non-uniform 1D mesh, one width per cell (`widths : Array α`). Generic over the arithmetic `α` of
`CFDLean.Exec.Kernel`; no Mathlib.

- First order, shared by every state type: the FVA `FV1D.Model` and `FV1D.face`, with the update of cell `i` divided
  by its own width `w[i]`.
- MUSCL with a limiter, scalar (Burgers): the E0c `limiterSlope` and the B0 `rusanov` flux. Both differences of
  cell `i` are rescaled to the width of cell `i`, by `two * w[i] / (w[i-1] + w[i])` and
  `two * w[i] / (w[i] + w[i+1])`, as in FVN (`CFDLean.FV1D.Nonuniform.backDiff`, `fwdDiff`). SSPRK2 and SSPRK3 are
  the Shu-Osher combinations (`axpby`) of `CFDLean.Exec.LimiterKernel`.

Indexing follows FVN: face `i` lies between cell `i` and cell `i + 1` (periodic); its left state is reconstructed in
cell `i` and its right state in cell `i + 1`, with the slope of `i + 1`. Cell `i` takes the flux difference of faces
`i` and `i - 1` and divides it by `w[i]`.

The widths are read with the total accessor `widthAt`, which returns `0` past the end of `widths`, so a size mismatch
cannot index out of bounds. The theorems about these kernels assume `widths.size = u.size = n ≥ 1` and that every
width is positive; checking sizes and signs is the driver's job. -/
namespace CFDLean.Exec

open Scalar

/-- Total width accessor: `widths[i]` if `i < widths.size`, and `0` otherwise. Theorems assume equal sizes, so the
default is never read there. -/
def widthAt {α : Type} [Zero α] (widths : Array α) (i : Nat) : α := widths.getD i 0

/-- In range, `widthAt` is the array entry. -/
theorem widthAt_of_lt {α : Type} [Zero α] (widths : Array α) {i : Nat} (h : i < widths.size) :
    widthAt widths i = widths[i] := by
  simp [widthAt, Array.getD, h]

namespace FV1D

variable {α S : Type}

/-- One first-order Forward-Euler step on the non-uniform periodic mesh `widths`; entry `i` is
`old[i] - (dt / w[i]) • (face(old[i], old[i+1]) - face(old[i-1], old[i]))` with periodic indices. It is `stepArray`
with `dx` replaced by the width of cell `i`. Same size as `old`. -/
def nonuniformStepArray [Mul α] [Div α] [Zero α] (M : Model α S) (half dt : α) (widths : Array α)
    (old : Array S) : Array S :=
  Array.ofFn fun i : Fin old.size =>
    let L := old[(i.val + old.size - 1) % old.size]'(pred_mod_lt i)
    let R := old[(i.val + 1) % old.size]'(succ_mod_lt i)
    M.sub old[i] (M.scale (dt / widthAt widths i.val) (M.sub (face M half old[i] R) (face M half L old[i])))

@[simp] theorem size_nonuniformStepArray [Mul α] [Div α] [Zero α] (M : Model α S) (half dt : α)
    (widths : Array α) (old : Array S) :
    (nonuniformStepArray M half dt widths old).size = old.size := Array.size_ofFn

end FV1D

section Rescaled

variable {α : Type} [Scalar α]

/-- Backward difference of cell `i`, rescaled to the width of cell `i`:
`(two * w[i] / (w[i-1] + w[i])) * (u[i] - u[i-1])`, periodic indices. -/
def nuBackDiff (widths u : Array α) (i : Fin u.size) : α :=
  two * widthAt widths i.val / (widthAt widths (prevIdx i).val + widthAt widths i.val) * (u[i] - u[prevIdx i])

/-- Forward difference of cell `i`, rescaled to the width of cell `i`:
`(two * w[i] / (w[i] + w[i+1])) * (u[i+1] - u[i])`, periodic indices. -/
def nuFwdDiff (widths u : Array α) (i : Fin u.size) : α :=
  two * widthAt widths i.val / (widthAt widths i.val + widthAt widths (nextIdx i).val) * (u[nextIdx i] - u[i])

end Rescaled

section Limited

variable {α : Type} [Scalar α] [ScalarSign α]

/-- Limited slope of cell `i`: `limiterSlope L` of the rescaled backward and forward differences. -/
def nuSlopeAt (L : Limiter) (widths u : Array α) (i : Fin u.size) : α :=
  limiterSlope L (nuBackDiff widths u i) (nuFwdDiff widths u i)

/-- Left state at face `i`, reconstructed in cell `i`: `u[i] + s i / two`. -/
def nuLeftState (L : Limiter) (widths u : Array α) (i : Fin u.size) : α :=
  u[i] + nuSlopeAt L widths u i / two

/-- Right state at face `i`, reconstructed in cell `i + 1`: `u[i+1] - s (i+1) / two`. -/
def nuRightState (L : Limiter) (widths u : Array α) (i : Fin u.size) : α :=
  u[nextIdx i] - nuSlopeAt L widths u (nextIdx i) / two

/-- Rusanov flux through face `i` (between cell `i` and cell `i + 1`). -/
def nuFaceFlux (L : Limiter) (widths u : Array α) (i : Fin u.size) : α :=
  rusanov (nuLeftState L widths u i) (nuRightState L widths u i)

/-- One Forward-Euler step of the MUSCL-Rusanov scheme with limiter `L` on the non-uniform periodic mesh `widths`;
entry `i` is `u[i] - (dt / w[i]) * (F(left i, right i) - F(left (i-1), right (i-1)))` with periodic indices. Same
size as `u`. -/
def nuLimiterEulerStepArray (L : Limiter) (dt : α) (widths u : Array α) : Array α :=
  Array.ofFn fun i : Fin u.size =>
    u[i] - dt / widthAt widths i.val * (nuFaceFlux L widths u i - nuFaceFlux L widths u (prevIdx i))

/-- SSPRK2 in Shu-Osher form over the non-uniform limiter Euler step: `½ u + ½ E(E u)`. -/
def nuLimiterSsprk2StepArray (L : Limiter) (dt : α) (widths u : Array α) : Array α :=
  axpby half u half (nuLimiterEulerStepArray L dt widths (nuLimiterEulerStepArray L dt widths u))

/-- SSPRK3 in Shu-Osher form over the non-uniform limiter Euler step: `⅓ u + ⅔ E(¾ u + ¼ E(E u))`. -/
def nuLimiterSsprk3StepArray (L : Limiter) (dt : α) (widths u : Array α) : Array α :=
  axpby third u twoThirds (nuLimiterEulerStepArray L dt widths
    (axpby threeQuarters u quarter (nuLimiterEulerStepArray L dt widths (nuLimiterEulerStepArray L dt widths u))))

@[simp] theorem size_nuLimiterEulerStepArray (L : Limiter) (dt : α) (widths u : Array α) :
    (nuLimiterEulerStepArray L dt widths u).size = u.size := Array.size_ofFn

@[simp] theorem size_nuLimiterSsprk2StepArray (L : Limiter) (dt : α) (widths u : Array α) :
    (nuLimiterSsprk2StepArray L dt widths u).size = u.size := by
  simp [nuLimiterSsprk2StepArray, axpby]

@[simp] theorem size_nuLimiterSsprk3StepArray (L : Limiter) (dt : α) (widths u : Array α) :
    (nuLimiterSsprk3StepArray L dt widths u).size = u.size := by
  simp [nuLimiterSsprk3StepArray, axpby]

end Limited

end CFDLean.Exec
