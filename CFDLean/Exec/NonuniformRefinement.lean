import CFDLean.Exec.NonuniformKernel
import CFDLean.Exec.FV1DRefinement
import CFDLean.Exec.LimiterRefinement
import CFDLean.Schemes.Burgers.Nonuniform
import CFDLean.Schemes.Euler.Nonuniform

/-! FVNA-F, FVNA-M, FVNA-U: the non-uniform array kernels of `CFDLean.Exec.NonuniformKernel`, instantiated at `ℝ`,
compute exactly the FVN steps of `CFDLean.FV1D.Nonuniform`, `CFDLean.Burgers.Nonuniform` and
`CFDLean.Euler1D.nonuniformStep`.

Array entry `i` represents periodic cell `(i : ZMod n)`: a field `u : ZMod n → S` is stored as `samples u`, as in
the FVA refinement (`CFDLean.Exec.FV1D.samples`, `samples_entries`). `meshOf widths` is the FVN `Mesh1D` on
`zmodGrid n` whose cell `j` has width `widths[j.val]`; it needs `widths.size = n` and positive entries.

- Supporting: `nonuniformStepArray_compatible`, the first-order stencil for a compatible model
  `⟨(· + ·), (· - ·), (· • ·), F, a⟩` over a real module.
- FVNA-F: `burgers_nonuniform_refines`, `euler_nonuniform_refines`.
- Alignment (face and width, seam included): `nuFace_alignment`, from `nextIdx_prevIdx` and `prevIdx_nextIdx`.
- FVNA-M: `nuLimiterEulerStepArray_refines`, `nuLimiterSsprk2StepArray_refines`, `nuLimiterSsprk3StepArray_refines`.
- FVNA-U: `nonuniformStepArray_uniform` (generic, supporting) with the concrete `burgers_nonuniformStepArray_uniform`
  and `euler_nonuniformStepArray_uniform`, and `nuLimiterEulerStepArray_uniform`, `nuLimiterSsprk2StepArray_uniform`,
  `nuLimiterSsprk3StepArray_uniform`. On uniform widths both rescaling factors are `2 * dx / (dx + dx) = 1`; the
  proofs rewrite the slope arguments and never split on the limiter. -/
noncomputable section
namespace CFDLean.Exec

open Periodic
open _root_.CFDLean.Exec.FV1D (samples)

private theorem real_two : (Scalar.two : ℝ) = 2 := rfl

/-! ### Periodic indices -/

/-- The right neighbour of the left neighbour is the cell itself, for every size (also `n = 1`). -/
theorem nextIdx_prevIdx {m : ℕ} (i : Fin m) : nextIdx (prevIdx i) = i := by
  have hi := i.isLt
  ext
  simp only [nextIdx, prevIdx]
  rw [Nat.mod_add_mod, show i.val + m - 1 + 1 = i.val + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

/-- The left neighbour of the right neighbour is the cell itself, for every size (also `n = 1`). -/
theorem prevIdx_nextIdx {m : ℕ} (i : Fin m) : prevIdx (nextIdx i) = i := by
  have hi := i.isLt
  ext
  simp only [nextIdx, prevIdx]
  rw [Nat.add_sub_assoc (by omega : 1 ≤ m), Nat.mod_add_mod, show i.val + 1 + (m - 1) = i.val + m by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hi]

section Residues

variable {n : ℕ} [NeZero n]

/-- `nextIdx` is `next` of `zmodGrid n` on the residues. -/
theorem natCast_nextIdx {m : ℕ} (hm : m = n) (k : Fin m) :
    (((nextIdx k).val : ℕ) : ZMod n) = (zmodGrid n).next (k.val : ZMod n) := by
  subst hm
  simp [nextIdx, zmodGrid, ZMod.natCast_mod]

/-- `prevIdx` is `prev` of `zmodGrid n` on the residues. -/
theorem natCast_prevIdx {m : ℕ} (hm : m = n) (k : Fin m) :
    (((prevIdx k).val : ℕ) : ZMod n) = (zmodGrid n).prev (k.val : ZMod n) := by
  subst hm
  have h : 1 ≤ k.val + m := by have := NeZero.pos m; omega
  have hp : (zmodGrid m).prev (k.val : ZMod m) = (k.val : ZMod m) - 1 := by
    simp [zmodGrid, Grid.prev, sub_eq_add_neg]
  rw [hp]
  simp [prevIdx, ZMod.natCast_mod, Nat.cast_sub h]

/-! ### The mesh of a width array -/

/-- The FVN mesh on `zmodGrid n` whose cell `j` has width `widths[j.val]` (read with `widthAt`). -/
def meshOf (widths : Array ℝ) (hw : widths.size = n) (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) :
    Mesh1D (ZMod n) where
  grid := zmodGrid n
  width j := widthAt widths j.val
  width_pos j := by
    have h : j.val < widths.size := hw ▸ ZMod.val_lt j
    rw [widthAt_of_lt widths h]
    exact hpos _ h

section Mesh

variable (widths : Array ℝ) (hw : widths.size = n) (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i])

@[simp] theorem meshOf_grid : (meshOf widths hw hpos).grid = zmodGrid n := rfl

/-- Cell `j` of `meshOf widths` has width `widths[j.val]`. -/
theorem meshOf_width (j : ZMod n) : (meshOf widths hw hpos).width j = widths[j.val]'(hw ▸ ZMod.val_lt j) :=
  widthAt_of_lt widths _

/-- The width the kernels read for array entry `k < n` is the width of cell `(k : ZMod n)`. -/
theorem widthAt_eq_meshOf (k : ℕ) (hk : k < n) : widthAt widths k = (meshOf widths hw hpos).width (k : ZMod n) := by
  change widthAt widths k = widthAt widths (k : ZMod n).val
  rw [ZMod.val_cast_of_lt hk]

end Mesh

/-! ### Stored fields -/

namespace FV1D

section Samples

variable {S : Type}

omit [NeZero n] in
@[simp] theorem samples_size (u : ZMod n → S) : (samples u).size = n := by
  simp [samples]

omit [NeZero n] in
theorem samples_getElem (u : ZMod n → S) (k : ℕ) (hk : k < (samples u).size) : (samples u)[k] = u (k : ZMod n) := by
  simp [samples]

omit [NeZero n] in
/-- The array linear combination of two stored real fields stores the pointwise linear combination. -/
theorem axpby_samples (a b : ℝ) (u v : ZMod n → ℝ) : axpby a (samples u) b (samples v) = samples (a • u + b • v) := by
  apply Array.ext (by simp [axpby])
  intro j _ _
  simp only [axpby, Array.getElem_zipWith, samples_getElem, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end Samples

end FV1D

open _root_.CFDLean.Exec.FV1D (samples_size samples_getElem axpby_samples)

/-! ### First order (FVNA-F) -/

/-- The first-order kernel on a stored field, written with the periodic residues. -/
private theorem nu_stencil {S : Type} (M : FV1D.Model ℝ S) (dt : ℝ) (widths : Array ℝ) (u : ZMod n → S) :
    FV1D.nonuniformStepArray M (1/2) dt widths (samples u) = samples (fun i =>
      M.sub (u i) (M.scale (dt / widthAt widths i.val) (M.sub (FV1D.face M (1/2) (u i) (u (i+1)))
        (FV1D.face M (1/2) (u (i-1)) (u i))))) := by
  apply Array.ext (by simp)
  intro j hj _
  have h : 1 ≤ j+n := by have := NeZero.pos n; omega
  have hjn : j < n := by simpa using hj
  simp [FV1D.nonuniformStepArray, samples, ZMod.natCast_mod, Nat.cast_sub h, Nat.mod_eq_of_lt hjn]

private theorem burgers_model :
    FV1D.burgers (α := ℝ) = ⟨(·+·), (·-·), (· • ·), Burgers.physicalFlux, Burgers.Rusanov.waveSpeed⟩ := by
  unfold FV1D.burgers
  congr 1
  funext x
  simp [Scalar.burgersFlux, Burgers.physicalFlux, pow_two, real_two]

private theorem euler_model (γ : ℝ) :
    FV1D.euler 1 2 γ abs Real.sqrt max = ⟨(·+·), (·-·), (· • ·), Euler1D.flux γ, Euler1D.speed γ⟩ := by
  unfold FV1D.euler
  congr 1
  · funext x j
    fin_cases j <;> simp [FV1D.pressure, Euler1D.flux, Euler1D.decode, Euler1D.encode,
      physicalFlux, Conservative.pressure, squareSum, dot, pow_two, Matrix.cons_val_two]
  · funext x y
    simp [FV1D.pressure, Euler1D.speed, Euler1D.endpointSpeed, Euler1D.decode, Conservative.pressure, squareSum,
      pow_two]

/-- Supporting stencil lemma: for a compatible model over a real module, the first-order array kernel stores the FVN
first-order step with the FV1D Rusanov face on `meshOf widths`. -/
theorem nonuniformStepArray_compatible {S : Type} [AddCommGroup S] [Module ℝ S] (F : S → S) (a : S → S → ℝ)
    (dt : ℝ) (widths : Array ℝ) (hw : widths.size = n) (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i])
    (u : ZMod n → S) :
    FV1D.nonuniformStepArray ⟨(·+·), (·-·), (· • ·), F, a⟩ (1/2) dt widths (samples u) =
      samples (_root_.CFDLean.FV1D.Nonuniform.firstOrderStep (meshOf widths hw hpos)
        (_root_.CFDLean.FV1D.face F a) dt u) := by
  rw [nu_stencil]
  apply congrArg samples
  funext i
  have hp : (zmodGrid n).prev i = i - 1 := by simp [zmodGrid, Grid.prev, sub_eq_add_neg]
  simp only [_root_.CFDLean.FV1D.Nonuniform.firstOrderStep, _root_.CFDLean.FV1D.Nonuniform.update, meshOf_grid,
    hp]
  simp [FV1D.face, _root_.CFDLean.FV1D.face, zmodGrid, div_eq_mul_inv, meshOf]

/-- FVNA-F (Burgers). The first-order array kernel with the real Burgers model stores the FVN first-order Burgers
step on `meshOf widths`, in every cell. -/
theorem burgers_nonuniform_refines (dt : ℝ) (widths : Array ℝ) (hw : widths.size = n)
    (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) (u : ZMod n → ℝ) (old : Array ℝ)
    (hu : old = samples u) :
    FV1D.nonuniformStepArray FV1D.burgers (1/2) dt widths old =
      samples (Burgers.Nonuniform.firstOrderStep (meshOf widths hw hpos) dt u) := by
  rw [hu, burgers_model, nonuniformStepArray_compatible _ _ _ _ hw hpos]
  rfl

/-- FVNA-F (Euler). For `γ > 1` and an array storing an admissible field, the first-order array kernel with the real
Euler model stores the FVN first-order Euler step on `meshOf widths`, in every cell and all three components. -/
theorem euler_nonuniform_refines (γ dt : ℝ) (_hg : 1 < γ) (widths : Array ℝ) (hw : widths.size = n)
    (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) (U : ZMod n → Conservative 1)
    (_hadm : ∀ j, (U j).Admissible γ) (old : Array (FV1D.EulerState ℝ))
    (hu : old = samples (fun j => Euler1D.encode (U j))) :
    FV1D.nonuniformStepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1/2) dt widths old =
      samples (fun j => Euler1D.encode (Euler1D.nonuniformStep γ (meshOf widths hw hpos) dt U j)) := by
  rw [hu, euler_model, nonuniformStepArray_compatible _ _ _ _ hw hpos]
  simp [Euler1D.nonuniformStep]

/-! ### MUSCL reconstruction and the alignment lemma -/

section Muscl

variable (L : Limiter) (widths : Array ℝ) (hw : widths.size = n)
  (hpos : ∀ (i : ℕ) (hi : i < widths.size), 0 < widths[i]) (u : ZMod n → ℝ)

omit [NeZero n] in
private theorem idx_lt (k : Fin (samples u).size) : k.val < n := by
  simpa using k.isLt

/-- Rescaled backward difference of a stored field: the FVN `backDiff` on `meshOf widths`. -/
private theorem nuBackDiff_samples (k : Fin (samples u).size) :
    nuBackDiff widths (samples u) k =
      _root_.CFDLean.FV1D.Nonuniform.backDiff (meshOf widths hw hpos) u (k.val : ZMod n) := by
  rw [nuBackDiff, widthAt_eq_meshOf widths hw hpos _ (idx_lt u k),
    widthAt_eq_meshOf widths hw hpos _ (idx_lt u (prevIdx k)), natCast_prevIdx (samples_size u)]
  simp only [_root_.CFDLean.FV1D.Nonuniform.backDiff, Mesh1D.spacing, Fin.getElem_fin, samples_getElem,
    natCast_prevIdx (samples_size u), meshOf_grid, Grid.next_prev, smul_eq_mul, real_two, div_div_eq_mul_div]
  ring

/-- Rescaled forward difference of a stored field: the FVN `fwdDiff` on `meshOf widths`. -/
private theorem nuFwdDiff_samples (k : Fin (samples u).size) :
    nuFwdDiff widths (samples u) k =
      _root_.CFDLean.FV1D.Nonuniform.fwdDiff (meshOf widths hw hpos) u (k.val : ZMod n) := by
  rw [nuFwdDiff, widthAt_eq_meshOf widths hw hpos _ (idx_lt u k),
    widthAt_eq_meshOf widths hw hpos _ (idx_lt u (nextIdx k)), natCast_nextIdx (samples_size u)]
  simp only [_root_.CFDLean.FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, Fin.getElem_fin, samples_getElem,
    natCast_nextIdx (samples_size u), meshOf_grid, smul_eq_mul, real_two, div_div_eq_mul_div]
  ring

private theorem nuSlopeAt_samples (k : Fin (samples u).size) :
    nuSlopeAt L widths (samples u) k =
      _root_.CFDLean.FV1D.Nonuniform.slope (meshOf widths hw hpos) L.slopeFn u (k.val : ZMod n) := by
  rw [nuSlopeAt, nuBackDiff_samples widths hw hpos, nuFwdDiff_samples widths hw hpos, limiterSlope_eq]
  rfl

private theorem nuLeftState_samples (k : Fin (samples u).size) :
    nuLeftState L widths (samples u) k =
      _root_.CFDLean.FV1D.Nonuniform.leftState (meshOf widths hw hpos) L.slopeFn u (k.val : ZMod n) := by
  rw [nuLeftState, nuSlopeAt_samples L widths hw hpos, _root_.CFDLean.FV1D.Nonuniform.leftState, Fin.getElem_fin,
    samples_getElem, smul_eq_mul, real_two]
  ring

private theorem nuRightState_samples (k : Fin (samples u).size) :
    nuRightState L widths (samples u) k =
      _root_.CFDLean.FV1D.Nonuniform.rightState (meshOf widths hw hpos) L.slopeFn u (k.val : ZMod n) := by
  rw [nuRightState, nuSlopeAt_samples L widths hw hpos, _root_.CFDLean.FV1D.Nonuniform.rightState,
    Fin.getElem_fin, samples_getElem, natCast_nextIdx (samples_size u), smul_eq_mul, real_two, meshOf_grid]
  ring

/-- Face and width alignment, seam included. For every face `j` of the stored field (also `j = n - 1`, whose right
cell is `0`, and `n = 1`, where every neighbour is the cell itself):
1. the backward difference of the right cell `j + 1` is rescaled with the pair `w[j]`, `w[j+1]` of face `j`, that is
   with the FVN spacing of face `j` (from `prevIdx_nextIdx`);
2. the right state at face `j` is the FVN right state at face `j`;
3. the right state at face `j - 1`, which the kernel reads at `nextIdx (prevIdx j)`, is the FVN right state at face
   `prev j` (from `nextIdx_prevIdx`).

The lemma states the alignment on its own, for review: the FVNA-M proofs use the per-face lemmas
(`nuRightState_samples` with `natCast_prevIdx`) and do not cite it. -/
theorem nuFace_alignment (j : Fin (samples u).size) :
    nuBackDiff widths (samples u) (nextIdx j) =
        ((meshOf widths hw hpos).width ((zmodGrid n).next (j.val : ZMod n)) /
          (meshOf widths hw hpos).spacing (j.val : ZMod n)) •
          (u ((zmodGrid n).next (j.val : ZMod n)) - u (j.val : ZMod n)) ∧
      nuRightState L widths (samples u) j =
        _root_.CFDLean.FV1D.Nonuniform.rightState (meshOf widths hw hpos) L.slopeFn u (j.val : ZMod n) ∧
      nuRightState L widths (samples u) (prevIdx j) =
        _root_.CFDLean.FV1D.Nonuniform.rightState (meshOf widths hw hpos) L.slopeFn u
          ((zmodGrid n).prev (j.val : ZMod n)) := by
  refine ⟨?_, nuRightState_samples L widths hw hpos u j, ?_⟩
  · simp only [nuBackDiff, prevIdx_nextIdx, Fin.getElem_fin, samples_getElem]
    rw [widthAt_eq_meshOf widths hw hpos _ (idx_lt u j),
      widthAt_eq_meshOf widths hw hpos _ (idx_lt u (nextIdx j)), natCast_nextIdx (samples_size u)]
    simp only [Mesh1D.spacing, meshOf_grid, smul_eq_mul, real_two, div_div_eq_mul_div]
    ring
  · simp only [nuRightState, nextIdx_prevIdx]
    rw [nuSlopeAt_samples L widths hw hpos,
      _root_.CFDLean.FV1D.Nonuniform.rightState, meshOf_grid, Grid.next_prev, Fin.getElem_fin, samples_getElem,
      smul_eq_mul, real_two]
    ring

/-- FVNA-M (Forward Euler). For every limiter `L`, the non-uniform MUSCL array kernel stores the FVN Burgers MUSCL
step on `meshOf widths` with the slope function of `L`, in every cell. -/
theorem nuLimiterEulerStepArray_refines (dt : ℝ) (old : Array ℝ) (hu : old = samples u) :
    nuLimiterEulerStepArray L dt widths old =
      samples (Burgers.Nonuniform.musclStep (meshOf widths hw hpos) dt L.slopeFn u) := by
  subst hu
  apply Array.ext (by simp)
  intro j hj _
  have hjn : j < n := by simpa using hj
  have hface : ∀ k : Fin (samples u).size, nuFaceFlux L widths (samples u) k =
      Burgers.Nonuniform.face (_root_.CFDLean.FV1D.Nonuniform.leftState (meshOf widths hw hpos) L.slopeFn u k.val)
        (_root_.CFDLean.FV1D.Nonuniform.rightState (meshOf widths hw hpos) L.slopeFn u k.val) := fun k => by
    rw [nuFaceFlux, nuLeftState_samples L widths hw hpos, nuRightState_samples L widths hw hpos, rusanov_eq,
      Burgers.Nonuniform.face, Burgers.fv1d_face_eq]
  simp only [nuLimiterEulerStepArray, Array.getElem_ofFn]
  rw [hface, hface, natCast_prevIdx (samples_size u),
    widthAt_eq_meshOf widths hw hpos _ hjn, Fin.getElem_fin, samples_getElem, samples_getElem]
  rfl

/-- FVNA-M (SSPRK2). For every limiter `L`, the non-uniform MUSCL SSPRK2 array kernel stores the FVN Burgers MUSCL
SSPRK2 step on `meshOf widths`, in every cell. -/
theorem nuLimiterSsprk2StepArray_refines (dt : ℝ) (old : Array ℝ) (hu : old = samples u) :
    nuLimiterSsprk2StepArray L dt widths old =
      samples (Burgers.Nonuniform.musclSsprk2Step (meshOf widths hw hpos) dt L.slopeFn u) := by
  rw [nuLimiterSsprk2StepArray, nuLimiterEulerStepArray_refines L widths hw hpos u dt old hu,
    nuLimiterEulerStepArray_refines L widths hw hpos _ dt _ rfl, hu, axpby_samples]
  rfl

/-- FVNA-M (SSPRK3). For every limiter `L`, the non-uniform MUSCL SSPRK3 array kernel stores the FVN Burgers MUSCL
SSPRK3 step on `meshOf widths`, in every cell. -/
theorem nuLimiterSsprk3StepArray_refines (dt : ℝ) (old : Array ℝ) (hu : old = samples u) :
    nuLimiterSsprk3StepArray L dt widths old =
      samples (Burgers.Nonuniform.musclSsprk3Step (meshOf widths hw hpos) dt L.slopeFn u) := by
  rw [nuLimiterSsprk3StepArray, nuLimiterEulerStepArray_refines L widths hw hpos u dt old hu,
    nuLimiterEulerStepArray_refines L widths hw hpos _ dt _ rfl, hu, axpby_samples,
    nuLimiterEulerStepArray_refines L widths hw hpos _ dt _ rfl, axpby_samples]
  rfl

end Muscl

/-! ### Uniform widths (FVNA-U) -/

section Uniform

variable (dx dt : ℝ) (widths : Array ℝ)

/-- FVNA-U (first order). If every width equals `dx > 0`, the first-order non-uniform kernel is the FVA `stepArray`
with `dx`, for every real model. -/
theorem nonuniformStepArray_uniform {S : Type} (M : FV1D.Model ℝ S) (half : ℝ) (_hdx : 0 < dx) (old : Array S)
    (hs : widths.size = old.size) (hw : ∀ (i : ℕ) (hi : i < widths.size), widths[i] = dx) :
    FV1D.nonuniformStepArray M half dt widths old = FV1D.stepArray M half dx dt old := by
  apply Array.ext (by simp [FV1D.stepArray])
  intro j hj _
  have hjw : j < widths.size := by rw [hs]; simpa using hj
  simp only [FV1D.nonuniformStepArray, FV1D.stepArray, Array.getElem_ofFn]
  rw [widthAt_of_lt widths hjw, hw j hjw]

/-- FVNA-U (first order, Burgers). If every width equals `dx > 0`, the first-order non-uniform kernel with the real
Burgers model is the FVA `stepArray` with `dx`. -/
theorem burgers_nonuniformStepArray_uniform (hdx : 0 < dx) (old : Array ℝ) (hs : widths.size = old.size)
    (hw : ∀ (i : ℕ) (hi : i < widths.size), widths[i] = dx) :
    FV1D.nonuniformStepArray FV1D.burgers (1/2) dt widths old = FV1D.stepArray FV1D.burgers (1/2) dx dt old :=
  nonuniformStepArray_uniform dx dt widths FV1D.burgers (1/2) hdx old hs hw

/-- FVNA-U (first order, Euler). If every width equals `dx > 0`, the first-order non-uniform kernel with the real
Euler model of `euler_nonuniform_refines` is the FVA `stepArray` with `dx`, for every `γ`. -/
theorem euler_nonuniformStepArray_uniform (γ : ℝ) (hdx : 0 < dx) (old : Array (FV1D.EulerState ℝ))
    (hs : widths.size = old.size) (hw : ∀ (i : ℕ) (hi : i < widths.size), widths[i] = dx) :
    FV1D.nonuniformStepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1/2) dt widths old =
      FV1D.stepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1/2) dx dt old :=
  nonuniformStepArray_uniform dx dt widths _ (1/2) hdx old hs hw

/-- FVNA-U (MUSCL, Forward Euler). If every width equals `dx > 0`, the non-uniform MUSCL kernel is the E0c
`limiterEulerStepArray` with `dx`, for every limiter. -/
theorem nuLimiterEulerStepArray_uniform (L : Limiter) (hdx : 0 < dx) (u : Array ℝ) (hs : widths.size = u.size)
    (hw : ∀ (i : ℕ) (hi : i < widths.size), widths[i] = dx) :
    nuLimiterEulerStepArray L dt widths u = limiterEulerStepArray L dx dt u := by
  have hwk : ∀ k : Fin u.size, widthAt widths k.val = dx := fun k => by
    have hk : k.val < widths.size := by rw [hs]; exact k.isLt
    rw [widthAt_of_lt widths hk, hw _ hk]
  have hfac : Scalar.two * dx / (dx + dx) = 1 := by
    rw [real_two, ← two_mul, div_self (mul_ne_zero two_ne_zero hdx.ne')]
  have hslope : ∀ k : Fin u.size, nuSlopeAt L widths u k = limSlopeAt L u k := fun k => by
    simp only [nuSlopeAt, nuBackDiff, nuFwdDiff, limSlopeAt, hwk, hfac, one_mul]
  apply Array.ext (by simp [limiterEulerStepArray])
  intro j _ _
  simp only [nuLimiterEulerStepArray, limiterEulerStepArray, Array.getElem_ofFn, nuFaceFlux, nuLeftState,
    nuRightState, limFacePlus, limFaceMinus, nextIdx_prevIdx, hslope, hwk]
  ring

/-- FVNA-U (MUSCL, SSPRK2). If every width equals `dx > 0`, the non-uniform MUSCL SSPRK2 kernel is the E0c
`limiterSsprk2StepArray` with `dx`, for every limiter. -/
theorem nuLimiterSsprk2StepArray_uniform (L : Limiter) (hdx : 0 < dx) (u : Array ℝ) (hs : widths.size = u.size)
    (hw : ∀ (i : ℕ) (hi : i < widths.size), widths[i] = dx) :
    nuLimiterSsprk2StepArray L dt widths u = limiterSsprk2StepArray L dx dt u := by
  have h1 : widths.size = (limiterEulerStepArray L dx dt u).size := by rw [limiterEulerStepArray_size, hs]
  rw [nuLimiterSsprk2StepArray, limiterSsprk2StepArray, nuLimiterEulerStepArray_uniform dx dt widths L hdx u hs hw,
    nuLimiterEulerStepArray_uniform dx dt widths L hdx _ h1 hw]

/-- FVNA-U (MUSCL, SSPRK3). If every width equals `dx > 0`, the non-uniform MUSCL SSPRK3 kernel is the E0c
`limiterSsprk3StepArray` with `dx`, for every limiter. -/
theorem nuLimiterSsprk3StepArray_uniform (L : Limiter) (hdx : 0 < dx) (u : Array ℝ) (hs : widths.size = u.size)
    (hw : ∀ (i : ℕ) (hi : i < widths.size), widths[i] = dx) :
    nuLimiterSsprk3StepArray L dt widths u = limiterSsprk3StepArray L dx dt u := by
  have h1 : widths.size = (limiterEulerStepArray L dx dt u).size := by rw [limiterEulerStepArray_size, hs]
  have h2 : widths.size =
      (axpby Scalar.threeQuarters u Scalar.quarter
        (limiterEulerStepArray L dx dt (limiterEulerStepArray L dx dt u))).size := by
    rw [axpby_size, limiterEulerStepArray_size, limiterEulerStepArray_size, min_self, hs]
  rw [nuLimiterSsprk3StepArray, limiterSsprk3StepArray, nuLimiterEulerStepArray_uniform dx dt widths L hdx u hs hw,
    nuLimiterEulerStepArray_uniform dx dt widths L hdx _ h1 hw,
    nuLimiterEulerStepArray_uniform dx dt widths L hdx _ h2 hw]

end Uniform

end Residues

/-! ### Checks

Every public theorem instantiated once with one cell (`n = 1`, where the seam reads the cell itself). -/

section Checks

private theorem one_cell_pos (w : ℝ) (hw : 0 < w) : ∀ (i : ℕ) (hi : i < #[w].size), 0 < #[w][i] := by
  intro i hi
  have h : i = 0 := by simpa using hi
  subst h
  simpa using hw

private theorem one_cell_eq (dx : ℝ) : ∀ (i : ℕ) (hi : i < #[dx].size), #[dx][i] = dx := by
  intro i hi
  have h : i = 0 := by simpa using hi
  subst h
  rfl

example (i : Fin 1) : nextIdx (prevIdx i) = i ∧ prevIdx (nextIdx i) = i :=
  ⟨nextIdx_prevIdx i, prevIdx_nextIdx i⟩

example (k : Fin 1) : (((nextIdx k).val : ℕ) : ZMod 1) = (zmodGrid 1).next (k.val : ZMod 1) ∧
    (((prevIdx k).val : ℕ) : ZMod 1) = (zmodGrid 1).prev (k.val : ZMod 1) :=
  ⟨natCast_nextIdx rfl k, natCast_prevIdx rfl k⟩

example (w : ℝ) (hw : 0 < w) (j : ZMod 1) :
    (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)).width j = w ∧
      widthAt #[w] 0 = (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)).width ((0 : ℕ) : ZMod 1) :=
  ⟨by rw [meshOf_width]; simp [Nat.lt_one_iff.mp (ZMod.val_lt j)],
    widthAt_eq_meshOf (n := 1) #[w] rfl (one_cell_pos w hw) 0 Nat.one_pos⟩

example (a b : ℝ) (u v : ZMod 1 → ℝ) :
    (samples u).size = 1 ∧ (samples u)[0]'(by simp) = u 0 ∧
      axpby a (samples u) b (samples v) = samples (a • u + b • v) :=
  ⟨FV1D.samples_size u, FV1D.samples_getElem u 0 (by simp), FV1D.axpby_samples a b u v⟩

example (F : ℝ → ℝ) (a : ℝ → ℝ → ℝ) (dt w : ℝ) (hw : 0 < w) (u : ZMod 1 → ℝ) :
    FV1D.nonuniformStepArray ⟨(·+·), (·-·), (· • ·), F, a⟩ (1/2) dt #[w] (samples u) =
      samples (_root_.CFDLean.FV1D.Nonuniform.firstOrderStep (meshOf (n := 1) #[w] rfl (one_cell_pos w hw))
        (_root_.CFDLean.FV1D.face F a) dt u) :=
  nonuniformStepArray_compatible F a dt #[w] rfl (one_cell_pos w hw) u

example (dt w : ℝ) (hw : 0 < w) (u : ZMod 1 → ℝ) :
    FV1D.nonuniformStepArray FV1D.burgers (1/2) dt #[w] (samples u) =
      samples (Burgers.Nonuniform.firstOrderStep (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)) dt u) :=
  burgers_nonuniform_refines dt #[w] rfl (one_cell_pos w hw) u _ rfl

example (dt w : ℝ) (hw : 0 < w) (U : ZMod 1 → Conservative 1) (hadm : ∀ j, (U j).Admissible 2) :
    FV1D.nonuniformStepArray (FV1D.euler 1 2 2 abs Real.sqrt max) (1/2) dt #[w]
        (samples (fun j => Euler1D.encode (U j))) =
      samples (fun j => Euler1D.encode
        (Euler1D.nonuniformStep 2 (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)) dt U j)) :=
  euler_nonuniform_refines 2 dt one_lt_two #[w] rfl (one_cell_pos w hw) U hadm _ rfl

example (L : Limiter) (w : ℝ) (hw : 0 < w) (u : ZMod 1 → ℝ) (j : Fin (samples u).size) :
    nuRightState L #[w] (samples u) (prevIdx j) =
      _root_.CFDLean.FV1D.Nonuniform.rightState (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)) L.slopeFn u
        ((zmodGrid 1).prev (j.val : ZMod 1)) :=
  (nuFace_alignment L #[w] rfl (one_cell_pos w hw) u j).2.2

example (L : Limiter) (dt w : ℝ) (hw : 0 < w) (u : ZMod 1 → ℝ) :
    nuLimiterEulerStepArray L dt #[w] (samples u) =
        samples (Burgers.Nonuniform.musclStep (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)) dt L.slopeFn u) ∧
      nuLimiterSsprk2StepArray L dt #[w] (samples u) =
        samples (Burgers.Nonuniform.musclSsprk2Step (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)) dt L.slopeFn u) ∧
      nuLimiterSsprk3StepArray L dt #[w] (samples u) =
        samples (Burgers.Nonuniform.musclSsprk3Step (meshOf (n := 1) #[w] rfl (one_cell_pos w hw)) dt L.slopeFn u) :=
  ⟨nuLimiterEulerStepArray_refines L #[w] rfl (one_cell_pos w hw) u dt _ rfl,
    nuLimiterSsprk2StepArray_refines L #[w] rfl (one_cell_pos w hw) u dt _ rfl,
    nuLimiterSsprk3StepArray_refines L #[w] rfl (one_cell_pos w hw) u dt _ rfl⟩

example {S : Type} (M : FV1D.Model ℝ S) (half dx dt : ℝ) (hdx : 0 < dx) (s : S) :
    FV1D.nonuniformStepArray M half dt #[dx] #[s] = FV1D.stepArray M half dx dt #[s] :=
  nonuniformStepArray_uniform dx dt #[dx] M half hdx #[s] rfl (one_cell_eq dx)

example (dx dt a γ : ℝ) (hdx : 0 < dx) (s : FV1D.EulerState ℝ) :
    FV1D.nonuniformStepArray FV1D.burgers (1/2) dt #[dx] #[a] = FV1D.stepArray FV1D.burgers (1/2) dx dt #[a] ∧
      FV1D.nonuniformStepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1/2) dt #[dx] #[s] =
        FV1D.stepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1/2) dx dt #[s] :=
  ⟨burgers_nonuniformStepArray_uniform dx dt #[dx] hdx #[a] rfl (one_cell_eq dx),
    euler_nonuniformStepArray_uniform dx dt #[dx] γ hdx #[s] rfl (one_cell_eq dx)⟩

example (L : Limiter) (dx dt a : ℝ) (hdx : 0 < dx) :
    nuLimiterEulerStepArray L dt #[dx] #[a] = limiterEulerStepArray L dx dt #[a] ∧
      nuLimiterSsprk2StepArray L dt #[dx] #[a] = limiterSsprk2StepArray L dx dt #[a] ∧
      nuLimiterSsprk3StepArray L dt #[dx] #[a] = limiterSsprk3StepArray L dx dt #[a] :=
  ⟨nuLimiterEulerStepArray_uniform dx dt #[dx] L hdx #[a] rfl (one_cell_eq dx),
    nuLimiterSsprk2StepArray_uniform dx dt #[dx] L hdx #[a] rfl (one_cell_eq dx),
    nuLimiterSsprk3StepArray_uniform dx dt #[dx] L hdx #[a] rfl (one_cell_eq dx)⟩

end Checks

end CFDLean.Exec
