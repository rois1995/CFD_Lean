import CFDLean.Discrete.Periodic.Nonuniform

/-! FVN: this milestone's MUSCL realization on a non-uniform periodic 1D mesh; not a general reconstruction interface.

The MUSCL step is one producer of face fluxes for the reconstruction-independent `update` of
`CFDLean.Discrete.Periodic.Nonuniform`. It works over any state type `S` with a limiter `lim : S → S → S`. Both
differences of cell `i` are first rescaled to the width of cell `i` (`δ` is `Mesh1D.spacing`):

```text
back i  = (w i / δ (prev i)) • (U i − U (prev i))
fwd i   = (w i / δ i)        • (U (next i) − U i)
s i     = lim (back i) (fwd i)
left i  = U i        + (1/2) • s i
right i = U (next i) − (1/2) • s (next i)
```

The face flux is `H (left i) (right i)`. Conservation (FVN-C) follows from `update_weighted_sum`. This file also
proves the MUSCL part of FVN-K and FVN-A, local affine reconstruction exactness at one fixed cell. -/
noncomputable section
namespace CFDLean.FV1D.Nonuniform

open Periodic
open scoped BigOperators

/-! ### MUSCL face states

The definitions in this section are specific to the MUSCL reconstruction of this milestone. -/
section Muscl

variable {S I : Type*} [AddCommGroup S] [Module ℝ S]

/-- Backward difference of cell `i`, rescaled by `w i / δ (prev i)`. -/
def backDiff (m : Mesh1D I) (U : I → S) (i : I) : S :=
  (m.width i / m.spacing (m.grid.prev i)) • (U i - U (m.grid.prev i))

/-- Forward difference of cell `i`, rescaled by `w i / δ i`. -/
def fwdDiff (m : Mesh1D I) (U : I → S) (i : I) : S :=
  (m.width i / m.spacing i) • (U (m.grid.next i) - U i)

/-- Limited slope of cell `i`: the limiter applied to the rescaled backward and forward differences. -/
def slope (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) : S :=
  lim (backDiff m U i) (fwdDiff m U i)

/-- Left state at face `i`, reconstructed in cell `i`. -/
def leftState (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) : S :=
  U i + (1 / 2 : ℝ) • slope m lim U i

/-- Right state at face `i`, reconstructed in cell `next i`. -/
def rightState (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) : S :=
  U (m.grid.next i) - (1 / 2 : ℝ) • slope m lim U (m.grid.next i)

/-- MUSCL step: the generic update with face flux `H (leftState i) (rightState i)`. -/
def musclStep (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (U : I → S) (i : I) : S :=
  update m dt (fun j => H (leftState m lim U j) (rightState m lim U j)) U i

/-- Componentwise limiter on `Fin n → ℝ`: the scalar limiter `φ` acts on each component separately. -/
def componentwise {n : ℕ} (φ : ℝ → ℝ → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ :=
  fun A B k => φ (A k) (B k)

/-- FVN-C (MUSCL): the width-weighted sum is conserved. An instance of `update_weighted_sum`. -/
theorem musclStep_weighted_sum [Fintype I] (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (U : I → S) :
    ∑ i, m.width i • musclStep m H lim dt U i = ∑ i, m.width i • U i :=
  update_weighted_sum m dt _ U

/-- FVN-K (MUSCL): a constant state is a fixed point for every two-point flux `H` if `lim 0 0 = 0`. -/
theorem musclStep_constant (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (C : S) (hlim : lim 0 0 = 0) :
    musclStep m H lim dt (fun _ => C) = fun _ => C := by
  funext i
  simp [musclStep, update, leftState, rightState, slope, backDiff, fwdDiff, hlim]

/-- Under the hypotheses of FVN-A, the slope of cell `i` is `w i • β`: both rescaled differences equal it. -/
private theorem slope_affine (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) (β : S)
    (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    slope m lim U i = m.width i • β := by
  have hδ : ∀ j, m.spacing j ≠ 0 := fun j =>
    (div_pos (add_pos (m.width_pos j) (m.width_pos (m.grid.next j))) two_pos).ne'
  rw [slope, backDiff, fwdDiff, hf, hb, smul_smul, smul_smul, div_mul_cancel₀ _ (hδ _),
    div_mul_cancel₀ _ (hδ _), hlim]

/-- FVN-A, local affine reconstruction exactness (left state). At one fixed cell `i`, if both neighbouring
differences are the spacing times `β`, the left state at face `i` is `U i + (w i / 2) • β`. -/
theorem leftState_affine (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) (β : S)
    (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    leftState m lim U i = U i + (m.width i / 2) • β := by
  rw [leftState, slope_affine m lim U i β hlim hf hb, smul_smul, one_div, inv_mul_eq_div]

/-- FVN-A, local affine reconstruction exactness (right state). Under the same hypotheses, the right state at
face `prev i`, reconstructed in cell `i`, is `U i - (w i / 2) • β`. -/
theorem rightState_prev_affine (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) (β : S)
    (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    rightState m lim U (m.grid.prev i) = U i - (m.width i / 2) • β := by
  rw [rightState, m.grid.next_prev, slope_affine m lim U i β hlim hf hb, smul_smul, one_div, inv_mul_eq_div]

end Muscl

end CFDLean.FV1D.Nonuniform
