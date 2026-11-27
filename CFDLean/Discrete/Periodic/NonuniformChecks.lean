import CFDLean.Discrete.Periodic.NonuniformMuscl

/-! Checks for the reconstruction-independent layer of FVN (task 1): each public theorem applied to its own
hypotheses, the one-cell grid `ZMod 1` (where `next i = prev i = i`) and the step with `dt = 0`. -/
noncomputable section
namespace CFDLean.FV1D.Nonuniform.Checks

open Periodic
open scoped BigOperators

variable {S I : Type*} [AddCommGroup S] [Module ℝ S]

example [Fintype I] (m : Mesh1D I) (dt : ℝ) (h U : I → S) :
    ∑ i, m.width i • update m dt h U i = ∑ i, m.width i • U i :=
  update_weighted_sum m dt h U

example [Fintype I] (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (U : I → S) :
    ∑ i, m.width i • firstOrderStep m H dt U i = ∑ i, m.width i • U i :=
  firstOrderStep_weighted_sum m H dt U

example (m : Mesh1D I) (H : S → S → S) (dt : ℝ) (C : S) :
    firstOrderStep m H dt (fun _ => C) = fun _ => C :=
  firstOrderStep_constant m H dt C

example (g : Grid I) (F : S → S) (a : S → S → ℝ) (dx : ℝ) (hdx : 0 < dx) (dt : ℝ) (U : I → S) (i : I) :
    firstOrderStep (Mesh1D.uniform g dx hdx) (FV1D.face F a) dt U i = FV1D.step g F a dx dt U i :=
  firstOrderStep_uniform g F a dx hdx dt U i

/-- Review focus 1: the one-cell grid needs no extra hypothesis for FVN-C. -/
example (m : Mesh1D (ZMod 1)) (H : S → S → S) (dt : ℝ) (U : ZMod 1 → S) :
    ∑ i, m.width i • firstOrderStep m H dt U i = ∑ i, m.width i • U i :=
  firstOrderStep_weighted_sum m H dt U

/-- Review focus 1: the one-cell grid needs no extra hypothesis for FVN-K. -/
example (m : Mesh1D (ZMod 1)) (H : S → S → S) (dt : ℝ) (C : S) :
    firstOrderStep m H dt (fun _ => C) = fun _ => C :=
  firstOrderStep_constant m H dt C

/-- Review focus 2: with `dt = 0` the first-order step returns its input. -/
example (m : Mesh1D I) (H : S → S → S) (U : I → S) : firstOrderStep m H 0 U = U := by
  funext i
  simp [firstOrderStep, update]

/-! Checks for the MUSCL realization of FVN (task 2): the rescaled differences and face states as frozen, each
public theorem applied to its own hypotheses, the one-cell grid and the step with `dt = 0`. -/

/-- The backward difference is rescaled by the cell's own width over the spacing of its left face. -/
example (m : Mesh1D I) (U : I → S) (i : I) :
    backDiff m U i = (m.width i / m.spacing (m.grid.prev i)) • (U i - U (m.grid.prev i)) :=
  rfl

/-- The forward difference is rescaled by the cell's own width over the spacing of its right face. -/
example (m : Mesh1D I) (U : I → S) (i : I) :
    fwdDiff m U i = (m.width i / m.spacing i) • (U (m.grid.next i) - U i) :=
  rfl

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) :
    slope m lim U i = lim (backDiff m U i) (fwdDiff m U i) :=
  rfl

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) :
    leftState m lim U i = U i + (1 / 2 : ℝ) • slope m lim U i :=
  rfl

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) :
    rightState m lim U i = U (m.grid.next i) - (1 / 2 : ℝ) • slope m lim U (m.grid.next i) :=
  rfl

/-- The MUSCL step is the generic update fed with the MUSCL face fluxes. -/
example (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (U : I → S) :
    musclStep m H lim dt U = update m dt (fun j => H (leftState m lim U j) (rightState m lim U j)) U :=
  rfl

example {n : ℕ} (φ : ℝ → ℝ → ℝ) (A B : Fin n → ℝ) (k : Fin n) :
    componentwise φ A B k = φ (A k) (B k) :=
  rfl

example [Fintype I] (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (U : I → S) :
    ∑ i, m.width i • musclStep m H lim dt U i = ∑ i, m.width i • U i :=
  musclStep_weighted_sum m H lim dt U

example (m : Mesh1D I) (H lim : S → S → S) (dt : ℝ) (C : S) (hlim : lim 0 0 = 0) :
    musclStep m H lim dt (fun _ => C) = fun _ => C :=
  musclStep_constant m H lim dt C hlim

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) (β : S) (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    leftState m lim U i = U i + (m.width i / 2) • β :=
  leftState_affine m lim U i β hlim hf hb

example (m : Mesh1D I) (lim : S → S → S) (U : I → S) (i : I) (β : S) (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    rightState m lim U (m.grid.prev i) = U i - (m.width i / 2) • β :=
  rightState_prev_affine m lim U i β hlim hf hb

/-- Review focus 1: the one-cell grid needs no extra hypothesis for the MUSCL part of FVN-C. -/
example (m : Mesh1D (ZMod 1)) (H lim : S → S → S) (dt : ℝ) (U : ZMod 1 → S) :
    ∑ i, m.width i • musclStep m H lim dt U i = ∑ i, m.width i • U i :=
  musclStep_weighted_sum m H lim dt U

/-- Review focus 1: the one-cell grid needs no extra hypothesis for the MUSCL part of FVN-K. -/
example (m : Mesh1D (ZMod 1)) (H lim : S → S → S) (dt : ℝ) (C : S) (hlim : lim 0 0 = 0) :
    musclStep m H lim dt (fun _ => C) = fun _ => C :=
  musclStep_constant m H lim dt C hlim

/-- Review focus 1: FVN-A on the one-cell grid, where both differences vanish and `β` is forced to `0`. -/
example (m : Mesh1D (ZMod 1)) (lim : S → S → S) (U : ZMod 1 → S) (i : ZMod 1) (β : S)
    (hlim : ∀ d, lim d d = d)
    (hf : U (m.grid.next i) - U i = m.spacing i • β)
    (hb : U i - U (m.grid.prev i) = m.spacing (m.grid.prev i) • β) :
    leftState m lim U i = U i + (m.width i / 2) • β :=
  leftState_affine m lim U i β hlim hf hb

/-- Review focus 2: with `dt = 0` the MUSCL step returns its input. -/
example (m : Mesh1D I) (H lim : S → S → S) (U : I → S) : musclStep m H lim 0 U = U := by
  funext i
  simp [musclStep, update]

end CFDLean.FV1D.Nonuniform.Checks
