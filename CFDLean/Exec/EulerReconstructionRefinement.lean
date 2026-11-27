import CFDLean.Exec.EulerReconstruction
import CFDLean.Exec.WenoRefinement
import CFDLean.Discrete.Periodic.MusclReconstruction

/-! Exact-real correspondence for cell-owned conservative Euler reconstruction and its FV update. -/
noncomputable section
namespace CFDLean.Exec.FV1D

open Periodic

/-- Exact density and pressure test, including strictness at the boundary. -/
def positiveState (γ : ℝ) (q : EulerState ℝ) : Bool :=
  decide (0 < q 0 ∧ 0 < pressure 1 2 γ q)

theorem positiveState_iff_m1 (γ : ℝ) (q : EulerState ℝ) :
    positiveState γ q = true ↔ (Euler1D.decode q).Admissible γ := by
  rw [positiveState, decide_eq_true_eq]
  simp [Euler1D.decode, Conservative.Admissible, Conservative.pressure,
    pressure, squareSum, pow_two]

/-- Left and right endpoints of an owning cell from the mathematical scalar reconstructions. -/
def realEulerPair {I : Type} (method : EulerReconstruction) (m : Mesh1D I)
    (ε : {x : ℝ // 0 < x}) (γ : ℝ) (u : I → EulerState ℝ) (i : I) : EulerState ℝ × EulerState ℝ :=
  let scalar : CFDLean.FV1D.Reconstruction m ℝ := match method with
    | .minmod => CFDLean.FV1D.Reconstruction.muscl m CFDLean.Scalar.FiniteVolume.minmod
    | .weno => CFDLean.FV1D.Reconstruction.gradedWeno m ε
  let l (k : Fin 3) := (scalar.traces (fun j => u j k) (m.grid.prev i)).2
  let r (k : Fin 3) := (scalar.traces (fun j => u j k) i).1
  selectEulerPair (positiveState γ) (u i) l r

def realEulerReconstruction {I : Type} (method : EulerReconstruction) (m : Mesh1D I)
    (ε : {x : ℝ // 0 < x}) (γ : ℝ) : CFDLean.FV1D.Reconstruction m (EulerState ℝ) where
  traces u i := ((realEulerPair method m ε γ u i).2, (realEulerPair method m ε γ u (m.grid.next i)).1)

private theorem triple_eta (f : EulerState ℝ) : triple (f 0) (f 1) (f 2) = f := by
  funext k
  fin_cases k <;> rfl

private theorem left_muscl {I : Type} (m : Mesh1D I) (v : I → ℝ) (i : I) :
    ((CFDLean.FV1D.Reconstruction.muscl m CFDLean.Scalar.FiniteVolume.minmod).traces v (m.grid.prev i)).2 =
      v i - CFDLean.FV1D.Nonuniform.slope m CFDLean.Scalar.FiniteVolume.minmod v i / 2 := by
  simp [CFDLean.FV1D.Reconstruction.muscl, CFDLean.FV1D.Nonuniform.rightState, Grid.next_prev,
    smul_eq_mul, div_eq_inv_mul]

private theorem left_weno {I : Type} (m : Mesh1D I) (v : I → ℝ) (ε : {x : ℝ // 0 < x}) (i : I) :
    ((CFDLean.FV1D.Reconstruction.gradedWeno m ε).traces v (m.grid.prev i)).2 =
      GradedWeno.edge ε.val (GradedWeno.gather m.grid.next m.grid.prev m.width i)
        (GradedWeno.gather m.grid.next m.grid.prev v i) := by
  simp [CFDLean.FV1D.Reconstruction.gradedWeno, Grid.next_prev]

/-- The production array cell reconstruction uses the mathematical left/right owners and fallback. -/
theorem eulerCell_refines (method : EulerReconstruction) (γ : ℝ) (ε : {x : ℝ // 0 < x})
    (w : Array ℝ) (u : Array (EulerState ℝ)) (hw : w.size = u.size)
    (hp : ∀ i : Fin w.size, 0 < w[i]) (i : Fin u.size) :
    let m : Mesh1D (Fin u.size) := ⟨arrayGrid u.size, fun j => widthAt w j.val,
      fun j => by rw [widthAt_of_lt _ (hw.symm ▸ j.isLt)]; exact hp ⟨j.val, hw.symm ▸ j.isLt⟩⟩
    eulerCell method ε.val (positiveState γ) w u i = realEulerPair method m ε γ (fun j => u[j]) i := by
  have norm (x y z : ℝ) : (2*x/(y+z)) = x/((y+z)/2) := by rw [div_div_eq_mul_div]; ring
  have two : (Scalar.two : ℝ) = 2 := rfl
  let comp := eulerComponent method ε.val w u i
  have hl := triple_eta (fun k => (comp k).1)
  have hr := triple_eta (fun k => (comp k).2)
  change selectEulerPair _ _ (triple _ _ _) (triple _ _ _) = _
  rw [hl, hr]
  unfold realEulerPair
  dsimp only [comp]
  have halfMul (x : ℝ) : (1/2 : ℝ)*x = x/2 := by ring
  apply congrArg₂ (selectEulerPair (positiveState γ) u[i]) <;> funext k <;> cases method
  case _ =>
    rw [left_muscl]
    simp only [eulerComponent, CFDLean.FV1D.Nonuniform.slope, CFDLean.FV1D.Nonuniform.backDiff,
      CFDLean.FV1D.Nonuniform.fwdDiff, Mesh1D.spacing, smul_eq_mul, two, norm, minmod_eq, Grid.next_prev]
    rfl
  case _ =>
    rw [left_weno]
    rfl
  case _ =>
    simp only [eulerComponent, CFDLean.FV1D.Reconstruction.muscl, CFDLean.FV1D.Nonuniform.leftState,
      CFDLean.FV1D.Nonuniform.slope, CFDLean.FV1D.Nonuniform.backDiff, CFDLean.FV1D.Nonuniform.fwdDiff,
      Mesh1D.spacing, smul_eq_mul, two, norm, minmod_eq, halfMul, Grid.next_prev]
    rfl
  case _ => rfl

/-- A full native Forward Euler update over reals is the mathematical reconstruction step. -/
theorem eulerReconstructedStep_refines (method : EulerReconstruction) (γ : ℝ)
    (ε : {x : ℝ // 0 < x}) (dt : ℝ) (w : Array ℝ) (u : Array (EulerState ℝ))
    (hw : w.size = u.size) (hp : ∀ i : Fin w.size, 0 < w[i]) (i : Fin u.size) :
    let m : Mesh1D (Fin u.size) := ⟨arrayGrid u.size, fun j => widthAt w j.val,
      fun j => by rw [widthAt_of_lt _ (hw.symm ▸ j.isLt)]; exact hp ⟨j.val, hw.symm ▸ j.isLt⟩⟩
    let model := euler 1 2 γ abs Real.sqrt max
    (reconstructedStep model (1/2) dt w u (eulerCell method ε.val (positiveState γ) w u))[i.val]?.getD 0 =
      (realEulerReconstruction method m ε γ).step (face model (1/2)) dt (fun j => u[j]) i := by
  simp only [reconstructedStep, Array.getElem?_ofFn, i.isLt, dite_eq_left, Option.getD_some,
    Vector.getElem_ofFn, Fin.getElem_fin, eulerCell_refines method γ ε w u hw hp,
    CFDLean.FV1D.Reconstruction.step, CFDLean.FV1D.Nonuniform.update, realEulerReconstruction]
  rfl

end CFDLean.Exec.FV1D
