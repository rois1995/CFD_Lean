import CFDLean.Exec.FV1D
import CFDLean.Exec.Refinement
import CFDLean.Schemes.Burgers.FV1D
import CFDLean.Schemes.Euler.FV1D

noncomputable section
namespace CFDLean.Exec.FV1D

@[simp] theorem triple_zero {α : Type} (r m e : α) : triple r m e 0 = r := rfl
@[simp] theorem triple_one {α : Type} (r m e : α) : triple r m e 1 = m := rfl
@[simp] theorem triple_two {α : Type} (r m e : α) : triple r m e 2 = e := rfl

private theorem real_two : (Scalar.two : ℝ) = 2 := rfl

variable {S : Type} {n : ℕ} [NeZero n]

def samples (U : ZMod n → S) : Array S := Array.ofFn fun i : Fin n => U (i.val : ZMod n)

/-- Every nonempty array is represented. Its periodic field uses the canonical residue. -/
theorem samples_entries (a : Array S) (hs : a.size = n) :
    samples (fun j : ZMod n => a[j.val]'(hs ▸ j.val_lt)) = a := by
  subst n
  apply Array.ext (by simp [samples])
  intro i hi hj
  simp [samples, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

private theorem stencil (M : Model ℝ S) (dx dt : ℝ) (u : ZMod n → S) :
    stepArray M (1/2) dx dt (samples u) = samples (fun i =>
      M.sub (u i) (M.scale (dt/dx) (M.sub (face M (1/2) (u i) (u (i+1)))
        (face M (1/2) (u (i-1)) (u i))))) := by
  apply Array.ext (by simp [samples])
  intro j hj _
  have h : 1 ≤ j+n := by have := NeZero.pos n; omega
  simp [stepArray, samples, ZMod.natCast_mod, Nat.cast_sub h]

private theorem exact_step [AddCommGroup S] [Module ℝ S] (F : S → S) (a : S → S → ℝ)
    (dx dt : ℝ) (u : ZMod n → S) :
    stepArray ⟨(·+·), (·-·), (· • ·), F, a⟩ (1/2) dx dt (samples u) =
      samples (_root_.CFDLean.FV1D.step (Periodic.zmodGrid n) F a dx dt u) := by
  rw [stencil]
  apply congrArg samples
  funext i
  simp only [_root_.CFDLean.FV1D.step, Periodic.Grid.next_prev]
  have hp : (Periodic.zmodGrid n).prev i = i-1 := by
    simp [Periodic.zmodGrid, Periodic.Grid.prev, sub_eq_add_neg]
  rw [hp]
  simp [face, _root_.CFDLean.FV1D.face, Periodic.zmodGrid, div_eq_mul_inv]

private theorem burgers_model :
    burgers (α := ℝ) = ⟨(·+·), (·-·), (· • ·), Burgers.physicalFlux, Burgers.Rusanov.waveSpeed⟩ := by
  unfold burgers
  congr 1
  funext x
  simp [Scalar.burgersFlux, Burgers.physicalFlux, pow_two, real_two]

private theorem euler_model (γ : ℝ) :
    euler 1 2 γ abs Real.sqrt max = ⟨(·+·), (·-·), (· • ·), Euler1D.flux γ, Euler1D.speed γ⟩ := by
  unfold euler
  congr 1
  · funext x j
    fin_cases j <;> simp [pressure, Euler1D.flux, Euler1D.decode, Euler1D.encode,
      physicalFlux, Conservative.pressure, squareSum, dot, pow_two, Matrix.cons_val_two]
  · funext x y
    simp [pressure, Euler1D.speed, Euler1D.endpointSpeed, Euler1D.decode, Conservative.pressure, squareSum, pow_two]

/-- FVA-B. Both equalities use the real interpretation of the kernel arithmetic. -/
theorem burgers_refines (dx dt : ℝ) (hdx : 0 < dx) (hdt : 0 ≤ dt) (u : ZMod n → ℝ)
    (old : Array ℝ) (hu : old = samples u) :
    stepArray burgers (1/2) dx dt old = samples (Burgers.Schemes.RusanovForwardEuler.step dx dt u) ∧
    stepArray burgers (1/2) dx dt old = eulerStepArray dx dt old := by
  constructor
  · rw [hu, burgers_model, exact_step]
    exact congrArg samples (funext (Burgers.fv1d_step_eq dx dt hdx hdt u))
  · apply Array.ext (by simp [eulerStepArray])
    intro j hj _
    simp only [stepArray, eulerStepArray, Array.getElem_ofFn, Fin.getElem_fin, face, burgers,
      Scalar.rusanov, real_two]
    ring

/-- FVA-E. Equality of the three stored coordinates to the assembled M1 Euler step. -/
theorem euler_refines (γ dx dt : ℝ) (_hg : 1 < γ) (_hdx : 0 < dx) (_hdt : 0 ≤ dt)
    (u : ZMod n → Conservative 1) (_hadm : ∀ j, (u j).Admissible γ) (old : Array (EulerState ℝ))
    (hu : old = samples (fun j => Euler1D.encode (u j))) :
    stepArray (euler 1 2 γ abs Real.sqrt max) (1/2) dx dt old =
      samples (fun j => Euler1D.encode (Euler1D.step γ dx dt u j)) := by
  rw [hu, euler_model, exact_step]
  simp [Euler1D.step]

end CFDLean.Exec.FV1D
