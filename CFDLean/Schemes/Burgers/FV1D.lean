import CFDLean.Discrete.Periodic.Rusanov
import CFDLean.Schemes.Burgers.RusanovForwardEuler
import Mathlib.Tactic.Ring

noncomputable section
namespace CFDLean.Burgers

theorem fv1d_face_eq (L R : ℝ) : FV1D.face physicalFlux Rusanov.waveSpeed L R = Rusanov.eval L R := by
  simp only [FV1D.face, smul_eq_mul, Rusanov.eval]
  ring

/-- FV1D-B. Cellwise agreement with the assembled B0 step. -/
theorem fv1d_step_eq {N : ℕ} [NeZero N] (dx dt : ℝ) (_hdx : 0 < dx) (_hdt : 0 ≤ dt)
    (u : ZMod N → ℝ) (i : ZMod N) :
    FV1D.step (Periodic.zmodGrid N) physicalFlux Rusanov.waveSpeed dx dt u i =
      Schemes.RusanovForwardEuler.step dx dt u i := by
  simp only [FV1D.step, fv1d_face_eq, smul_eq_mul, Schemes.RusanovForwardEuler.step,
    Time.ForwardEuler.step, Schemes.RusanovForwardEuler.semidiscrete, Schemes.RusanovForwardEuler.grid,
    Scalar.FiniteVolume.rhs, Scalar.FiniteVolume.interfaceFlux, Rusanov.numericalFlux, div_eq_mul_inv]
  ring

end CFDLean.Burgers
