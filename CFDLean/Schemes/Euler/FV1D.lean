import CFDLean.Discrete.Periodic.Rusanov
import CFDLean.Physics.Euler.PhysicalFlux
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section
namespace CFDLean.Euler1D

/-- Density, x-momentum and total energy in a real vector space. -/
def encode (U : Conservative 1) : Vector 3 := ![U.density, U.momentum 0, U.energy]

def decode (x : Vector 3) : Conservative 1 := ⟨x 0, fun _ => x 1, x 2⟩

@[simp] theorem decode_encode (U : Conservative 1) : decode (encode U) = U := by
  cases U with
  | mk r m e =>
    change Conservative.mk r (fun _ : Fin 1 => m 0) e = ⟨r, m, e⟩
    have hm : (fun _ : Fin 1 => m 0) = m := funext fun j => congrArg m (Subsingleton.elim 0 j)
    rw [hm]

@[simp] theorem encode_decode (x : Vector 3) : encode (decode x) = x := by
  funext i
  fin_cases i <;> rfl

def flux (γ : ℝ) (x : Vector 3) : Vector 3 := encode (physicalFlux γ (decode x) (fun _ => 1))

theorem flux_m1 (γ : ℝ) (U : Conservative 1) :
    decode (flux γ (encode U)) = physicalFlux γ U (fun _ => 1) := by simp [flux]

def endpointSpeed (γ : ℝ) (x : Vector 3) : ℝ :=
  let U := decode x
  |U.momentum 0 / U.density| + Real.sqrt (γ * U.pressure γ / U.density)

def speed (γ : ℝ) (L R : Vector 3) : ℝ := max (endpointSpeed γ L) (endpointSpeed γ R)

def face (γ : ℝ) (L R : Conservative 1) : Conservative 1 :=
  decode (FV1D.face (flux γ) (speed γ) (encode L) (encode R))

def step {N : ℕ} [NeZero N] (γ dx dt : ℝ) (U : ZMod N → Conservative 1) (i : ZMod N) : Conservative 1 :=
  decode (FV1D.step (Periodic.zmodGrid N) (flux γ) (speed γ) dx dt (fun j => encode (U j)) i)

/-- FV1D-F. Equal-state flux on the positive unit face. -/
theorem face_consistent (γ : ℝ) (_hγ : 1 < γ) (C : Conservative 1) (_hC : C.Admissible γ) :
    face γ C C = physicalFlux γ C (fun _ => 1) := by rw [face, FV1D.face_self, flux_m1]

/-- FV1D-K. A physically admissible constant is preserved. -/
theorem step_constant {N : ℕ} [NeZero N] (γ dx dt : ℝ) (_hγ : 1 < γ) (_hdx : 0 < dx)
    (_hdt : 0 ≤ dt) (C : Conservative 1) (_hC : C.Admissible γ) :
    step (N := N) γ dx dt (fun _ => C) = fun _ => C := by
  funext i
  simp [step, FV1D.step_constant]

/-- FV1D-C. Project the common vector balance onto the three M1 quantities. -/
theorem component_balance {N : ℕ} [NeZero N] (γ dx dt : ℝ) (_hγ : 1 < γ) (_hdx : 0 < dx)
    (_hdt : 0 ≤ dt) (U : ZMod N → Conservative 1) (_hU : ∀ i, (U i).Admissible γ) :
    (dx * ∑ i, (step γ dx dt U i).density = dx * ∑ i, (U i).density) ∧
    (dx * ∑ i, (step γ dx dt U i).momentum 0 = dx * ∑ i, (U i).momentum 0) ∧
    (dx * ∑ i, (step γ dx dt U i).energy = dx * ∑ i, (U i).energy) := by
  have balance := FV1D.step_sum (Periodic.zmodGrid N) (flux γ) (speed γ) dx dt (fun j => encode (U j))
  have proj (k : Fin 3) := congrArg (fun x : Vector 3 => dx * x k) balance
  simp only [Finset.sum_apply] at proj
  exact ⟨proj 0, proj 1, proj 2⟩

end CFDLean.Euler1D
