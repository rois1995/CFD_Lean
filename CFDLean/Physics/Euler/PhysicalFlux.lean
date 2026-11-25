import CFDLean.Physics.Euler.State

noncomputable section

namespace CFDLean

open scoped BigOperators

variable {d : ℕ}

def dot (v S : Vector d) : ℝ := ∑ i, v i * S i

/-- Integrated Euler flux for an oriented area vector, including zero area. -/
def physicalFlux (γ : ℝ) (U : Conservative d) (S : Vector d) : Conservative d :=
  ⟨dot U.momentum S,
    fun i => U.momentum i * (dot U.momentum S / U.density) + U.pressure γ * S i,
    (U.energy + U.pressure γ) * (dot U.momentum S / U.density)⟩

theorem dot_add (v S T : Vector d) :
    dot v (fun i => S i + T i) = dot v S + dot v T := by
  simp only [dot, mul_add, Finset.sum_add_distrib]

theorem dot_mul (v S : Vector d) (a : ℝ) :
    dot v (fun i => a * S i) = a * dot v S := by
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring1

theorem physicalFlux_add (γ : ℝ) (U : Conservative d) (S T : Vector d) :
    physicalFlux γ U (fun i => S i + T i) =
      ⟨(physicalFlux γ U S).density + (physicalFlux γ U T).density,
       fun i => (physicalFlux γ U S).momentum i + (physicalFlux γ U T).momentum i,
       (physicalFlux γ U S).energy + (physicalFlux γ U T).energy⟩ := by
  simp only [physicalFlux, dot_add, add_div, mul_add]
  congr 1
  funext i
  ring1

theorem physicalFlux_mul (γ : ℝ) (U : Conservative d) (S : Vector d) (a : ℝ) :
    physicalFlux γ U (fun i => a * S i) =
      ⟨a * (physicalFlux γ U S).density,
       fun i => a * (physicalFlux γ U S).momentum i,
       a * (physicalFlux γ U S).energy⟩ := by
  simp only [physicalFlux, dot_mul]
  congr 1
  · funext i
    ring1
  · ring1

theorem physicalFlux_reverse (γ : ℝ) (U : Conservative d) (S : Vector d) :
    physicalFlux γ U (fun i => -S i) =
      ⟨-(physicalFlux γ U S).density,
       fun i => -(physicalFlux γ U S).momentum i,
       -(physicalFlux γ U S).energy⟩ := by
  simpa only [neg_one_mul] using physicalFlux_mul γ U S (-1)

theorem physicalFlux_zero (γ : ℝ) (U : Conservative d) :
    physicalFlux γ U (fun _ => 0) = ⟨0, fun _ => 0, 0⟩ := by
  simp [physicalFlux, dot]

end CFDLean
