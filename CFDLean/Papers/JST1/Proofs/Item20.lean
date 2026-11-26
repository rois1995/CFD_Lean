import CFDLean.Papers.JST1.Spec.Item20

/-! Proofs of item 20 (P5): the paper's Euler definitions against the M1 Euler physics. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Proofs

open CFDLean.JST1.Spec

variable {d : ℕ}

theorem dot_self_eq_squareSum (v : Vec d) : Num.dot v v = CFDLean.squareSum v := by
  simp only [Num.dot, CFDLean.squareSum, sq]

theorem p5_20_1 : CFDLean.JST1.Spec.P5_20_1 := by
  intro d
  refine ⟨fun U => rfl, fun U => ?_, fun U => ⟨rfl, rfl, rfl⟩⟩
  funext c
  cases c <;> rfl

theorem pressure_toState (g : Gas) (U : CFDLean.Conservative d) :
    pressure g (toState U) = U.pressure g.γ := by
  simp only [pressure, CFDLean.Conservative.pressure, ← dot_self_eq_squareSum]
  rfl

theorem p5_20_2 : CFDLean.JST1.Spec.P5_20_2 := by
  intro d g
  refine ⟨pressure_toState g, fun U => ?_, fun U => rfl, fun r v p => ?_⟩
  · simp only [Admissible, CFDLean.Conservative.Admissible, pressure_toState]
    rfl
  · funext c
    cases c <;>
      simp only [primState, toState, CFDLean.Primitive.toConservative, dot_self_eq_squareSum]

theorem p5_20_3 : CFDLean.JST1.Spec.P5_20_3 := by
  intro d g U y
  have hv : Num.dot (vel (toState U)) y = CFDLean.dot U.momentum y / U.density := by
    simp only [Num.dot, CFDLean.dot, vel, mom, rho, toState, Finset.sum_div]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  funext c
  cases c <;> simp only [physFlux, CFDLean.physicalFlux, toState, hv, pressure_toState] <;> rfl

theorem p5_20_4 : CFDLean.JST1.Spec.P5_20_4 := by
  intro d g U
  have hp := pressure_toState g U
  refine ⟨?_, ?_⟩
  · simp only [entropyFun, physEntropy, hp]
    rfl
  · funext c
    cases c <;>
      simp only [entropyVars, physEntropy, hp, toState, CFDLean.Conservative.toPrimitive,
        ← dot_self_eq_squareSum] <;> rfl

end CFDLean.JST1.Proofs
