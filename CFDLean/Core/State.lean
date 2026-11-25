import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.Basic

/-! Exact-real ideal-gas Euler states. See specifications/M1.md and references/M1.md. -/
noncomputable section

namespace CFDLean

open scoped BigOperators

abbrev Vector (d : ℕ) := Fin d → ℝ

def squareSum {d : ℕ} (v : Vector d) : ℝ := ∑ i, (v i) ^ 2

structure Conservative (d : ℕ) where
  density : ℝ
  momentum : Vector d
  energy : ℝ

structure Primitive (d : ℕ) where
  density : ℝ
  velocity : Vector d
  pressure : ℝ

variable {d : ℕ}

def Conservative.pressure (γ : ℝ) (U : Conservative d) : ℝ :=
  (γ - 1) * (U.energy - squareSum U.momentum / (2 * U.density))

def Conservative.Admissible (γ : ℝ) (U : Conservative d) : Prop :=
  0 < U.density ∧ 0 < U.pressure γ

def Primitive.Admissible (W : Primitive d) : Prop :=
  0 < W.density ∧ 0 < W.pressure

def Primitive.toConservative (γ : ℝ) (W : Primitive d) : Conservative d :=
  ⟨W.density, fun i => W.density * W.velocity i,
    W.pressure / (γ - 1) + W.density * squareSum W.velocity / 2⟩

def Conservative.toPrimitive (γ : ℝ) (U : Conservative d) : Primitive d :=
  ⟨U.density, fun i => U.momentum i / U.density, U.pressure γ⟩

theorem squareSum_mul (a : ℝ) (v : Vector d) :
    squareSum (fun i => a * v i) = a ^ 2 * squareSum v := by
  simp only [squareSum, mul_pow, Finset.mul_sum]

theorem squareSum_div (v : Vector d) (a : ℝ) :
    squareSum (fun i => v i / a) = squareSum v / a ^ 2 := by
  simp only [squareSum, div_pow, Finset.sum_div]

set_option linter.unusedVariables false in
theorem pressure_toConservative (γ : ℝ) (W : Primitive d)
    (hγ : γ ≠ 1) (hρ : W.density ≠ 0) :
    (W.toConservative γ).pressure γ = W.pressure := by
  simp only [Conservative.pressure, Primitive.toConservative, squareSum_mul]
  field_simp [sub_ne_zero.mpr hγ, hρ]
  ring1

theorem primitive_roundTrip (γ : ℝ) (W : Primitive d)
    (hγ : γ ≠ 1) (hρ : W.density ≠ 0) :
    (W.toConservative γ).toPrimitive γ = W := by
  have hp := pressure_toConservative γ W hγ hρ
  cases W with
  | mk ρ v p =>
    simp only [Conservative.toPrimitive, Primitive.toConservative] at hp ⊢
    simp only [mul_div_cancel_left₀ _ hρ, hp]

theorem conservative_roundTrip (γ : ℝ) (U : Conservative d)
    (hγ : γ ≠ 1) (hρ : U.density ≠ 0) :
    (U.toPrimitive γ).toConservative γ = U := by
  cases U with
  | mk ρ m E =>
    simp only [Conservative.toPrimitive, Primitive.toConservative, Conservative.pressure,
      squareSum_div]
    have hm : (fun i => ρ * (m i / ρ)) = m := by
      funext i
      exact mul_div_cancel₀ (m i) hρ
    rw [hm]
    congr 1
    field_simp [sub_ne_zero.mpr hγ, hρ]
    ring1

theorem primitive_admissible_toConservative (γ : ℝ) (W : Primitive d)
    (hγ : 1 < γ) (hW : W.Admissible) :
    (W.toConservative γ).Admissible γ := by
  refine ⟨hW.1, ?_⟩
  rw [pressure_toConservative γ W (ne_of_gt hγ) (ne_of_gt hW.1)]
  exact hW.2

theorem conservative_admissible_toPrimitive (γ : ℝ) (U : Conservative d)
    (hU : U.Admissible γ) : (U.toPrimitive γ).Admissible := hU

theorem admissible_iff_internalEnergy_pos (γ : ℝ) (U : Conservative d)
    (hγ : 1 < γ) :
    U.Admissible γ ↔ 0 < U.density ∧
      squareSum U.momentum / (2 * U.density) < U.energy := by
  simp only [Conservative.Admissible, Conservative.pressure]
  have hg : 0 < γ - 1 := sub_pos.mpr hγ
  rw [mul_pos_iff_of_pos_left hg, sub_pos]

theorem admissible_exists (γ : ℝ) (hγ : 1 < γ) :
    ∃ U : Conservative d, U.Admissible γ := by
  exact ⟨(Primitive.mk 1 (fun _ => 0) 1).toConservative γ,
    primitive_admissible_toConservative γ _ hγ ⟨zero_lt_one, zero_lt_one⟩⟩

end CFDLean
