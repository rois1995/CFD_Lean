import CFDLean.Exec.NonuniformRefinement
import CFDLean.Schemes.Burgers.NonuniformControls
import CFDLean.Schemes.Euler.NonuniformControls

/-! FVNA controls: exact real values of the non-uniform array kernels of `CFDLean.Exec.NonuniformKernel`.

- FVN-BC (Burgers): widths `(1, 3, 1, 1)`, state `(0, 1, 6/5, 0)`, `dt = 1/10`. First order
  `(1/40, 1463/1500, 1141/1000, 27/250)` (`burgers_firstOrder_fvnBC`); minmod MUSCL Forward Euler
  `(289/16000, 23327/24000, 18529/16000, 27/250)` (`burgers_minmod_fvnBC`). Cells 0 and 3 read the seam face between
  cell 3 and cell 0, so these four-cell values also check the periodic width and state alignment there.
- FVN-E (Euler, `γ = 2`): widths `(1, 2, 1)`, `dt = 1/16`, states `(ρ, ρ, 2 + ρ/2)` for `ρ = 1, 4, 9`. First order:
  densities `(35/16, 249/64, 257/32)`, momenta equal to the densities, energies `(99/32, 505/128, 385/64)`
  (`euler_firstOrder_fvnE`).
- Edges: an empty input gives an empty output, for every arithmetic and every kernel; one cell (the seam reads the
  cell itself) and `dt = 0` give the identity, for every kernel.

The FVN-BC and FVN-E values are obtained from the FVN controls (`CFDLean.Burgers.Nonuniform`,
`CFDLean.Euler1D.NonuniformControls`) through the FVNA-F and FVNA-M refinement theorems on `meshOf widths`, with the
input and output arrays matched entry by entry. One value (one kernel output) per declaration. -/
noncomputable section
namespace CFDLean.Exec.NonuniformControls

open Periodic
open _root_.CFDLean.Exec.FV1D (samples)

/-! ### Array literal as a stored field -/

private theorem samples_four (a b c d : ℝ) : samples (n := 4) (![a, b, c, d] : ZMod 4 → ℝ) = #[a, b, c, d] := by
  apply Array.ext (by simp [samples])
  intro j hj _
  have h : j < 4 := by simpa [samples] using hj
  interval_cases j <;> rfl

/-! ### FVN-BC, Burgers -/

private theorem bc_pos :
    ∀ (i : ℕ) (hi : i < (#[1, 3, 1, 1] : Array ℝ).size), 0 < (#[1, 3, 1, 1] : Array ℝ)[i] := by
  intro i hi
  have h : i < 4 := by simpa using hi
  interval_cases i <;> norm_num

private theorem bc_mesh : meshOf (n := 4) #[1, 3, 1, 1] rfl bc_pos = Burgers.Nonuniform.fvnMesh := by
  unfold meshOf Burgers.Nonuniform.fvnMesh
  congr 1
  funext j
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
  rcases h with rfl | rfl | rfl | rfl <;> rfl

private theorem bc_state : (#[0, 1, 6 / 5, 0] : Array ℝ) = samples Burgers.Nonuniform.fvnState :=
  (samples_four _ _ _ _).symm

/-- FVNA control, FVN-BC first order: one step of the real first-order array kernel with the Burgers model. -/
theorem burgers_firstOrder_fvnBC :
    FV1D.nonuniformStepArray FV1D.burgers (1 / 2) (1 / 10) (#[1, 3, 1, 1] : Array ℝ) #[0, 1, 6 / 5, 0] =
      #[1 / 40, 1463 / 1500, 1141 / 1000, 27 / 250] := by
  rw [burgers_nonuniform_refines (n := 4) (1 / 10) _ rfl bc_pos _ _ bc_state, bc_mesh,
    Burgers.Nonuniform.firstOrderStep_fvnMesh]
  exact samples_four _ _ _ _

/-- FVNA control, FVN-BC minmod MUSCL: one Forward-Euler step of the real non-uniform MUSCL array kernel. -/
theorem burgers_minmod_fvnBC :
    nuLimiterEulerStepArray Limiter.minmod (1 / 10) (#[1, 3, 1, 1] : Array ℝ) #[0, 1, 6 / 5, 0] =
      #[289 / 16000, 23327 / 24000, 18529 / 16000, 27 / 250] := by
  rw [nuLimiterEulerStepArray_refines Limiter.minmod _ rfl bc_pos _ (1 / 10) _ bc_state, bc_mesh,
    show Limiter.minmod.slopeFn = Scalar.FiniteVolume.minmod from Scalar.FiniteVolume.limitedSlope_minmodFactor,
    Burgers.Nonuniform.musclStep_fvnMesh_minmod]
  exact samples_four _ _ _ _

/-! ### FVN-E, Euler -/

private theorem e_pos : ∀ (i : ℕ) (hi : i < (#[1, 2, 1] : Array ℝ).size), 0 < (#[1, 2, 1] : Array ℝ)[i] := by
  intro i hi
  have h : i < 3 := by simpa using hi
  interval_cases i <;> norm_num

private theorem e_mesh : meshOf (n := 3) #[1, 2, 1] rfl e_pos = Euler1D.NonuniformControls.m3 := by
  unfold meshOf Euler1D.NonuniformControls.m3
  congr 1
  funext j
  have h : j = 0 ∨ j = 1 ∨ j = 2 := by revert j; decide
  rcases h with rfl | rfl | rfl <;> rfl

private theorem e_adm (j : ZMod 3) : (Euler1D.NonuniformControls.initial j).Admissible 2 := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 := by revert j; decide
  rcases h with rfl | rfl | rfl <;>
    norm_num [Euler1D.NonuniformControls.initial, Euler1D.NonuniformControls.state, Conservative.Admissible,
      Conservative.pressure, squareSum, dot]

private theorem e_state :
    #[FV1D.triple 1 1 (2 + 1 / 2), FV1D.triple 4 4 (2 + 4 / 2), FV1D.triple 9 9 (2 + 9 / 2)] =
      samples (fun j => Euler1D.encode (Euler1D.NonuniformControls.initial j)) := by
  apply Array.ext (by simp)
  intro j hj _
  have h : j < 3 := by simpa using hj
  interval_cases j <;> funext k <;> fin_cases k <;> rfl

/-- FVNA control, FVN-E first order: one step of the real first-order array kernel with the Euler model at `γ = 2`
on the states `(ρ, ρ, 2 + ρ/2)`, `ρ = 1, 4, 9`. -/
theorem euler_firstOrder_fvnE :
    FV1D.nonuniformStepArray (FV1D.euler 1 2 2 abs Real.sqrt max) (1 / 2) (1 / 16) (#[1, 2, 1] : Array ℝ)
        #[FV1D.triple 1 1 (2 + 1 / 2), FV1D.triple 4 4 (2 + 4 / 2), FV1D.triple 9 9 (2 + 9 / 2)] =
      #[FV1D.triple (35 / 16) (35 / 16) (99 / 32), FV1D.triple (249 / 64) (249 / 64) (505 / 128),
        FV1D.triple (257 / 32) (257 / 32) (385 / 64)] := by
  rw [euler_nonuniform_refines (n := 3) 2 (1 / 16) one_lt_two _ rfl e_pos _ e_adm _ e_state, e_mesh]
  simp only [Euler1D.NonuniformControls.nonuniformStep_cells]
  apply Array.ext (by simp)
  intro j hj _
  have h : j < 3 := by simpa using hj
  interval_cases j <;> funext k <;> fin_cases k <;> rfl

/-! ### Edges: empty input -/

section Empty

variable {α : Type}

/-- Empty input, first order: empty output, for every arithmetic and model. -/
theorem nonuniformStepArray_empty {S : Type} [Mul α] [Div α] [Zero α] (M : FV1D.Model α S) (half dt : α)
    (widths : Array α) : FV1D.nonuniformStepArray M half dt widths #[] = #[] := by
  exact Array.eq_empty_of_size_eq_zero (by simp)

variable [Scalar α] [ScalarSign α] (L : Limiter) (dt : α) (widths : Array α)

/-- Empty input, MUSCL Forward Euler: empty output, for every arithmetic and limiter. -/
theorem nuLimiterEulerStepArray_empty : nuLimiterEulerStepArray L dt widths #[] = #[] := by
  exact Array.eq_empty_of_size_eq_zero (by simp)

/-- Empty input, MUSCL SSPRK2: empty output, for every arithmetic and limiter. -/
theorem nuLimiterSsprk2StepArray_empty : nuLimiterSsprk2StepArray L dt widths #[] = #[] := by
  exact Array.eq_empty_of_size_eq_zero (by simp)

/-- Empty input, MUSCL SSPRK3: empty output, for every arithmetic and limiter. -/
theorem nuLimiterSsprk3StepArray_empty : nuLimiterSsprk3StepArray L dt widths #[] = #[] := by
  exact Array.eq_empty_of_size_eq_zero (by simp)

end Empty

/-! ### Edges: `dt = 0` -/

/-- `a u + b u = u` when `a + b = 1`. -/
private theorem axpby_self (a b : ℝ) (h : a + b = 1) (u : Array ℝ) : axpby a u b u = u := by
  apply Array.ext (by simp [axpby])
  intro j _ _
  simp only [axpby, Array.getElem_zipWith]
  rw [← add_mul, h, one_mul]

/-- `dt = 0`, first order, Burgers: the identity, for every widths and state. -/
theorem burgers_nonuniformStepArray_dt_zero (widths u : Array ℝ) :
    FV1D.nonuniformStepArray FV1D.burgers (1 / 2) 0 widths u = u := by
  apply Array.ext (by simp)
  intro j _ _
  simp [FV1D.nonuniformStepArray, FV1D.burgers]

/-- `dt = 0`, first order, Euler: the identity, for every `γ`, widths and state. -/
theorem euler_nonuniformStepArray_dt_zero (γ : ℝ) (widths : Array ℝ) (u : Array (FV1D.EulerState ℝ)) :
    FV1D.nonuniformStepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1 / 2) 0 widths u = u := by
  apply Array.ext (by simp)
  intro j _ _
  simp only [FV1D.nonuniformStepArray, Array.getElem_ofFn]
  funext k
  simp [FV1D.euler]

/-- `dt = 0`, MUSCL Forward Euler: the identity, for every limiter, widths and state. -/
theorem nuLimiterEulerStepArray_dt_zero (L : Limiter) (widths u : Array ℝ) :
    nuLimiterEulerStepArray L 0 widths u = u := by
  apply Array.ext (by simp)
  intro j _ _
  simp [nuLimiterEulerStepArray]

/-- `dt = 0`, MUSCL SSPRK2: the identity, for every limiter, widths and state. -/
theorem nuLimiterSsprk2StepArray_dt_zero (L : Limiter) (widths u : Array ℝ) :
    nuLimiterSsprk2StepArray L 0 widths u = u := by
  rw [nuLimiterSsprk2StepArray, nuLimiterEulerStepArray_dt_zero, nuLimiterEulerStepArray_dt_zero]
  exact axpby_self _ _ (by norm_num [Scalar.half]) u

/-- `dt = 0`, MUSCL SSPRK3: the identity, for every limiter, widths and state. -/
theorem nuLimiterSsprk3StepArray_dt_zero (L : Limiter) (widths u : Array ℝ) :
    nuLimiterSsprk3StepArray L 0 widths u = u := by
  simp only [nuLimiterSsprk3StepArray, nuLimiterEulerStepArray_dt_zero]
  rw [axpby_self _ _ (by norm_num [Scalar.threeQuarters, Scalar.quarter]) u]
  exact axpby_self _ _ (by norm_num [Scalar.third, Scalar.twoThirds]) u

/-! ### Edges: one cell

With one cell the left and right neighbours are the cell itself, so both faces of the cell carry the same flux. -/

/-- With one cell the left neighbour is the cell itself. -/
private theorem prevIdx_self {m : ℕ} (hm : m = 1) (i : Fin m) : prevIdx i = i := by
  subst hm
  exact Subsingleton.elim _ _

/-- One cell, first order, Burgers: the identity, for every `dt`, width and value. -/
theorem burgers_nonuniformStepArray_one_cell (dt w a : ℝ) :
    FV1D.nonuniformStepArray FV1D.burgers (1 / 2) dt #[w] #[a] = #[a] := by
  apply Array.ext (by simp)
  intro j hj _
  have h : j = 0 := by simpa using hj
  subst h
  simp [FV1D.nonuniformStepArray, FV1D.burgers]

/-- One cell, first order, Euler: the identity, for every `γ`, `dt`, width and state. -/
theorem euler_nonuniformStepArray_one_cell (γ dt w : ℝ) (s : FV1D.EulerState ℝ) :
    FV1D.nonuniformStepArray (FV1D.euler 1 2 γ abs Real.sqrt max) (1 / 2) dt #[w] #[s] = #[s] := by
  apply Array.ext (by simp)
  intro j hj _
  have h : j = 0 := by simpa using hj
  subst h
  simp only [FV1D.nonuniformStepArray, Array.getElem_ofFn]
  funext k
  simp [FV1D.euler]

/-- One cell, MUSCL Forward Euler: the identity, for every limiter, `dt`, width and value. -/
theorem nuLimiterEulerStepArray_one_cell (L : Limiter) (dt w a : ℝ) :
    nuLimiterEulerStepArray L dt #[w] #[a] = #[a] := by
  apply Array.ext (by simp)
  intro j hj _
  have h : j = 0 := by simpa using hj
  subst h
  simp only [nuLimiterEulerStepArray, Array.getElem_ofFn]
  rw [prevIdx_self (by simp)]
  simp

/-- One cell, MUSCL SSPRK2: the identity, for every limiter, `dt`, width and value. -/
theorem nuLimiterSsprk2StepArray_one_cell (L : Limiter) (dt w a : ℝ) :
    nuLimiterSsprk2StepArray L dt #[w] #[a] = #[a] := by
  rw [nuLimiterSsprk2StepArray, nuLimiterEulerStepArray_one_cell, nuLimiterEulerStepArray_one_cell]
  exact axpby_self _ _ (by norm_num [Scalar.half]) _

/-- One cell, MUSCL SSPRK3: the identity, for every limiter, `dt`, width and value. -/
theorem nuLimiterSsprk3StepArray_one_cell (L : Limiter) (dt w a : ℝ) :
    nuLimiterSsprk3StepArray L dt #[w] #[a] = #[a] := by
  rw [nuLimiterSsprk3StepArray, nuLimiterEulerStepArray_one_cell, nuLimiterEulerStepArray_one_cell,
    axpby_self _ _ (by norm_num [Scalar.threeQuarters, Scalar.quarter]) #[a], nuLimiterEulerStepArray_one_cell]
  exact axpby_self _ _ (by norm_num [Scalar.third, Scalar.twoThirds]) _

end CFDLean.Exec.NonuniformControls
