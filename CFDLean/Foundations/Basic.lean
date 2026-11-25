import Mathlib

/-! Generic finite-dimensional vocabulary. Exact reals; no floating point.

MC-N: moved verbatim from JST_Paper_Lean `NumCore/Basic.lean` (namespace `NumCore` → `CFDLean.Num`). -/
noncomputable section
open scoped BigOperators
namespace CFDLean.Num

/-- Vectors of `ℝ^d` as functions (no norm structure is used: see `len`). -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Euclidean inner product. -/
def dot {d : ℕ} (u v : Vec d) : ℝ := ∑ α, u α * v α

/-- Euclidean length (the Pi-type norm of Mathlib is the sup norm, so it is not used). -/
def len {d : ℕ} (u : Vec d) : ℝ := Real.sqrt (dot u u)

/-- Outer product `u ⊗ v = u vᵀ`, entry `(α, β)` is `u α * v β`. -/
def outer {d : ℕ} (u v : Vec d) : Matrix (Fin d) (Fin d) ℝ := fun α β => u α * v β

/-- Pairing of two vectors on a finite index type (states, entropy variables). -/
def pairF {κ : Type} [Fintype κ] (x y : κ → ℝ) : ℝ := ∑ c, x c * y c

/-- Frobenius product `A : B`. -/
def frob {κ ι : Type} [Fintype κ] [Fintype ι] (A B : Matrix κ ι ℝ) : ℝ := ∑ r, ∑ c, A r c * B r c

/-- The continuous linear functional `x ↦ pairF w x`. -/
def pairCLM {κ : Type} [Fintype κ] (w : κ → ℝ) : (κ → ℝ) →L[ℝ] ℝ :=
  ∑ c, w c • ContinuousLinearMap.proj c

end CFDLean.Num
