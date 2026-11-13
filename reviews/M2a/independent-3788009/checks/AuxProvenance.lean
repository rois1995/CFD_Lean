import Mathlib.Analysis.Calculus.FDeriv.Prod

noncomputable section
namespace ReviewerAux
abbrev Vec := Fin 5 → ℝ
abbrev proj (i : Fin 5) : Vec →L[ℝ] ℝ := ContinuousLinearMap.proj i
def dot3 (v w : Fin 3 → ℝ) := ∑ i, v i * w i
def squared3 (v : Fin 3 → ℝ) := ∑ i, (v i)^2
end ReviewerAux
