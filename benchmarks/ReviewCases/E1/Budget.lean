import ReviewCases.E1.Binary64
import ReviewCases.E1.ExactStep

namespace ReviewCases.E1

open CFDLean.Exec

private def within (budget ref : ℚ) (x : Option Float) : Bool :=
  (x.bind value).any fun q => decide (|q - ref| ≤ budget)

private def compareStep (budget : ℚ) (actual : Array Float) (ref : Array ℚ) : Bool :=
  decide (actual.size = ref.size) &&
    decide (∀ i : Fin ref.size, within budget ref[i] actual[i.val]? = true)

/-- Check the observed kernel result against a budget supplied independently of that result. -/
def checkStep (dx dt : Float) (old : Array Float) (budget : ℚ) : Bool :=
  match value dx, value dt, old.mapM value with
  | some x, some t, some qs =>
    decide (0 < old.size ∧ 0 < x ∧ 0 ≤ t ∧ 0 ≤ budget) &&
      compareStep budget (eulerStepArray dx dt old) (eulerStepArray x t qs)
  | _, _, _ => false

/-- Acceptance gives a finite observed value at every reference cell, within the requested real budget. -/
theorem checkStep_sound {dx dt : Float} {old : Array Float} {budget : ℚ}
    (accepted : checkStep dx dt old budget = true) :
    ∃ x t qs, value dx = some x ∧ value dt = some t ∧ old.mapM value = some qs ∧
      (0 < old.size ∧ 0 < x ∧ 0 ≤ t ∧ 0 ≤ budget) ∧
      (eulerStepArray dx dt old).size = (eulerStepArray x t qs).size ∧
      ∀ i : Fin (eulerStepArray x t qs).size, ∃ q : ℚ,
        ((eulerStepArray dx dt old)[i.val]?.bind value) = some q ∧
        |(q : ℝ) - (((eulerStepArray x t qs)[i] : ℚ) : ℝ)| ≤ (budget : ℝ) := by
  cases hx : value dx with
  | none => simp [checkStep, hx] at accepted
  | some x =>
    cases ht : value dt with
    | none => simp [checkStep, hx, ht] at accepted
    | some t =>
      cases hu : old.mapM value with
      | none => simp [checkStep, hx, ht, hu] at accepted
      | some qs =>
        simp only [checkStep, hx, ht, hu, compareStep, Bool.and_eq_true, decide_eq_true_eq] at accepted
        refine ⟨x, t, qs, rfl, rfl, rfl, accepted.1, accepted.2.1, ?_⟩
        intro i
        have h := accepted.2.2 i
        cases hq : (eulerStepArray dx dt old)[i.val]?.bind value with
        | none => simp [within, hq] at h
        | some q =>
          simp [within, hq] at h
          exact ⟨q, rfl, by exact_mod_cast h⟩

/-- Express the certificate directly against E0's real kernel at the decoded input values. -/
theorem real_cell_bound {dx dt : Float} {old : Array Float} {budget x t : ℚ} {qs : Array ℚ}
    (accepted : checkStep dx dt old budget = true) (hx : value dx = some x)
    (ht : value dt = some t) (hu : old.mapM value = some qs) (i : Nat) (r : ℝ)
    (hr : (eulerStepArray (x : ℝ) (t : ℝ) (qs.map fun q : ℚ => (q : ℝ)))[i]? = some r) :
    ∃ q : ℚ, ((eulerStepArray dx dt old)[i]?.bind value) = some q ∧ |(q : ℝ) - r| ≤ (budget : ℝ) := by
  obtain ⟨x', t', qs', hx', ht', hu', _, _, hc⟩ := checkStep_sound accepted
  rw [hx] at hx'
  rw [ht] at ht'
  rw [hu] at hu'
  cases hx'
  cases ht'
  cases hu'
  rw [← cast_step, Array.getElem?_map] at hr
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨hi, rfl⟩ := getElem?_eq_some_iff.mp ha
  exact hc ⟨i, hi⟩

end ReviewCases.E1
