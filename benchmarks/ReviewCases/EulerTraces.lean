import CFDLean.Physics.Euler.State
import CFDLean.Exec.FV1D
import CFDLean.Exec.MusclKernel
import ReviewCases.E1.ExactStep
import Mathlib.Tactic.Ring

/-! Candidate cell-owned conservative traces. These controls do not advance the Euler state. -/
namespace ReviewCases.EulerTraces

open CFDLean.Exec
open FV1D (EulerState triple pressure)

variable {α : Type} [Field α] [LinearOrder α]

def admissible (γ : α) (u : EulerState α) : Prop := 0 < u 0 ∧ 0 < pressure 1 2 γ u

instance (γ : α) (u : EulerState α) : Decidable (admissible γ u) :=
  inferInstanceAs (Decidable (_ ∧ _))

def raw (u s : EulerState α) : EulerState α × EulerState α :=
  (fun k => u k - s k / 2, fun k => u k + s k / 2)

def select (γ : α) (u s : EulerState α) : EulerState α × EulerState α :=
  let pair := raw u s
  if admissible γ pair.1 ∧ admissible γ pair.2 then pair else (u, u)

theorem admissible_pair {γ : α} {u : EulerState α} (hu : admissible γ u) (s : EulerState α) :
    admissible γ (select γ u s).1 ∧ admissible γ (select γ u s).2 := by
  dsimp only [select]
  split
  · assumption
  · exact ⟨hu, hu⟩

theorem retain_raw {γ : α} {u s : EulerState α}
    (h : admissible γ (raw u s).1 ∧ admissible γ (raw u s).2) :
    select γ u s = raw u s := by simp [select, h]

theorem pair_sum (γ : α) (u s : EulerState α) (k : Fin 3) :
    (select γ u s).1 k + (select γ u s).2 k = 2 * u k := by
  dsimp only [select]
  split <;> simp only [raw] <;> ring

def slope (lim : α → α → α) (a u b : EulerState α) : EulerState α :=
  fun k => lim (u k - a k) (b k - u k)

def faceStates (lim : α → α → α) (γ : α) (u : Array (EulerState α)) (i : Fin u.size) :
    EulerState α × EulerState α :=
  let cell (j : Fin u.size) := select γ u[j] (slope lim u[prevIdx j] u[j] u[nextIdx j])
  ((cell i).2, (cell (nextIdx i)).1)

theorem face_admissible (lim : α → α → α) {γ : α} {u : Array (EulerState α)}
    (hu : ∀ i : Fin u.size, admissible γ u[i]) (i : Fin u.size) :
    admissible γ (faceStates lim γ u i).1 ∧ admissible γ (faceStates lim γ u i).2 :=
  ⟨(admissible_pair (hu i) _).2, (admissible_pair (hu (nextIdx i)) _).1⟩

theorem admissible_iff_m1 (γ : ℝ) (u : EulerState ℝ) :
    admissible γ u ↔ (⟨u 0, fun _ => u 1, u 2⟩ : CFDLean.Conservative 1).Admissible γ := by
  simp [admissible, pressure, CFDLean.Conservative.Admissible, CFDLean.Conservative.pressure,
    CFDLean.squareSum, pow_two]

theorem face_constant (lim : α → α → α) (h0 : lim 0 0 = 0) (γ : α) (c : EulerState α)
    (u : Array (EulerState α)) (hu : ∀ j : Fin u.size, u[j] = c) (i : Fin u.size) :
    faceStates lim γ u i = (c, c) := by
  simp [faceStates, hu, slope, h0, select, raw]

open scoped ReviewCases.E1

private def sample (u : EulerState ℚ) := #[u 0, u 1, u 2]
private def a := triple (1 : ℚ) (-3) 5
private def b := triple (1 : ℚ) (-2) 3
private def c := triple (1 : ℚ) (-1) 3

#guard [a, b, c].all fun q => decide (admissible 2 q)
#guard sample (slope Scalar.minmod a b c) == #[0, 1, 0]
#guard pressure 1 2 2 (raw b (slope Scalar.minmod a b c)).1 == -1/8
#guard pressure 1 2 2 (raw b (slope Scalar.minmod a b c)).2 == 15/8
#guard sample (select 2 b (slope Scalar.minmod a b c)).1 == sample b
#guard sample (select 2 b (slope Scalar.minmod a b c)).2 == sample b

-- A constant-pressure contact with increasing densities retains both reconstructed traces.
private def contact (r : ℚ) := triple r (2*r) (1+2*r)
private def wave := #[contact 2, contact 3, contact 1]
#guard sample (faceStates Scalar.minmod 2 wave ⟨0, by decide⟩).1 == sample (contact (5/2))
#guard sample (faceStates Scalar.minmod 2 wave ⟨2, by decide⟩).2 == sample (contact (3/2))
#guard sample (faceStates Scalar.minmod 2 #[b] 0).1 == sample b
#guard sample (faceStates Scalar.minmod 2 #[b] 0).2 == sample b

end ReviewCases.EulerTraces
