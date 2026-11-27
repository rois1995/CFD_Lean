import CFDLean.Physics.Euler.State
import CFDLean.Exec.FV1D
import CFDLean.Exec.MusclKernel
import Mathlib.Tactic.Ring

/-! Uniform cell-owned conservative MUSCL traces with paired admissibility fallback. -/
namespace CFDLean.Exec.EulerTraces

open CFDLean.Exec.FV1D (EulerState pressure)

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

end CFDLean.Exec.EulerTraces
