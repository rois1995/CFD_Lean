import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exact scalar-advection control, with one interior face and unequal cell areas. -/
namespace ReviewCases.OrientedTriangles

abbrev Point := ℚ × ℚ

def areaVector (p q : Point) : Point := (q.2 - p.2, p.1 - q.1)

def area (p q r : Point) : ℚ :=
  ((q.1-p.1)*(r.2-p.2) - (q.2-p.2)*(r.1-p.1)) / 2

theorem triangle_closes (p q r : Point) :
    areaVector p q + areaVector q r + areaVector r p = 0 := by
  apply Prod.ext <;> change _ + _ + _ = (0 : ℚ) <;> unfold areaVector <;> dsimp <;> ring

def upwind (s inside outside : ℚ) : ℚ := s * (if 0 ≤ s then inside else outside)

theorem flip_flux (s inside outside : ℚ) :
    upwind (-s) outside inside = - upwind s inside outside := by
  rcases lt_trichotomy s 0 with h | rfl | h
  · simp [upwind, h.le, not_le.mpr h]
  · simp [upwind]
  · simp [upwind, h.le, not_le.mpr h]

private def a : Point := (0, 0)
private def b : Point := (2, 0)
private def c : Point := (2, 1)
private def d : Point := (0, 2)

private def speed (p q : Point) : ℚ :=
  let n := areaVector p q
  n.1 + 2*n.2

private def boundary (x y g : ℚ) : ℚ × ℚ :=
  (upwind (speed a b) x g + upwind (speed b c) x g,
   upwind (speed c d) y g + upwind (speed d a) y g)

def residual (x y g : ℚ) : ℚ × ℚ :=
  let shared := upwind (speed c a) x y
  let outer := boundary x y g
  (outer.1 + shared, outer.2 - shared)

def step (dt x y g : ℚ) : ℚ × ℚ :=
  let outward := residual x y g
  (x - dt*outward.1 / area a b c, y - dt*outward.2 / area a c d)

theorem boundary_balance (dt x y g : ℚ) :
    area a b c * (step dt x y g).1 + area a c d * (step dt x y g).2 =
    area a b c*x + area a c d*y - dt*((boundary x y g).1 + (boundary x y g).2) := by
  have h₁ : area a b c = 1 := by norm_num [area, a, b, c]
  have h₂ : area a c d = 2 := by norm_num [area, a, c, d]
  simp only [step, residual, h₁, h₂]
  ring

theorem constant_residual (k : ℚ) : residual k k k = (0, 0) := by
  apply Prod.ext <;> simp [residual, boundary, upwind, speed, areaVector, a, b, c, d] <;> ring

#guard areaVector c a == (-1, 2) && areaVector a c == (1, -2)
#guard area a b c == 1 && area a c d == 2
#guard upwind (speed c a) 2 5 == 6 && upwind (speed a c) 5 2 == -6
#guard boundary 2 5 1 == (-2, 23)
#guard residual 2 5 1 == (4, 17)
#guard step (1/8) 2 5 1 == (3/2, 63/16)

end ReviewCases.OrientedTriangles
