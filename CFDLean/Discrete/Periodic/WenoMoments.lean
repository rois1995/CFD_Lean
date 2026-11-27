import CFDLean.Discrete.Periodic.GradedWeno
import Mathlib.Tactic.FieldSimp

/-! The cubic and quartic moments of the *linear* five-cell WENO reconstruction at the face x=0.
Coordinates use the owner's width. Each mean below is the exact interval mean of the named monomial. -/
namespace CFDLean.GradedWeno

noncomputable section

def cubicMean (w x : ℝ) := x^3 + x*w^2/4
def quarticMean (w x : ℝ) := x^4 + x^2*w^2/2 + w^4/80

def faceMeans (f : ℝ → ℝ → ℝ) (a b d e : ℝ) : Stencil ℝ :=
  ⟨f a (-1-b-a/2), f b (-1-b/2), f 1 (-1/2), f d (d/2), f e (d+e/2)⟩

def linearEdge (a b d e : ℝ) (u : Stencil ℝ) : ℝ :=
  let w := ideal a b d e
  (w.1 * (candidate a b 1 ((b+1)/2) u.farLeft u.left u.center).1 +
    w.2.1 * (candidate b 1 d 0 u.left u.center u.right).1 +
    w.2.2 * (candidate 1 d e (-(1+d)/2) u.center u.right u.farRight).1) / 10

private theorem left_moments {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let L := a+b+1
    let B := b+1
    let trace (f : ℝ → ℝ → ℝ) := (candidate a b 1 (B/2)
      (f a (-1-b-a/2)) (f b (-1-b/2)) (f 1 (-1/2))).1
    trace cubicMean = -L*B/4 ∧ trace quarticMean = -L*B*(-L-B-1)/5 := by
  dsimp [candidate, cubicMean, quarticMean]
  constructor <;> field_simp <;> ring

private theorem middle_moments {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    let B := b+1
    let trace (f : ℝ → ℝ → ℝ) := (candidate b 1 d 0
      (f b (-1-b/2)) (f 1 (-1/2)) (f d (d/2))).1
    trace cubicMean = B*d/4 ∧ trace quarticMean = B*d*(-B-1+d)/5 := by
  dsimp [candidate, cubicMean, quarticMean]
  constructor <;> field_simp <;> ring

private theorem right_moments {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    let R := d+e
    let trace (f : ℝ → ℝ → ℝ) := (candidate 1 d e (-(1+d)/2)
      (f 1 (-1/2)) (f d (d/2)) (f e (d+e/2))).1
    trace cubicMean = -d*R/4 ∧ trace quarticMean = -d*R*(-1+d+R)/5 := by
  dsimp [candidate, cubicMean, quarticMean]
  constructor <;> field_simp <;> ring

/-- For arbitrary positive neighboring widths the same ideal weights annihilate both moments.
Together with exact three-cell quadratic candidates this characterizes the degree-four linear reconstruction. -/
theorem ideal_cubic_quartic {a b d e : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e) :
    linearEdge a b d e (faceMeans cubicMean a b d e) = 0 ∧
    linearEdge a b d e (faceMeans quarticMean a b d e) = 0 := by
  obtain ⟨lc,lq⟩ := left_moments ha hb
  obtain ⟨mc,mq⟩ := middle_moments hb hd
  obtain ⟨rc,rq⟩ := right_moments hd he
  simp only [linearEdge, faceMeans, lc, lq, mc, mq, rc, rq, ideal]
  constructor <;> field_simp <;> ring

end
end CFDLean.GradedWeno
