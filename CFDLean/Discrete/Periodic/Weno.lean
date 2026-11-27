import CFDLean.Discrete.Periodic.Reconstruction
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Scalar WENO-JS5 on uniform cell averages. See Jiang and Shu (1996), Table I and
equations (2.15)–(2.16), (3.2)–(3.4), https://doi.org/10.1006/jcph.1996.0130.
The formulas here reconstruct states before the two-point flux is evaluated. -/
namespace CFDLean.FV1D.Reconstruction

open Periodic

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace Weno

/-- Unnormalized Jiang–Shu weight. The smoothness indicator is the sum of two scaled squares. -/
def weight (ε d curvature gradient : K) : K :=
  d / (ε + 13 / 12 * curvature^2 + gradient^2 / 4)^2

theorem weight_pos {ε d : K} (hε : 0 < ε) (hd : 0 < d) (k g : K) : 0 < weight ε d k g := by
  unfold weight
  positivity

/-- Right endpoint of the center cell on an ordered five-cell stencil.
The ideal weights 1/10, 6/10 and 3/10 are scaled by 10, which cancels in the normalization. -/
def edge (ε : {e : K // 0 < e}) (a b c d e : K) : K :=
  let w₀ := weight ε.val 1 (a - 2*b + c) (a - 4*b + 3*c)
  let w₁ := weight ε.val 6 (b - 2*c + d) (b - d)
  let w₂ := weight ε.val 3 (c - 2*d + e) (3*c - 4*d + e)
  let q₀ := (2*a - 7*b + 11*c) / 6
  let q₁ := (-b + 5*c + 2*d) / 6
  let q₂ := (2*c + 5*d - e) / 6
  (w₀*q₀ + w₁*q₁ + w₂*q₂) / (w₀ + w₁ + w₂)

private theorem edge_of_agree (ε : {e : K // 0 < e}) (a b c d e v : K)
    (h₀ : (2*a - 7*b + 11*c) / 6 = v) (h₁ : (-b + 5*c + 2*d) / 6 = v)
    (h₂ : (2*c + 5*d - e) / 6 = v) : edge ε a b c d e = v := by
  simp only [edge, h₀, h₁, h₂, ← add_mul]
  rw [div_eq_iff (ne_of_gt (add_pos (add_pos (weight_pos ε.property one_pos _ _)
    (weight_pos ε.property (by norm_num : (0 : K) < 6) _ _))
    (weight_pos ε.property (by norm_num : (0 : K) < 3) _ _)))]
  exact mul_comm _ _

/-- Exact on quadratic cell averages in unit-width coordinates centered on the owning cell.
Averaging `a*x² + b*x + c` on the cell centered at `j` adds the second moment `a/12`. -/
theorem edge_quadratic (ε : {e : K // 0 < e}) (a b c : K) :
    let mean (j : K) := a*(j^2 + 1/12) + b*j + c
    edge ε (mean (-2)) (mean (-1)) (mean 0) (mean 1) (mean 2) = a/4 + b/2 + c := by
  dsimp only
  apply edge_of_agree <;> ring

end Weno

/-- Left and right WENO-JS5 face traces. The second stencil is centered on the successor and reversed. -/
def wenoJS5 {I : Type*} (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (ε : {e : K // 0 < e}) :
    Reconstruction (Mesh1D.uniform g dx hdx) K where
  traces U i :=
    let j := g.next i
    let l := g.prev i
    let r := g.next j
    (Weno.edge ε (U (g.prev l)) (U l) (U i) (U j) (U r),
     Weno.edge ε (U (g.next r)) (U r) (U j) (U i) (U l))

theorem wenoJS5_constants {I : Type*} (g : Grid I) (dx : ℝ) (hdx : 0 < dx) (ε : {e : K // 0 < e}) :
    (wenoJS5 g dx hdx ε).PreservesConstants := by
  intro c i
  have h := Weno.edge_quadratic ε 0 0 c
  simpa [wenoJS5] using congrArg (fun v => (v, v)) h

end CFDLean.FV1D.Reconstruction
