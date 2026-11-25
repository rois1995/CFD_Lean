import CFDLean.Papers.JST1.Proofs.Closure
import CFDLean.Papers.JST1.Proofs.DissGeom
import CFDLean.Papers.JST1.Proofs.Viscous
import CFDLean.Papers.JST1.Spec.Item6
import CFDLean.Discrete.Mesh
import CFDLean.Geometry.MeshBoundary
import CFDLean.Entropy.PairFlux
import CFDLean.Discrete.Galerkin

/-! Proofs of item 6 (P2): `prop:sbp`, boundary facets, `lem:bdefect`, `prop:consistency`(b). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
set_option linter.unusedSectionVars false
namespace CFDLean.JST1.Proofs

theorem p2_6_3 : Spec.P2_6_3 := CFDLean.Num.WMesh.conforming_boundary

theorem p2_6_1 : Spec.P2_6_1 := CFDLean.Num.WMesh.sbp_defect

theorem p2_6_2 : Spec.P2_6_2 := CFDLean.Num.Simplex.median_defect_iff

theorem p2_6_4 : Spec.P2_6_4 := CFDLean.Num.edgeForm_boundary_split

namespace Sbp6

theorem prim_pressure {d : ℕ} (g : Gas) (r : ℝ) (_hr : 0 < r) (v : Vec d) (p : ℝ) :
    pressure g (primState g r v p) = p := by
  have hg : g.γ - 1 ≠ 0 := by have := g.one_lt_γ; linarith
  simp only [pressure, primState, energy, mom, rho, Num.dot]
  have : (∑ x, r * v x * (r * v x)) = r * (r * ∑ x, v x * v x) := by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  field_simp
  ring

end Sbp6

open Sbp6

theorem p2_6_5 : Spec.P2_6_5 := CFDLean.Num.WMesh.standardClosure_entropy

theorem p2_6_5b : Spec.P2_6_5b := CFDLean.Num.WMesh.standardClosure_linear

theorem p2_6_6 : Spec.P2_6_6 := by
  intro d g y hd hy
  have hyy : 0 < Num.dot y y := by
    rcases (DissGeom.dot_self_nonneg y).lt_or_eq with h | h
    · exact h
    · exact absurd (DissGeom.eq_zero_of_dot_self y h.symm) hy
  let U : ℝ → ℝ → State d := fun t p => primState g 1 (t • y) p
  have hadm : ∀ t p, 0 < p → Admissible g (U t p) := fun t p hp =>
    ⟨by simp [U, rho, primState], by rw [prim_pressure g 1 one_pos]; exact hp⟩
  have key : ∀ t1 p1 t2 p2, 0 < p1 → 0 < p2 →
      pairF (entropyVars g (U t2 p2) - entropyVars g (U t1 p1))
        (pressFlux g (U t2 p2) y - pressFlux g (U t1 p1) y) = (t2 / p2 - t1 / p1) * (p2 - p1) * Num.dot y y := by
    intro t1 p1 t2 p2 h1 h2
    unfold pairF
    rw [sum_channel]
    have hm : ∀ t p α, 0 < p → entropyVars g (U t p) (.momentum α) = t * y α / p := by
      intro t p α hp
      show rho (U t p) * vel (U t p) α / pressure g (U t p) = _
      rw [prim_pressure g 1 one_pos]
      simp [U, rho, vel, mom, primState]
    have hpf : ∀ t p α, 0 < p → pressFlux g (U t p) y (.momentum α) = p * y α := by
      intro t p α hp
      show pressure g (U t p) * y α = _
      rw [prim_pressure g 1 one_pos]
    simp only [Pi.sub_apply, hm _ _ _ h1, hm _ _ _ h2, hpf _ _ _ h1, hpf _ _ _ h2]
    simp only [pressFlux, sub_self, mul_zero, zero_add, add_zero, Num.dot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    field_simp
  refine ⟨⟨U 0 1, U 1 2, hadm _ _ one_pos, hadm _ _ two_pos, ?_⟩,
    ⟨U 0 1, U (-1) 2, hadm _ _ one_pos, hadm _ _ two_pos, ?_⟩⟩
  · rw [key _ _ _ _ one_pos two_pos]; nlinarith
  · rw [key _ _ _ _ one_pos two_pos]; nlinarith

theorem p2_6_7 : Spec.P2_6_7 := CFDLean.Num.WMesh.closed_mean_galerkin

end CFDLean.JST1.Proofs
