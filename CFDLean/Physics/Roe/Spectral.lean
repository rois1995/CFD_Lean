import CFDLean.Physics.Roe.Linearization
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Tactic.Module

noncomputable section
namespace CFDLean.Roe.Spectral
open Coordinates PhysicalJacobian
open scoped BigOperators

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

abbrev E := StateCoordinates

def A (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) : Module.End ℝ E :=
  (operator γ u H n).toLinearMap

def shift (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) : Module.End ℝ E :=
  A γ u H n - dot u n • 1

def b (u n : Vector 3) : E →ₗ[ℝ] ℝ :=
  (normalMomentum n - dot u n • projection 0).toLinearMap

def dp (γ : ℝ) (u : Vector 3) : E →ₗ[ℝ] ℝ :=
  ((γ - 1) • (projection 4 -
    (u 0 • projection 1 + u 1 • projection 2 + u 2 • projection 3) +
    (squareSum u / 2) • projection 0)).toLinearMap

def vb (u : Vector 3) (H : ℝ) : E := ![1, u 0, u 1, u 2, H]
def vp (u n : Vector 3) : E := ![0, n 0, n 1, n 2, dot u n]
def acoustic (u : Vector 3) (H : ℝ) (n : Vector 3) (s : ℝ) : E := vb u H + s • vp u n
def contact (u : Vector 3) : E := ![1, u 0, u 1, u 2, squareSum u / 2]
def shear (u t : Vector 3) : E := ![0, t 0, t 1, t 2, dot u t]

def minus (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ) : Module.End ℝ E :=
  (1 / (2 * c ^ 2)) • (shift γ u H n ^ 2 - c • shift γ u H n)
def plus (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ) : Module.End ℝ E :=
  (1 / (2 * c ^ 2)) • (shift γ u H n ^ 2 + c • shift γ u H n)
def zero (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ) : Module.End ℝ E :=
  1 - (1 / c ^ 2) • shift γ u H n ^ 2

def projector (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ) (i : Fin 3) : Module.End ℝ E :=
  ![minus γ u H n c, zero γ u H n c, plus γ u H n c] i

def offset (c : ℝ) (i : Fin 3) : ℝ := ![-c, 0, c] i
def speed (u n : Vector 3) (c : ℝ) (i : Fin 3) : ℝ := dot u n + offset c i

def absolute (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ) : Module.End ℝ E :=
  |speed u n c 0| • minus γ u H n c + |speed u n c 1| • zero γ u H n c +
    |speed u n c 2| • plus γ u H n c

theorem shift_apply (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (v : E) :
    shift γ u H n v = b u n v • vb u H + dp γ u v • vp u n := by
  funext i
  fin_cases i <;> simp [shift, A, operator, assemble_eq_pi, b, dp, vb, vp, projection] <;> ring1

theorem b_vb (u n : Vector 3) (H : ℝ) : b u n (vb u H) = 0 := by
  simp [b, vb, normalMomentum, projection, dot_three]
  ring1

theorem dp_vb (γ : ℝ) (u : Vector 3) (H : ℝ) :
    dp γ u (vb u H) = (γ - 1) * (H - squareSum u / 2) := by
  change (γ - 1) * (H - (u 0 * u 0 + u 1 * u 1 + u 2 * u 2) + squareSum u / 2 * 1) = _
  rw [squareSum_three]
  ring1

theorem b_vp (u n : Vector 3) : b u n (vp u n) = dot n n := by
  simp [b, vp, normalMomentum, projection, dot_three]

theorem dp_vp (γ : ℝ) (u n : Vector 3) : dp γ u (vp u n) = 0 := by
  simp [dp, vp, projection, dot_three]

-- Keep algebraic proofs from unfolding the five-row implementation.
attribute [local irreducible] shift b dp

theorem b_shift (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3)
    (hn : dot n n = 1) (v : E) : b u n (shift γ u H n v) = dp γ u v := by
  rw [shift_apply, map_add, map_smul, map_smul, b_vb, b_vp, hn]
  simp

theorem dp_shift (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (v : E) :
    dp γ u (shift γ u H n v) = (γ - 1) * (H - squareSum u / 2) * b u n v := by
  rw [shift_apply, map_add, map_smul, map_smul, dp_vb, dp_vp]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring1

theorem shift_square_apply (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (v : E) :
    (shift γ u H n ^ 2) v = dp γ u v • vb u H + (c ^ 2 * b u n v) • vp u n := by
  change shift γ u H n (shift γ u H n v) = _
  rw [shift_apply, b_shift γ u H n hn, dp_shift, ← hc]

theorem shifted_cubic (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) :
    shift γ u H n ^ 3 = c ^ 2 • shift γ u H n := by
  apply LinearMap.ext
  intro v
  change shift γ u H n ((shift γ u H n ^ 2) v) = c ^ 2 • shift γ u H n v
  have hb : b u n ((shift γ u H n ^ 2) v) = c ^ 2 * b u n v := by
    change b u n (shift γ u H n (shift γ u H n v)) = _
    rw [b_shift γ u H n hn, dp_shift, ← hc]
  have hp : dp γ u ((shift γ u H n ^ 2) v) = c ^ 2 * dp γ u v := by
    change dp γ u (shift γ u H n (shift γ u H n v)) = _
    rw [dp_shift, b_shift γ u H n hn, ← hc]
  rw [shift_apply, hb, hp, shift_apply]
  module

theorem shifted_acoustic (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (s : ℝ)
    (hn : dot n n = 1) (hs : s ^ 2 = (γ - 1) * (H - squareSum u / 2)) :
    shift γ u H n (acoustic u H n s) = s • acoustic u H n s := by
  rw [shift_apply]
  simp only [acoustic, map_add, map_smul, b_vb, b_vp, dp_vb, dp_vp, hn, ← hs,
    smul_eq_mul, mul_one, mul_zero, zero_add, add_zero]
  module

theorem A_eq_shift (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (v : E) :
    A γ u H n v = dot u n • v + shift γ u H n v := by
  simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self]
  module

theorem acoustic_eigen (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (s : ℝ)
    (hn : dot n n = 1) (hs : s ^ 2 = (γ - 1) * (H - squareSum u / 2)) :
    A γ u H n (acoustic u H n s) = (dot u n + s) • acoustic u H n s := by
  rw [A_eq_shift, shifted_acoustic γ u H n s hn hs]
  module

theorem contact_eigen (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) :
    A γ u H n (contact u) = dot u n • contact u := by
  have hb : b u n (contact u) = 0 := b_vb u n _
  have hp : dp γ u (contact u) = 0 := by rw [show contact u = vb u (squareSum u / 2) from rfl, dp_vb]; ring
  rw [A_eq_shift, shift_apply, hb, hp]
  module

theorem shear_eigen (γ : ℝ) (u : Vector 3) (H : ℝ) (n t : Vector 3) (ht : dot t n = 0) :
    A γ u H n (shear u t) = dot u n • shear u t := by
  have hb : b u n (shear u t) = 0 := by
    simpa [b, shear, normalMomentum, projection, dot_three, mul_comm] using ht
  have hp : dp γ u (shear u t) = 0 := by simp [dp, shear, projection, dot_three]
  rw [A_eq_shift, shift_apply, hb, hp]
  module

theorem minus_apply (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (v : E) :
    minus γ u H n c v = ((dp γ u v - c * b u n v) / (2 * c ^ 2)) • acoustic u H n (-c) := by
  change (1 / (2 * c ^ 2)) • ((shift γ u H n ^ 2) v - c • shift γ u H n v) = _
  rw [shift_square_apply γ u H n c hn hc, shift_apply]
  simp only [acoustic, div_eq_mul_inv]
  module

theorem plus_apply (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (v : E) :
    plus γ u H n c v = ((dp γ u v + c * b u n v) / (2 * c ^ 2)) • acoustic u H n c := by
  change (1 / (2 * c ^ 2)) • ((shift γ u H n ^ 2) v + c • shift γ u H n v) = _
  rw [shift_square_apply γ u H n c hn hc, shift_apply]
  simp only [acoustic, div_eq_mul_inv]
  module

def multiplier (c s : ℝ) (j : Fin 3) : ℝ :=
  ![(s ^ 2 - c * s) / (2 * c ^ 2), 1 - s ^ 2 / c ^ 2,
    (s ^ 2 + c * s) / (2 * c ^ 2)] j

theorem projector_on_eigen (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c s : ℝ)
    (v : E) (hv : shift γ u H n v = s • v) (j : Fin 3) :
    projector γ u H n c j v = multiplier c s j • v := by
  have h2 : (shift γ u H n ^ 2) v = s ^ 2 • v := by
    change shift γ u H n (shift γ u H n v) = _
    rw [hv, map_smul, hv, smul_smul]
    congr 1
    ring1
  fin_cases j
  · change (1 / (2 * c ^ 2)) • ((shift γ u H n ^ 2) v - c • shift γ u H n v) =
      ((s ^ 2 - c * s) / (2 * c ^ 2)) • v
    rw [h2, hv]
    simp only [div_eq_mul_inv]
    module
  · change v - (1 / c ^ 2) • (shift γ u H n ^ 2) v = (1 - s ^ 2 / c ^ 2) • v
    rw [h2]
    simp only [div_eq_mul_inv]
    module
  · change (1 / (2 * c ^ 2)) • ((shift γ u H n ^ 2) v + c • shift γ u H n v) =
      ((s ^ 2 + c * s) / (2 * c ^ 2)) • v
    rw [h2, hv]
    simp only [div_eq_mul_inv]
    module

theorem multiplier_offset (c : ℝ) (hc : c ≠ 0) (i j : Fin 3) :
    multiplier c (offset c i) j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [multiplier, offset] <;> field_simp [hc] <;> norm_num

theorem projector_on_shift_eigen (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hc : c ≠ 0) (i j : Fin 3) (v : E)
    (hv : shift γ u H n v = offset c i • v) :
    projector γ u H n c j v = if i = j then v else 0 := by
  rw [projector_on_eigen γ u H n c (offset c i) v hv j, multiplier_offset c hc i j]
  by_cases h : i = j <;> simp [h]

theorem shift_projector (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hc0 : c ≠ 0)
    (i : Fin 3) (v : E) :
    shift γ u H n (projector γ u H n c i v) = offset c i • projector γ u H n c i v := by
  fin_cases i
  · change shift γ u H n (minus γ u H n c v) = -c • minus γ u H n c v
    rw [minus_apply γ u H n c hn hc, map_smul,
      shifted_acoustic γ u H n (-c) hn (by simpa using hc)]
    module
  · simp only [projector, offset, Matrix.cons_val_zero', Matrix.cons_val_succ', zero_smul]
    change shift γ u H n (v - (1 / c ^ 2) • (shift γ u H n ^ 2) v) = (0 : E)
    rw [map_sub, map_smul]
    have h3 := congrArg (fun f : Module.End ℝ E => f v) (shifted_cubic γ u H n c hn hc)
    change shift γ u H n ((shift γ u H n ^ 2) v) = c ^ 2 • shift γ u H n v at h3
    rw [h3]
    match_scalars
    field_simp [hc0]
    norm_num
  · change shift γ u H n (plus γ u H n c v) = c • plus γ u H n c v
    rw [plus_apply γ u H n c hn hc, map_smul, shifted_acoustic γ u H n c hn hc]
    module

theorem projector_algebra (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hc0 : c ≠ 0)
    (i j : Fin 3) :
    projector γ u H n c i * projector γ u H n c j =
      if i = j then projector γ u H n c i else 0 := by
  apply LinearMap.ext
  intro v
  have h := projector_on_shift_eigen γ u H n c hc0 j i (projector γ u H n c j v)
    (shift_projector γ u H n c hn hc hc0 j v)
  by_cases hij : i = j
  · subst j
    simpa using h
  · simpa [hij, Ne.symm hij] using h

theorem projector_sum (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ) (hc : c ≠ 0) :
    minus γ u H n c + zero γ u H n c + plus γ u H n c = 1 := by
  apply LinearMap.ext
  intro v
  change (1 / (2 * c ^ 2)) • ((shift γ u H n ^ 2) v - c • shift γ u H n v) +
    (v - (1 / c ^ 2) • (shift γ u H n ^ 2) v) +
    (1 / (2 * c ^ 2)) • ((shift γ u H n ^ 2) v + c • shift γ u H n v) = v
  match_scalars <;> field_simp [hc]
  all_goals ring1

theorem spectral_decomposition (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ) (hc : c ≠ 0) :
    A γ u H n = speed u n c 0 • minus γ u H n c + speed u n c 1 • zero γ u H n c +
      speed u n c 2 • plus γ u H n c := by
  apply LinearMap.ext
  intro v
  rw [A_eq_shift]
  simp only [speed, offset, minus, zero, plus, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self]
  match_scalars
  · ring1
  all_goals field_simp [hc]
  all_goals ring1

theorem projector_range (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hc0 : c ≠ 0)
    (i : Fin 3) :
    LinearMap.range (projector γ u H n c i) = Module.End.eigenspace (A γ u H n) (speed u n c i) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    rw [A_eq_shift, shift_projector γ u H n c hn hc hc0]
    unfold speed
    module
  · intro hv
    have he := Module.End.mem_eigenspace_iff.mp hv
    have hs : shift γ u H n v = offset c i • v := by
      simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self]
      rw [he]
      unfold speed
      module
    exact ⟨v, by simpa using projector_on_shift_eigen γ u H n c hc0 i i v hs⟩

theorem acoustic_ne_zero (u : Vector 3) (H : ℝ) (n : Vector 3) (s : ℝ) :
    acoustic u H n s ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [acoustic, vb, vp] at h0

theorem rank_one_range (f : Module.End ℝ E) (r : E) (a : E → ℝ)
    (ha : ∀ v, f v = a v • r) (hr : f r = r) :
    LinearMap.range f = Submodule.span ℝ {r} := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨a w, (ha w).symm⟩
  · apply Submodule.span_le.mpr
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    exact ⟨r, hr⟩

theorem minus_range (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hc0 : c ≠ 0) :
    LinearMap.range (minus γ u H n c) = Submodule.span ℝ {acoustic u H n (-c)} := by
  apply rank_one_range _ _ (fun v => (dp γ u v - c * b u n v) / (2 * c ^ 2))
  · exact minus_apply γ u H n c hn hc
  · have h := projector_on_shift_eigen γ u H n c hc0 0 0 (acoustic u H n (-c))
      (shifted_acoustic γ u H n (-c) hn (by simpa using hc))
    simpa [projector] using h

theorem plus_range (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hc0 : c ≠ 0) :
    LinearMap.range (plus γ u H n c) = Submodule.span ℝ {acoustic u H n c} := by
  apply rank_one_range _ _ (fun v => (dp γ u v + c * b u n v) / (2 * c ^ 2))
  · exact plus_apply γ u H n c hn hc
  · have h := projector_on_shift_eigen γ u H n c hc0 2 2 (acoustic u H n c)
      (shifted_acoustic γ u H n c hn hc)
    simpa [projector] using h

def energy (γ : ℝ) : E := ![0, 0, 0, 0, 1 / (γ - 1)]
def waveMap (γ : ℝ) (u n : Vector 3) : E →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.pi ![b u n, dp γ u]

theorem b_energy (γ : ℝ) (u n : Vector 3) : b u n (energy γ) = 0 := by
  simp [b, energy, normalMomentum, projection]

theorem dp_energy (γ : ℝ) (u : Vector 3) (hg : γ - 1 ≠ 0) : dp γ u (energy γ) = 1 := by
  simp [dp, energy, projection, hg]

theorem waveMap_surjective (γ : ℝ) (u n : Vector 3) (hn : dot n n = 1) (hg : γ - 1 ≠ 0) :
    Function.Surjective (waveMap γ u n) := by
  intro w
  refine ⟨w 0 • vp u n + w 1 • energy γ, ?_⟩
  funext i
  fin_cases i <;> simp [waveMap, map_add, map_smul, b_vp, dp_vp, b_energy, dp_energy γ u hg, hn]

theorem convective_eq_kernel (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (hn : dot n n = 1) :
    Module.End.eigenspace (A γ u H n) (dot u n) = LinearMap.ker (waveMap γ u n) := by
  ext v
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
  constructor
  · intro he
    have hs : shift γ u H n v = 0 := by
      simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, he, sub_self]
    have hb : b u n v = 0 := by
      have h := congrArg (fun w : E => w 0) hs
      rw [shift_apply] at h
      simpa [vb, vp] using h
    have hp : dp γ u v = 0 := by
      have h := b_shift γ u H n hn v
      rw [hs, map_zero] at h
      exact h.symm
    funext i
    fin_cases i <;> simp [waveMap, hb, hp]
  · intro hw
    have hb : b u n v = 0 := congrFun hw 0
    have hp : dp γ u v = 0 := congrFun hw 1
    rw [A_eq_shift, shift_apply, hb, hp]
    module

theorem convective_dimension (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3)
    (hn : dot n n = 1) (hg : γ - 1 ≠ 0) :
    Module.finrank ℝ (Module.End.eigenspace (A γ u H n) (dot u n)) = 3 := by
  rw [convective_eq_kernel γ u H n hn]
  have h := (waveMap γ u n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (waveMap_surjective γ u n hn hg)] at h
  norm_num [E, StateCoordinates, Module.finrank_pi] at h
  omega

theorem eigenspace_dimensions (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hc0 : c ≠ 0)
    (hg : γ - 1 ≠ 0) (i : Fin 3) :
    Module.finrank ℝ (Module.End.eigenspace (A γ u H n) (speed u n c i)) = ![1, 3, 1] i := by
  fin_cases i
  · change Module.finrank ℝ (Module.End.eigenspace (A γ u H n) (speed u n c 0)) = 1
    rw [← projector_range γ u H n c hn hc hc0 0]
    change Module.finrank ℝ (LinearMap.range (minus γ u H n c)) = 1
    rw [minus_range γ u H n c hn hc hc0]
    exact finrank_span_singleton (acoustic_ne_zero u H n (-c))
  · change Module.finrank ℝ (Module.End.eigenspace (A γ u H n) (dot u n + 0)) = 3
    rw [add_zero]
    exact convective_dimension γ u H n hn hg
  · change Module.finrank ℝ (Module.End.eigenspace (A γ u H n) (speed u n c 2)) = 1
    rw [← projector_range γ u H n c hn hc hc0 2]
    change Module.finrank ℝ (LinearMap.range (plus γ u H n c)) = 1
    rw [plus_range γ u H n c hn hc hc0]
    exact finrank_span_singleton (acoustic_ne_zero u H n c)

theorem eigenspaces_span (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hc0 : c ≠ 0) :
    (⨆ i : Fin 3, Module.End.eigenspace (A γ u H n) (speed u n c i)) = ⊤ := by
  apply top_unique
  intro v _
  have hm (i : Fin 3) : projector γ u H n c i v ∈
      ⨆ j : Fin 3, Module.End.eigenspace (A γ u H n) (speed u n c j) := by
    apply Submodule.mem_iSup_of_mem i
    rw [← projector_range γ u H n c hn hc hc0 i]
    exact ⟨v, rfl⟩
  have h := (Submodule.add_mem _ (Submodule.add_mem _ (hm 0) (hm 1)) (hm 2))
  have hs := congrArg (fun f : Module.End ℝ E => f v) (projector_sum γ u H n c hc0)
  change minus γ u H n c v + zero γ u H n c v + plus γ u H n c v = v at hs
  change minus γ u H n c v + zero γ u H n c v + plus γ u H n c v ∈ _ at h
  rwa [hs] at h

theorem speed_injective (u n : Vector 3) (c : ℝ) (hc : 0 < c) :
    Function.Injective (speed u n c) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [speed, offset] at h ⊢ <;> linarith

theorem complete_eigenbasis (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hcpos : 0 < c)
    (hg : γ - 1 ≠ 0) :
    ∃ bas : Module.Basis (Fin 5) ℝ E, ∀ j, ∃ i : Fin 3, A γ u H n (bas j) = speed u n c i • bas j := by
  let spaces := fun i : Fin 3 => Module.End.eigenspace (A γ u H n) (speed u n c i)
  have hi : iSupIndep spaces :=
    (Module.End.eigenspaces_iSupIndep (A γ u H n)).comp (speed_injective u n c hcpos)
  have hs : iSup spaces = ⊤ := eigenspaces_span γ u H n c hn hc (ne_of_gt hcpos)
  have hd := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi hs
  let bs := fun i : Fin 3 => Module.finBasis ℝ (spaces i)
  let index := (Σ i : Fin 3, Fin (Module.finrank ℝ (spaces i)))
  let basis : Module.Basis index ℝ E := hd.collectedBasis bs
  have hcard : Fintype.card index = 5 := by
    simp [index, Fintype.card_sigma, spaces,
      eigenspace_dimensions γ u H n c hn hc (ne_of_gt hcpos) hg, Fin.sum_univ_succ]
  let e : index ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  refine ⟨basis.reindex e, ?_⟩
  intro j
  refine ⟨(e.symm j).1, ?_⟩
  simp only [Module.Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp (hd.collectedBasis_mem bs (e.symm j))

theorem eigenvalue_exhaustive (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c μ : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2))
    (v : E) (hv : v ≠ 0) (he : A γ u H n v = μ • v) :
    ∃ i : Fin 3, μ = speed u n c i := by
  have hN : shift γ u H n v = (μ - dot u n) • v := by
    simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, he]
    module
  have h2 : (shift γ u H n ^ 2) v = (μ - dot u n) ^ 2 • v := by
    change shift γ u H n (shift γ u H n v) = _
    rw [hN, map_smul, hN, smul_smul]
    congr 1
    ring1
  have h3 := congrArg (fun f : Module.End ℝ E => f v) (shifted_cubic γ u H n c hn hc)
  change shift γ u H n ((shift γ u H n ^ 2) v) = c ^ 2 • shift γ u H n v at h3
  rw [h2, map_smul, hN, smul_smul, smul_smul] at h3
  have hz : ((μ - dot u n) * ((μ - dot u n) - c) * ((μ - dot u n) + c)) • v = 0 := by
    calc
      _ = (μ - dot u n) ^ 2 • ((μ - dot u n) • v) - c ^ 2 • ((μ - dot u n) • v) := by module
      _ = 0 := by simpa only [smul_smul, sub_self] using sub_eq_zero.mpr h3
  have hz' : (μ - dot u n) * ((μ - dot u n) - c) * ((μ - dot u n) + c) = 0 :=
    (smul_eq_zero.mp hz).resolve_right hv
  rcases mul_eq_zero.mp hz' with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨1, by simp [speed, offset]; linarith⟩
    · exact ⟨2, by simp [speed, offset]; linarith⟩
  · exact ⟨0, by simp [speed, offset]; linarith⟩

theorem absolute_on_eigen (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c μ : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hc0 : c ≠ 0)
    (v : E) (hv : v ≠ 0) (he : A γ u H n v = μ • v) :
    absolute γ u H n c v = |μ| • v := by
  obtain ⟨i, rfl⟩ := eigenvalue_exhaustive γ u H n c μ hn hc v hv he
  have hN : shift γ u H n v = offset c i • v := by
    simp only [shift, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, he, speed]
    module
  have hp (j : Fin 3) := projector_on_shift_eigen γ u H n c hc0 i j v hN
  change |speed u n c 0| • projector γ u H n c 0 v +
    |speed u n c 1| • projector γ u H n c 1 v +
    |speed u n c 2| • projector γ u H n c 2 v = _
  rw [hp 0, hp 1, hp 2]
  fin_cases i <;> norm_num [speed, offset, Fin.ext_iff]

def diagonal {ι : Type*} (a : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x := fun i => a i * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' r x := by ext i; simp; ring1

theorem absolute_basis_representation {ι : Type*} [Fintype ι]
    (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ)
    (hn : dot n n = 1) (hc : c ^ 2 = (γ - 1) * (H - squareSum u / 2)) (hc0 : c ≠ 0)
    (bas : Module.Basis ι ℝ E) (μ : ι → ℝ) (he : ∀ i, A γ u H n (bas i) = μ i • bas i) :
    absolute γ u H n c = bas.equivFun.symm.toLinearMap.comp
      ((diagonal (fun i => |μ i|)).comp bas.equivFun.toLinearMap) := by
  classical
  apply bas.ext
  intro i
  rw [absolute_on_eigen γ u H n c (μ i) hn hc hc0 (bas i) (bas.ne_zero i) (he i)]
  change |μ i| • bas i = bas.equivFun.symm (diagonal (fun j => |μ j|) (bas.equivFun (bas i)))
  apply bas.equivFun.injective
  rw [map_smul, bas.equivFun.apply_symm_apply]
  funext j
  by_cases h : i = j
  · subst j; simp [diagonal]
  · simp [diagonal, h]

def normal (n : Vector 3) : Vector 3 →ₗ[ℝ] ℝ where
  toFun t := dot t n
  map_add' t s := by simp [dot_three]; ring1
  map_smul' r t := by simp [dot_three]; ring1

def tangent (n : Vector 3) : Submodule ℝ (Vector 3) := LinearMap.ker (normal n)

def shearMap (u : Vector 3) : Vector 3 →ₗ[ℝ] E where
  toFun := shear u
  map_add' t s := by ext i; fin_cases i <;> simp [shear, dot_three]; ring1
  map_smul' r t := by ext i; fin_cases i <;> simp [shear, dot_three]; ring1

theorem normal_surjective (n : Vector 3) (hn : dot n n = 1) : Function.Surjective (normal n) := by
  intro r
  refine ⟨r • n, ?_⟩
  change dot (r • n) n = r
  calc
    _ = r * dot n n := by simp [dot_three]; ring1
    _ = r := by rw [hn, mul_one]

theorem tangent_dimension (n : Vector 3) (hn : dot n n = 1) : Module.finrank ℝ (tangent n) = 2 := by
  have h := (normal n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (normal_surjective n hn)] at h
  norm_num [Vector, Module.finrank_pi] at h
  change Module.finrank ℝ (LinearMap.ker (normal n)) = 2
  omega

noncomputable def tangentBasis (n : Vector 3) (hn : dot n n = 1) : Module.Basis (Fin 2) ℝ (tangent n) :=
  Module.finBasisOfFinrankEq ℝ _ (tangent_dimension n hn)

theorem convective_decomposition (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3)
    (hn : dot n n = 1) (hg : γ - 1 ≠ 0) (v : E)
    (hv : v ∈ Module.End.eigenspace (A γ u H n) (dot u n)) :
    ∃ t : Vector 3, dot t n = 0 ∧ v = v 0 • contact u + shear u t := by
  have hw : waveMap γ u n v = 0 := by
    rw [← LinearMap.mem_ker, ← convective_eq_kernel γ u H n hn]
    exact hv
  have hb : b u n v = 0 := congrFun hw 0
  have hp : dp γ u v = 0 := congrFun hw 1
  unfold dp at hp
  change (γ - 1) * (v 4 - (u 0 * v 1 + u 1 * v 2 + u 2 * v 3) + squareSum u / 2 * v 0) = 0 at hp
  have ht := (mul_eq_zero.mp hp).resolve_left hg
  let t : Vector 3 := ![v 1 - v 0 * u 0, v 2 - v 0 * u 1, v 3 - v 0 * u 2]
  refine ⟨t, ?_, ?_⟩
  · have h : dot t n = b u n v := by
      simp [t, b, normalMomentum, projection, dot_three]
      ring1
    rw [h, hb]
  · simp only [squareSum_three] at ht
    funext i
    fin_cases i <;> simp [t, contact, shear, dot_three, squareSum_three]
    nlinarith [ht]

theorem convective_tangent_span (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3)
    (hn : dot n n = 1) (hg : γ - 1 ≠ 0) (tb : Module.Basis (Fin 2) ℝ (tangent n)) :
    Submodule.span ℝ ({contact u} ∪ Set.range (fun i => shear u (tb i))) =
      Module.End.eigenspace (A γ u H n) (dot u n) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with h | ⟨i, rfl⟩
    · rw [Set.mem_singleton_iff] at h
      subst v
      exact Module.End.mem_eigenspace_iff.mpr (contact_eigen γ u H n)
    · apply Module.End.mem_eigenspace_iff.mpr
      exact shear_eigen γ u H n _ (tb i).property
  · intro v hv
    obtain ⟨t, ht, he⟩ := convective_decomposition γ u H n hn hg v hv
    let tt : tangent n := ⟨t, ht⟩
    have ht' : t = tb.repr tt 0 • (tb 0 : Vector 3) + tb.repr tt 1 • (tb 1 : Vector 3) := by
      have h := congrArg (fun w : tangent n => (w : Vector 3)) (tb.sum_repr tt)
      simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul] at h
      exact h.symm
    have hs : shear u t = tb.repr tt 0 • shear u (tb 0) + tb.repr tt 1 • shear u (tb 1) := by
      change shearMap u t = _
      rw [ht', map_add, map_smul, map_smul]
      rfl
    rw [he, hs]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl))
    · exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨0, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨1, rfl⟩)))

theorem dot_reverse (u n : Vector 3) : dot u (-n) = -dot u n := by
  have h := dot_mul u n (-1)
  simp only [neg_one_mul] at h
  exact h

theorem A_reverse (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) : A γ u H (-n) = -A γ u H n := by
  unfold A
  apply LinearMap.ext
  intro v
  funext i
  have h := congrArg (fun f : E →L[ℝ] E => f v i) (operator_smul γ u H (-1) n)
  change operator γ u H (-n) v i = -(operator γ u H n v i)
  change operator γ u H (fun j => (-1 : ℝ) * n j) v i = (-1 : ℝ) * operator γ u H n v i at h
  simp only [neg_one_mul] at h
  exact h

theorem shift_reverse (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) :
    shift γ u H (-n) = -shift γ u H n := by
  simp only [shift, A_reverse, dot_reverse]
  module

theorem speed_reverse (u n : Vector 3) (c : ℝ) (i : Fin 3) :
    speed u (-n) c i = -speed u n c i.rev := by
  fin_cases i <;> simp [speed, offset, dot_reverse] <;> ring1

theorem neg_square (f : Module.End ℝ E) : (-f) ^ 2 = f ^ 2 := by
  apply LinearMap.ext
  intro v
  change -(f (-f v)) = f (f v)
  rw [map_neg, neg_neg]

theorem projector_reverse (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ) (i : Fin 3) :
    projector γ u H (-n) c i = projector γ u H n c i.rev := by
  fin_cases i
  · change minus γ u H (-n) c = plus γ u H n c
    simp only [minus, plus, shift_reverse, neg_square, smul_neg, sub_eq_add_neg, neg_neg]
  · change zero γ u H (-n) c = zero γ u H n c
    simp only [zero, shift_reverse, neg_square]
  · change plus γ u H (-n) c = minus γ u H n c
    simp only [plus, minus, shift_reverse, neg_square, smul_neg, sub_eq_add_neg]

theorem absolute_reverse (γ : ℝ) (u : Vector 3) (H : ℝ) (n : Vector 3) (c : ℝ) :
    absolute γ u H (-n) c = absolute γ u H n c := by
  have hm : minus γ u H (-n) c = plus γ u H n c := projector_reverse γ u H n c 0
  have hz : zero γ u H (-n) c = zero γ u H n c := projector_reverse γ u H n c 1
  have hp : plus γ u H (-n) c = minus γ u H n c := projector_reverse γ u H n c 2
  have hs0 : speed u (-n) c 0 = -speed u n c 2 := speed_reverse u n c 0
  have hs1 : speed u (-n) c 1 = -speed u n c 1 := speed_reverse u n c 1
  have hs2 : speed u (-n) c 2 = -speed u n c 0 := speed_reverse u n c 2
  unfold absolute
  rw [hm, hz, hp, hs0, hs1, hs2]
  simp only [abs_neg]
  module

def roeShift (γ : ℝ) (x y : E) (n : Vector 3) : Module.End ℝ E :=
  shift γ (averageVelocity x y) (averageEnthalpy γ x y) n

def roeProjector (γ : ℝ) (x y : E) (n : Vector 3) (i : Fin 3) : Module.End ℝ E :=
  projector γ (averageVelocity x y) (averageEnthalpy γ x y) n (soundSpeed γ x y) i

def roeSpeed (γ : ℝ) (x y : E) (n : Vector 3) (i : Fin 3) : ℝ :=
  speed (averageVelocity x y) n (soundSpeed γ x y) i

def dissipation (γ : ℝ) (x y : E) (n : Vector 3) : Module.End ℝ E :=
  absolute γ (averageVelocity x y) (averageEnthalpy γ x y) n (soundSpeed γ x y)


theorem sound_parameters (γ : ℝ) (x y : E) (hγ : 1 < γ)
    (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) :
    0 < soundSpeed γ x y ∧ soundSpeed γ x y ^ 2 =
      (γ - 1) * (averageEnthalpy γ x y - squareSum (averageVelocity x y) / 2) :=
  ⟨soundSpeed_pos γ x y hγ hx hy, soundSpeed_sq γ x y hγ hx hy⟩

section Physical
variable (γ : ℝ) (x y : E) (n : Vector 3) (hγ : 1 < γ)
  (hx : (decode x).Admissible γ) (hy : (decode y).Admissible γ) (hn : dot n n = 1)
include hγ hx hy hn

theorem roe_cubic : roeShift γ x y n ^ 3 = soundSpeed γ x y ^ 2 • roeShift γ x y n :=
  shifted_cubic γ _ _ n _ hn (sound_parameters γ x y hγ hx hy).2

theorem roe_eigenvectors :
    (∀ s : ℝ, s = -soundSpeed γ x y ∨ s = soundSpeed γ x y →
      roeMatrix γ x y n (acoustic (averageVelocity x y) (averageEnthalpy γ x y) n s) =
        (dot (averageVelocity x y) n + s) •
          acoustic (averageVelocity x y) (averageEnthalpy γ x y) n s) ∧
    roeMatrix γ x y n (contact (averageVelocity x y)) =
      dot (averageVelocity x y) n • contact (averageVelocity x y) ∧
    (∀ t : Vector 3, dot t n = 0 → roeMatrix γ x y n (shear (averageVelocity x y) t) =
      dot (averageVelocity x y) n • shear (averageVelocity x y) t) := by
  refine ⟨?_, contact_eigen γ _ _ n, ?_⟩
  · intro s hs
    apply acoustic_eigen γ _ _ n s hn
    rcases hs with rfl | rfl
    · simpa using (sound_parameters γ x y hγ hx hy).2
    · exact (sound_parameters γ x y hγ hx hy).2
  · intro t ht
    exact shear_eigen γ _ _ n t ht

theorem roe_projector_algebra (i j : Fin 3) :
    roeProjector γ x y n i * roeProjector γ x y n j =
      if i = j then roeProjector γ x y n i else 0 :=
  projector_algebra γ _ _ n _ hn (sound_parameters γ x y hγ hx hy).2
    (ne_of_gt (sound_parameters γ x y hγ hx hy).1) i j

omit hn in
theorem roe_projector_sum :
    roeProjector γ x y n 0 + roeProjector γ x y n 1 + roeProjector γ x y n 2 = 1 :=
  projector_sum γ _ _ n _ (ne_of_gt (sound_parameters γ x y hγ hx hy).1)

theorem roe_projector_ranges (i : Fin 3) :
    LinearMap.range (roeProjector γ x y n i) =
      Module.End.eigenspace (roeMatrix γ x y n).toLinearMap (roeSpeed γ x y n i) :=
  projector_range γ _ _ n _ hn (sound_parameters γ x y hγ hx hy).2
    (ne_of_gt (sound_parameters γ x y hγ hx hy).1) i

theorem roe_dimensions (i : Fin 3) :
    Module.finrank ℝ (Module.End.eigenspace (roeMatrix γ x y n).toLinearMap (roeSpeed γ x y n i)) =
      ![1, 3, 1] i :=
  eigenspace_dimensions γ _ _ n _ hn (sound_parameters γ x y hγ hx hy).2
    (ne_of_gt (sound_parameters γ x y hγ hx hy).1) (ne_of_gt (sub_pos.mpr hγ)) i

theorem roe_projector_ranks (i : Fin 3) :
    Module.finrank ℝ (LinearMap.range (roeProjector γ x y n i)) = ![1, 3, 1] i := by
  rw [roe_projector_ranges γ x y n hγ hx hy hn]
  exact roe_dimensions γ x y n hγ hx hy hn i

theorem roe_complete_basis :
    ∃ bas : Module.Basis (Fin 5) ℝ E, ∀ j, ∃ i : Fin 3, roeMatrix γ x y n (bas j) = roeSpeed γ x y n i • bas j :=
  complete_eigenbasis γ _ _ n _ hn (sound_parameters γ x y hγ hx hy).2
    (sound_parameters γ x y hγ hx hy).1 (ne_of_gt (sub_pos.mpr hγ))

omit hn in
theorem roe_spectral_decomposition :
    (roeMatrix γ x y n).toLinearMap = roeSpeed γ x y n 0 • roeProjector γ x y n 0 +
      roeSpeed γ x y n 1 • roeProjector γ x y n 1 + roeSpeed γ x y n 2 • roeProjector γ x y n 2 :=
  spectral_decomposition γ _ _ n _ (ne_of_gt (sound_parameters γ x y hγ hx hy).1)

omit hx hy in
theorem roe_convective_tangent_span (tb : Module.Basis (Fin 2) ℝ (tangent n)) :
    Submodule.span ℝ ({contact (averageVelocity x y)} ∪
      Set.range (fun i => shear (averageVelocity x y) (tb i))) =
      Module.End.eigenspace (roeMatrix γ x y n).toLinearMap (dot (averageVelocity x y) n) :=
  convective_tangent_span γ _ _ n hn (ne_of_gt (sub_pos.mpr hγ)) tb

theorem roe_absolute_basis {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ E) (μ : ι → ℝ)
    (he : ∀ i, roeMatrix γ x y n (bas i) = μ i • bas i) :
    dissipation γ x y n = bas.equivFun.symm.toLinearMap.comp
      ((diagonal (fun i => |μ i|)).comp bas.equivFun.toLinearMap) :=
  absolute_basis_representation γ _ _ n _ hn (sound_parameters γ x y hγ hx hy).2
    (ne_of_gt (sound_parameters γ x y hγ hx hy).1) bas μ he

theorem roe_absolute_eigen (μ : ℝ) (v : E) (hv : v ≠ 0)
    (he : roeMatrix γ x y n v = μ • v) : dissipation γ x y n v = |μ| • v :=
  absolute_on_eigen γ _ _ n _ μ hn (sound_parameters γ x y hγ hx hy).2
    (ne_of_gt (sound_parameters γ x y hγ hx hy).1) v hv he

end Physical

theorem exists_tangent_basis (n : Vector 3) (hn : dot n n = 1) :
    Nonempty (Module.Basis (Fin 2) ℝ (tangent n)) := ⟨tangentBasis n hn⟩

theorem roe_matrix_reverse (γ : ℝ) (x y : E) (n : Vector 3) :
    roeMatrix γ x y (-n) = -roeMatrix γ x y n := by
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun f : Module.End ℝ E => f v) (A_reverse γ _ _ n)

theorem roe_shift_reverse (γ : ℝ) (x y : E) (n : Vector 3) :
    roeShift γ x y (-n) = -roeShift γ x y n := shift_reverse γ _ _ n

theorem roe_projector_reverse (γ : ℝ) (x y : E) (n : Vector 3) (i : Fin 3) :
    roeProjector γ x y (-n) i = roeProjector γ x y n i.rev := projector_reverse γ _ _ n _ i

theorem roe_speed_reverse (γ : ℝ) (x y : E) (n : Vector 3) (i : Fin 3) :
    roeSpeed γ x y (-n) i = -roeSpeed γ x y n i.rev := speed_reverse _ n _ i

theorem roe_absolute_reverse (γ : ℝ) (x y : E) (n : Vector 3) :
    dissipation γ x y (-n) = dissipation γ x y n := absolute_reverse γ _ _ n _

theorem roe_swap (γ : ℝ) (x y : E) (n : Vector 3) :
    roeShift γ y x n = roeShift γ x y n ∧
    (∀ i, roeProjector γ y x n i = roeProjector γ x y n i) ∧
    dissipation γ y x n = dissipation γ x y n := by
  have hv := (averages_swap γ x y).1
  have hH := (averages_swap γ x y).2.1
  have hc : soundSpeed γ y x = soundSpeed γ x y := by
    unfold soundSpeed
    rw [(averages_swap γ x y).2.2]
  simp [roeShift, roeProjector, dissipation, hv, hH, hc]

end CFDLean.Roe.Spectral
