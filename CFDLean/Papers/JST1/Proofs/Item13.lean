import CFDLean.Papers.JST1.Spec.Item13
import CFDLean.Papers.JST1.Proofs.Item1
import CFDLean.Papers.JST1.Proofs.Item8
import CFDLean.Entropy.Production

/-! Proofs of item 13 (P3): `prop:defect` (paper lines 162-168, proof 897-907). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology

namespace CFDLean.JST1.Proofs
namespace Def13

/-! ### P3-13.2: an acoustic path in primitive variables -/

section
variable {d : ℕ}

theorem sum_lin (v E : Vec d) (x y z u : ℝ) :
    ∑ α, (x * v α + y * E α) * (z * v α + u * E α) =
      x * z * Num.dot v v + (x * u + y * z) * Num.dot v E + y * u * Num.dot E E := by
  simp only [Num.dot, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by ring

theorem dot_V (v E : Vec d) (k t : ℝ) :
    Num.dot (fun α => v α + t * (k * E α)) (fun α => v α + t * (k * E α)) =
      Num.dot v v + t * (2 * k * Num.dot v E) + t ^ 2 * (k ^ 2 * Num.dot E E) := by
  simp only [Num.dot, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by ring

theorem dot_VE (v E : Vec d) (k t : ℝ) :
    Num.dot (fun α => v α + t * (k * E α)) E = Num.dot v E + t * (k * Num.dot E E) := by
  simp only [Num.dot, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- The path `ρ(t) = ρ₀(1+t)`, `v(t) = v₀ + t k E`, `p(t) = p₀(1+γt)` (isentropic to first order). -/
def path (g : Gas) (r0 : ℝ) (v E : Vec d) (p0 k t : ℝ) : State d :=
  primState g (r0 * (1 + t)) (fun α => v α + t * (k * E α)) (p0 * (1 + g.γ * t))

variable (g : Gas) (r0 : ℝ) (v E : Vec d) (p0 k : ℝ)

theorem rho_path (t : ℝ) : rho (path g r0 v E p0 k t) = r0 * (1 + t) := rfl

theorem vel_path {t : ℝ} (h : r0 * (1 + t) ≠ 0) :
    vel (path g r0 v E p0 k t) = fun α => v α + t * (k * E α) :=
  Cl8.vel_prim g h _ _

theorem pressure_path {t : ℝ} (h : r0 * (1 + t) ≠ 0) :
    pressure g (path g r0 v E p0 k t) = p0 * (1 + g.γ * t) :=
  Cl8.pressure_prim g h _ _

theorem mom_path (t : ℝ) (α : Fin d) :
    mom (path g r0 v E p0 k t) α = r0 * (1 + t) * (v α + t * (k * E α)) := rfl

theorem energy_path (t : ℝ) :
    energy (path g r0 v E p0 k t) = p0 * (1 + g.γ * t) / (g.γ - 1) +
      r0 * (1 + t) * (Num.dot v v + t * (2 * k * Num.dot v E) + t ^ 2 * (k ^ 2 * Num.dot E E)) / 2 := by
  rw [← dot_V]; rfl

theorem dotmom_path (t : ℝ) :
    Num.dot (mom (path g r0 v E p0 k t)) E = r0 * (1 + t) * (Num.dot v E + t * (k * Num.dot E E)) := by
  rw [← dot_VE]
  simp only [Num.dot, mom_path, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- Derivative of the entropy variables along the path at `t = 0`. -/
def dW (γ r0 p0 A vn k : ℝ) (v E : Vec d) : State d
  | .mass => -(r0 * ((1 - γ) * A + 2 * k * vn)) / (2 * p0)
  | .momentum α => r0 * (1 - γ) / p0 * v α + r0 * k / p0 * E α
  | .energy => -(r0 * (1 - γ)) / p0

/-- Derivative of the flux `F·E` along the path at `t = 0`. -/
def dF (γ r0 p0 A vn L2 k : ℝ) (v E : Vec d) : State d
  | .mass => r0 * (vn + k * L2)
  | .momentum α => (r0 * vn + r0 * k * L2) * v α + (r0 * k * vn + p0 * γ) * E α
  | .energy => (p0 * γ / (γ - 1) + r0 * A / 2 + r0 * k * vn + p0 * γ) * vn +
      (p0 / (γ - 1) + r0 * A / 2 + p0) * (k * L2)

theorem hR : HasDerivAt (fun t : ℝ => r0 * (1 + t)) r0 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).const_add 1).const_mul r0

theorem hP : HasDerivAt (fun t : ℝ => p0 * (1 + g.γ * t)) (p0 * g.γ) 0 := by
  simpa using (((hasDerivAt_id' (0 : ℝ)).const_mul g.γ).const_add 1).const_mul p0

theorem hD (A B C : ℝ) : HasDerivAt (fun t : ℝ => A + t * B + t ^ 2 * C) B 0 := by
  have := (((hasDerivAt_id' (0 : ℝ)).mul_const B).const_add A).fun_add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const C)
  simpa using this

theorem hN (A B : ℝ) : HasDerivAt (fun t : ℝ => A + t * B) B 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const B).const_add A

theorem ev_ne (hr : r0 ≠ 0) : ∀ᶠ t in 𝓝 (0 : ℝ), r0 * (1 + t) ≠ 0 :=
  (hR r0).continuousAt.eventually_ne (by simpa using hr)

theorem hw_mass (hr : r0 ≠ 0) (hp : p0 ≠ 0) :
    HasDerivAt (fun t => entropyVars g (path g r0 v E p0 k t) .mass)
      (dW g.γ r0 p0 (Num.dot v v) (Num.dot v E) k v E .mass) 0 := by
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  have h1 := (((((hP g p0).log (by simpa using hp)).fun_sub
    (((hR r0).log (by simpa using hr)).const_mul g.γ)).const_sub g.γ).div_const (g.γ - 1)).fun_sub
    (((hR r0).fun_mul (hD (Num.dot v v) (2 * k * Num.dot v E) (k ^ 2 * Num.dot E E))).fun_div ((hP g p0).const_mul 2)
      (by simpa using hp))
  refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [dW]
    field_simp
    ring
  · filter_upwards [ev_ne r0 hr] with t ht
    simp only [entropyVars, physEntropy, rho_path, vel_path g r0 v E p0 k ht, pressure_path g r0 v E p0 k ht,
      dot_V]

theorem hw_mom (hr : r0 ≠ 0) (hp : p0 ≠ 0) (α : Fin d) :
    HasDerivAt (fun t => entropyVars g (path g r0 v E p0 k t) (.momentum α))
      (dW g.γ r0 p0 (Num.dot v v) (Num.dot v E) k v E (.momentum α)) 0 := by
  have h1 := ((hR r0).fun_mul (hN (v α) (k * E α))).fun_div (hP g p0) (by simpa using hp)
  refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [dW]
    field_simp
    ring
  · filter_upwards [ev_ne r0 hr] with t ht
    simp only [entropyVars, rho_path, vel_path g r0 v E p0 k ht, pressure_path g r0 v E p0 k ht]

theorem hw_en (hr : r0 ≠ 0) (hp : p0 ≠ 0) :
    HasDerivAt (fun t => entropyVars g (path g r0 v E p0 k t) .energy)
      (dW g.γ r0 p0 (Num.dot v v) (Num.dot v E) k v E .energy) 0 := by
  have h1 := ((hR r0).fun_div (hP g p0) (by simpa using hp)).fun_neg
  refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [dW]
    field_simp
    ring
  · filter_upwards [ev_ne r0 hr] with t ht
    simp only [entropyVars, rho_path, pressure_path g r0 v E p0 k ht, neg_div]

theorem hf_mass :
    HasDerivAt (fun t => physFlux g (path g r0 v E p0 k t) E .mass)
      (dF g.γ r0 p0 (Num.dot v v) (Num.dot v E) (Num.dot E E) k v E .mass) 0 := by
  have h1 := (hR r0).fun_mul (hN (Num.dot v E) (k * Num.dot E E))
  refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [dF]
    ring
  · filter_upwards with t
    simp only [physFlux, dotmom_path]

theorem hf_mom (hr : r0 ≠ 0) (α : Fin d) :
    HasDerivAt (fun t => physFlux g (path g r0 v E p0 k t) E (.momentum α))
      (dF g.γ r0 p0 (Num.dot v v) (Num.dot v E) (Num.dot E E) k v E (.momentum α)) 0 := by
  have h1 := (((hR r0).fun_mul (hN (v α) (k * E α))).fun_mul (hN (Num.dot v E) (k * Num.dot E E))).fun_add
    ((hP g p0).mul_const (E α))
  refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [dF]
    ring
  · filter_upwards [ev_ne r0 hr] with t ht
    simp only [physFlux, mom_path, vel_path g r0 v E p0 k ht, pressure_path g r0 v E p0 k ht, dot_VE]

theorem hf_en (hr : r0 ≠ 0) :
    HasDerivAt (fun t => physFlux g (path g r0 v E p0 k t) E .energy)
      (dF g.γ r0 p0 (Num.dot v v) (Num.dot v E) (Num.dot E E) k v E .energy) 0 := by
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  have h1 := ((((hP g p0).div_const (g.γ - 1)).fun_add
    (((hR r0).fun_mul (hD (Num.dot v v) (2 * k * Num.dot v E) (k ^ 2 * Num.dot E E))).div_const 2)).fun_add (hP g p0)).fun_mul
    (hN (Num.dot v E) (k * Num.dot E E))
  refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [dF]
    ring
  · filter_upwards [ev_ne r0 hr] with t ht
    simp only [physFlux, energy_path, vel_path g r0 v E p0 k ht, pressure_path g r0 v E p0 k ht, dot_VE]

theorem hw_all (hr : r0 ≠ 0) (hp : p0 ≠ 0) (c : Channel d) :
    HasDerivAt (fun t => entropyVars g (path g r0 v E p0 k t) c)
      (dW g.γ r0 p0 (Num.dot v v) (Num.dot v E) k v E c) 0 := by
  cases c with
  | mass => exact hw_mass g r0 v E p0 k hr hp
  | momentum α => exact hw_mom g r0 v E p0 k hr hp α
  | energy => exact hw_en g r0 v E p0 k hr hp

theorem hf_all (hr : r0 ≠ 0) (c : Channel d) :
    HasDerivAt (fun t => physFlux g (path g r0 v E p0 k t) E c)
      (dF g.γ r0 p0 (Num.dot v v) (Num.dot v E) (Num.dot E E) k v E c) 0 := by
  cases c with
  | mass => exact hf_mass g r0 v E p0 k
  | momentum α => exact hf_mom g r0 v E p0 k hr α
  | energy => exact hf_en g r0 v E p0 k hr

/-- The second variation: `(Dw r)·(A r) = ρ(γ v·E + (ρ/p) k²|E|² v·E + 2γ k|E|²)`. -/
theorem Q_eq (hp : p0 ≠ 0) :
    pairF (dW g.γ r0 p0 (Num.dot v v) (Num.dot v E) k v E) (dF g.γ r0 p0 (Num.dot v v) (Num.dot v E) (Num.dot E E) k v E) =
      r0 * (g.γ * Num.dot v E + r0 / p0 * k ^ 2 * Num.dot E E * Num.dot v E + 2 * g.γ * k * Num.dot E E) := by
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  rw [e1_pairF_channel]
  simp only [dW, dF]
  rw [sum_lin]
  field_simp
  ring

end

theorem slope_prod {ι : Type} [Fintype ι] (f h : ι → ℝ → ℝ) (f' h' : ι → ℝ)
    (hf : ∀ i, HasDerivAt (f i) (f' i) 0) (hh : ∀ i, HasDerivAt (h i) (h' i) 0) :
    Tendsto (fun t => (∑ i, (f i t - f i 0) * (h i t - h i 0)) / t ^ 2) (𝓝[≠] 0) (𝓝 (∑ i, f' i * h' i)) := by
  have hl : Tendsto (fun t => ∑ i, slope (f i) 0 t * slope (h i) 0 t) (𝓝[≠] 0) (𝓝 (∑ i, f' i * h' i)) :=
    tendsto_finsetSum _ fun i _ =>
      (hasDerivAt_iff_tendsto_slope.1 (hf i)).mul (hasDerivAt_iff_tendsto_slope.1 (hh i))
  refine hl.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  have ht' : t ≠ 0 := ht
  simp only [slope_def_field, sub_zero, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem path_cont {d : ℕ} (g : Gas) (r0 : ℝ) (v E : Vec d) (p0 k : ℝ) :
    Continuous fun t => path g r0 v E p0 k t := by
  refine continuous_pi fun c => ?_
  cases c with
  | mass => show Continuous fun t : ℝ => r0 * (1 + t); fun_prop
  | momentum α => show Continuous fun t : ℝ => r0 * (1 + t) * (v α + t * (k * E α)); fun_prop
  | energy =>
    have : (fun t => path g r0 v E p0 k t .energy) = fun t => p0 * (1 + g.γ * t) / (g.γ - 1) +
        r0 * (1 + t) * (Num.dot v v + t * (2 * k * Num.dot v E) + t ^ 2 * (k ^ 2 * Num.dot E E)) / 2 :=
      funext fun t => energy_path g r0 v E p0 k t
    rw [this]
    fun_prop

/-- Along the path, states arbitrarily close to `U` are admissible with `P(t)/t²` in any open
neighbourhood of the second variation. -/
theorem exists_near {d : ℕ} (g : Gas) (U : State d) (E : Vec d) (hU : Admissible g U) (k : ℝ) {ε : ℝ} (hε : 0 < ε)
    {S : Set ℝ} (hS : IsOpen S)
    (hQ : rho U * (g.γ * Num.dot (vel U) E + rho U / pressure g U * k ^ 2 * Num.dot E E * Num.dot (vel U) E +
      2 * g.γ * k * Num.dot E E) ∈ S) :
    ∃ t : ℝ, t ≠ 0 ∧ Admissible g (path g (rho U) (vel U) E (pressure g U) k t) ∧
      ‖path g (rho U) (vel U) E (pressure g U) k t - U‖ < ε ∧
      pairF (entropyVars g (path g (rho U) (vel U) E (pressure g U) k t) - entropyVars g U)
        (physFlux g (path g (rho U) (vel U) E (pressure g U) k t) E - physFlux g U E) / t ^ 2 ∈ S := by
  have hr : rho U ≠ 0 := hU.1.ne'
  have hp : pressure g U ≠ 0 := hU.2.ne'
  set γt := fun t => path g (rho U) (vel U) E (pressure g U) k t with hγt
  have h0 : γt 0 = U := by
    refine Eq.trans ?_ (Cl8.eq_prim g hr).symm
    simp [γt, path]
  have hlim := slope_prod (fun c t => entropyVars g (γt t) c) (fun c t => physFlux g (γt t) E c) _ _
    (hw_all g (rho U) (vel U) E (pressure g U) k hr hp) (hf_all g (rho U) (vel U) E (pressure g U) k hr)
  have hQ' : (∑ c, dW g.γ (rho U) (pressure g U) (Num.dot (vel U) (vel U)) (Num.dot (vel U) E) k (vel U) E c *
      dF g.γ (rho U) (pressure g U) (Num.dot (vel U) (vel U)) (Num.dot (vel U) E) (Num.dot E E) k (vel U) E c) ∈ S := by
    have := Q_eq g (rho U) (vel U) E (pressure g U) k hp
    simp only [pairF] at this
    rw [this]; exact hQ
  have hev1 := hlim.eventually (hS.mem_nhds hQ')
  have hρ : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < rho U * (1 + t) :=
    (hR (rho U)).continuousAt.tendsto.eventually_const_lt (by simpa using hU.1)
  have hpp : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < pressure g U * (1 + g.γ * t) :=
    (hP g (pressure g U)).continuousAt.tendsto.eventually_const_lt (by simpa using hU.2)
  have hT : Tendsto γt (𝓝 0) (𝓝 U) := h0 ▸ (path_cont g (rho U) (vel U) E (pressure g U) k).tendsto 0
  have hball := hT.eventually (Metric.ball_mem_nhds U hε)
  have hall := ((hρ.and (hpp.and hball)).filter_mono nhdsWithin_le_nhds).and
    (hev1.and (self_mem_nhdsWithin (s := {(0 : ℝ)}ᶜ) (a := 0)))
  obtain ⟨t, ⟨hρt, hpt, hbt⟩, hSt, ht⟩ := hall.exists
  refine ⟨t, ht, ⟨hρt, ?_⟩, ?_, ?_⟩
  · rw [pressure_path g (rho U) (vel U) E (pressure g U) k hρt.ne']; exact hpt
  · rw [dist_eq_norm] at hbt; exact hbt
  · simp only [h0] at hSt
    exact hSt

end Def13

theorem p3_13_1 : CFDLean.JST1.Spec.P3_13_1 := CFDLean.Num.pair_production_integral

open Def13 in
theorem p3_13_2 : CFDLean.JST1.Spec.P3_13_2 := by
  intro d g U E hU hv ε hε
  obtain ⟨hr, hp⟩ := hU
  have hγ := g.one_lt_γ
  set c := CFDLean.JST1.Spec.soundSpeed g U with hc
  set L := len E with hLdef
  have hE0 : 0 ≤ Num.dot E E := Finset.sum_nonneg fun α _ => mul_self_nonneg (E α)
  have hL2 : L ^ 2 = Num.dot E E := Real.sq_sqrt hE0
  have hc2 : c ^ 2 = g.γ * pressure g U / rho U := Real.sq_sqrt (by positivity)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hv' := abs_lt.1 hv
  have hcL : 0 < c * L := lt_of_le_of_lt (abs_nonneg _) hv
  have hLpos : 0 < L := by
    rcases hL0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hcL; exact absurd hcL (lt_irrefl 0)
  have key : ∀ σ : ℝ, σ ^ 2 = 1 →
      rho U * (g.γ * Num.dot (vel U) E + rho U / pressure g U * (σ * c / L) ^ 2 * Num.dot E E * Num.dot (vel U) E +
        2 * g.γ * (σ * c / L) * Num.dot E E) = 2 * rho U * g.γ * (Num.dot (vel U) E + σ * (c * L)) := by
    intro σ hσ
    have hk2 : rho U / pressure g U * (σ * c / L) ^ 2 * Num.dot E E = g.γ := by
      rw [← hL2, div_pow, mul_pow, hσ, hc2]
      field_simp
    have hk1 : (σ * c / L) * Num.dot E E = σ * (c * L) := by
      rw [← hL2]; field_simp
    linear_combination (rho U * Num.dot (vel U) E) * hk2 + (2 * g.γ * rho U) * hk1
  have hU : Admissible g U := ⟨hr, hp⟩
  constructor
  · obtain ⟨t, ht, hadm, hn, hS⟩ := exists_near g U E hU (1 * c / L) hε (isOpen_Ioi (a := (0 : ℝ)))
      (by
        rw [Set.mem_Ioi, key 1 (by norm_num)]
        exact mul_pos (mul_pos (mul_pos two_pos hr) (by linarith)) (by linarith))
    refine ⟨_, hadm, hn, ?_⟩
    have h2 : 0 < t ^ 2 := by positivity
    have := mul_pos (Set.mem_Ioi.1 hS) h2
    rwa [div_mul_cancel₀ _ h2.ne'] at this
  · obtain ⟨t, ht, hadm, hn, hS⟩ := exists_near g U E hU ((-1) * c / L) hε (isOpen_Iio (a := (0 : ℝ)))
      (by
        rw [Set.mem_Iio, key (-1) (by norm_num)]
        exact mul_neg_of_pos_of_neg (mul_pos (mul_pos two_pos hr) (by linarith)) (by linarith))
    refine ⟨_, hadm, hn, ?_⟩
    have h2 : 0 < t ^ 2 := by positivity
    have := mul_neg_of_neg_of_pos (Set.mem_Iio.1 hS) h2
    rwa [div_mul_cancel₀ _ h2.ne'] at this

end CFDLean.JST1.Proofs
