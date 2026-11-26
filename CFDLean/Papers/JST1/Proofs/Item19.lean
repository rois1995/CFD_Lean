import CFDLean.Papers.JST1.Spec.Item19
import CFDLean.Papers.JST1.Spec.Item16
import CFDLean.Papers.JST1.Proofs.Item2Euler
import CFDLean.Papers.JST1.Proofs.Item16

/-! Proofs of item 19 (P5, paper gap G6): the log mean is `logMean a b = a · E(ln b - ln a)` with the analytic
`E = dslope exp 0` (`E(t) = (eᵗ - 1)/t`, `E(0) = 1`), hence smooth on `(0, ∞)²`; the Ismail-Roe flux is then smooth on
admissible × admissible, and P4-16.2 applies to it. -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology Asymptotics Set
namespace CFDLean.JST1.Proofs
namespace IR19

/-- `E(t) = (eᵗ - 1)/t`, `E(0) = 1`. -/
def expSlope : ℝ → ℝ := dslope Real.exp 0

theorem expSlope_contDiff (n : ℕ) : ContDiff ℝ n expSlope :=
  contDiff_iff_contDiffAt.mpr fun _ => (analyticAt_rexp.dslope 0).contDiffAt

theorem logMean_eq_expSlope {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logMean a b = a * expSlope (Real.log b - Real.log a) := by
  by_cases h : a = b
  · subst h
    simp [logMean, expSlope, dslope_same, Real.deriv_exp]
  · have ht : Real.log b - Real.log a ≠ 0 := by
      intro h0
      exact h (Real.log_injOn_pos (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) (by linarith))
    rw [logMean, ite_eq_right h, expSlope, dslope_of_ne _ ht, slope_def_field, Real.exp_sub,
      Real.exp_log ha, Real.exp_log hb, Real.exp_zero, sub_zero]
    field_simp

end IR19

open IR19

theorem p5_19_1 : CFDLean.JST1.Spec.P5_19_1 := by
  intro n
  have hlog1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.log p.1) (Ioi 0 ×ˢ Ioi 0) :=
    contDiffOn_fst.log fun p hp => (Set.mem_Ioi.mp hp.1).ne'
  have hlog2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.log p.2) (Ioi 0 ×ˢ Ioi 0) :=
    contDiffOn_snd.log fun p hp => (Set.mem_Ioi.mp hp.2).ne'
  have h : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * expSlope (Real.log p.2 - Real.log p.1)) (Ioi 0 ×ˢ Ioi 0) :=
    contDiffOn_fst.mul ((expSlope_contDiff n).comp_contDiffOn (hlog2.sub hlog1))
  refine h.congr fun p hp => ?_
  exact logMean_eq_expSlope hp.1 hp.2

namespace IR19

variable {d : ℕ}

/-- The admissible set. -/
def Adm (g : Gas) : Set (State d) := {U : State d | Admissible g U}

/-- The domain `admissible × admissible`. -/
def Dom (g : Gas) : Set (State d × State d) := Adm g ×ˢ Adm g

theorem pressure_eq (g : Gas) (U : State d) :
    pressure g U = (g.γ - 1) * (U .energy - (∑ α, U (.momentum α) * U (.momentum α)) / (2 * U .mass)) := rfl

/-- Smoothness of the pressure where `ρ ≠ 0`, along a smooth state map. -/
theorem pressure_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Gas) (n : ℕ)
    (f : E → State d) (hf : ContDiff ℝ n f) (s : Set E) (hs : ∀ x ∈ s, rho (f x) ≠ 0) :
    ContDiffOn ℝ n (fun x => pressure g (f x)) s := by
  have hc : ∀ c : Channel d, ContDiff ℝ n (fun x => f x c) := fun c => contDiff_pi.mp hf c
  simp only [pressure_eq]
  refine contDiffOn_const.mul ((hc _).contDiffOn.sub (ContDiffOn.div ?_ ?_ ?_))
  · exact ContDiffOn.sum fun α _ => ((hc _).mul (hc _)).contDiffOn
  · exact (contDiff_const.mul (hc _)).contDiffOn
  · intro x hx
    exact mul_ne_zero two_ne_zero (hs x hx)

theorem isOpen_adm (g : Gas) : IsOpen (Adm g : Set (State d)) := by
  have h1 : IsOpen {U : State d | 0 < rho U} :=
    isOpen_lt continuous_const (continuous_apply _)
  have h2 : ContinuousOn (fun U : State d => pressure g U) {U | 0 < rho U} :=
    (pressure_contDiffOn g 0 id contDiff_id _ fun x hx => (ne_of_gt hx)).continuousOn
  have := h2.isOpen_inter_preimage h1 (isOpen_Ioi (a := (0 : ℝ)))
  simpa [Adm, Admissible, Set.preimage, Set.inter_def] using this

end IR19

open IR19

theorem p5_19_2 : CFDLean.JST1.Spec.P5_19_2 := by
  intro d g y
  refine ⟨isOpen_adm g, fun n => ?_⟩
  set S : Set (State d × State d) := Dom g with hS
  have hfst : ContDiff ℝ n (fun p : State d × State d => p.1) := contDiff_fst
  have hsnd : ContDiff ℝ n (fun p : State d × State d => p.2) := contDiff_snd
  -- components and primitive quantities of both states
  have comp : ∀ (f : State d × State d → State d), ContDiff ℝ n f → (∀ p ∈ S, Admissible g (f p)) →
      (∀ c, ContDiffOn ℝ n (fun p => f p c) S) ∧
      ContDiffOn ℝ n (fun p => rho (f p)) S ∧ ContDiffOn ℝ n (fun p => pressure g (f p)) S ∧
      (∀ α, ContDiffOn ℝ n (fun p => vel (f p) α) S) ∧
      ContDiffOn ℝ n (fun p => √(rho (f p) / pressure g (f p))) S ∧
      ContDiffOn ℝ n (fun p => √(rho (f p) * pressure g (f p))) S := by
    intro f hf hA
    have hc : ∀ c, ContDiffOn ℝ n (fun p => f p c) S := fun c => (contDiff_pi.mp hf c).contDiffOn
    have hr : ContDiffOn ℝ n (fun p => rho (f p)) S := hc _
    have hp : ContDiffOn ℝ n (fun p => pressure g (f p)) S :=
      pressure_contDiffOn g n f hf S fun p hp => (hA p hp).1.ne'
    refine ⟨hc, hr, hp, fun α => (hc _).div hr fun p hp' => (hA p hp').1.ne', ?_, ?_⟩
    · exact (hr.div hp fun p hp' => (hA p hp').2.ne').sqrt fun p hp' =>
        (div_pos (hA p hp').1 (hA p hp').2).ne'
    · exact (hr.mul hp).sqrt fun p hp' => (mul_pos (hA p hp').1 (hA p hp').2).ne'
  obtain ⟨-, -, -, hva, h1a, h5a⟩ := comp _ hfst fun p hp => hp.1
  obtain ⟨-, -, -, hvb, h1b, h5b⟩ := comp _ hsnd fun p hp => hp.2
  have pos1a : ∀ p ∈ S, 0 < √(rho p.1 / pressure g p.1) := fun p hp => (zfacts g _ hp.1).1
  have pos1b : ∀ p ∈ S, 0 < √(rho p.2 / pressure g p.2) := fun p hp => (zfacts g _ hp.2).1
  have pos5a : ∀ p ∈ S, 0 < √(rho p.1 * pressure g p.1) := fun p hp => (zfacts g _ hp.1).2.1
  have pos5b : ∀ p ∈ S, 0 < √(rho p.2 * pressure g p.2) := fun p hp => (zfacts g _ hp.2).2.1
  -- the log means
  have hL : ∀ (u v : State d × State d → ℝ), ContDiffOn ℝ n u S → ContDiffOn ℝ n v S →
      (∀ p ∈ S, 0 < u p) → (∀ p ∈ S, 0 < v p) →
      ContDiffOn ℝ n (fun p => logMean (u p) (v p)) S ∧ ∀ p ∈ S, 0 < logMean (u p) (v p) := by
    intro u v hu hv hu0 hv0
    refine ⟨(p5_19_1 n).comp (f := fun p => (u p, v p)) (hu.prodMk hv) fun p hp => ⟨hu0 p hp, hv0 p hp⟩,
      fun p hp => (logMean_properties _ _ (hu0 p hp) (hv0 p hp)).2.2.1⟩
  obtain ⟨hL5, pL5⟩ := hL _ _ h5a h5b pos5a pos5b
  obtain ⟨hL1, pL1⟩ := hL _ _ h1a h1b pos1a pos1b
  have hm1 : ContDiffOn ℝ n (fun p : State d × State d =>
      (√(rho p.1 / pressure g p.1) + √(rho p.2 / pressure g p.2)) / 2) S :=
    (h1a.add h1b).div_const _
  have pm1 : ∀ p ∈ S, (√(rho p.1 / pressure g p.1) + √(rho p.2 / pressure g p.2)) / 2 ≠ 0 :=
    fun p hp => (div_pos (add_pos (pos1a p hp) (pos1b p hp)) two_pos).ne'
  have hm5 : ContDiffOn ℝ n (fun p : State d × State d =>
      (√(rho p.1 * pressure g p.1) + √(rho p.2 * pressure g p.2)) / 2) S :=
    (h5a.add h5b).div_const _
  have hrhoh := hm1.mul hL5
  have prhoh : ∀ p ∈ S, (√(rho p.1 / pressure g p.1) + √(rho p.2 / pressure g p.2)) / 2 *
      logMean √(rho p.1 * pressure g p.1) √(rho p.2 * pressure g p.2) ≠ 0 :=
    fun p hp => mul_ne_zero (pm1 p hp) (pL5 p hp).ne'
  have huh : ∀ α, ContDiffOn ℝ n (fun p : State d × State d =>
      (√(rho p.1 / pressure g p.1) * vel p.1 α + √(rho p.2 / pressure g p.2) * vel p.2 α) / 2 /
        ((√(rho p.1 / pressure g p.1) + √(rho p.2 / pressure g p.2)) / 2)) S :=
    fun α => (((h1a.mul (hva α)).add (h1b.mul (hvb α))).div_const _).div hm1 pm1
  have hun := ContDiffOn.sum (s := Finset.univ) fun α _ => (huh α).mul (contDiffOn_const (c := y α))
  have huu := ContDiffOn.sum (s := Finset.univ) fun α _ => (huh α).mul (huh α)
  have hp1 := hm5.div hm1 pm1
  have hp2 := ((contDiffOn_const (c := (g.γ + 1) / (2 * g.γ))).mul (hL5.div hL1 fun p hp => (pL1 p hp).ne')).add
    ((contDiffOn_const (c := (g.γ - 1) / (2 * g.γ))).mul hp1)
  have hg1 : g.γ - 1 ≠ 0 := (sub_pos.mpr g.one_lt_γ).ne'
  have hhh := ((contDiffOn_const (c := g.γ)).mul hp2).div (hrhoh.mul contDiffOn_const)
    (fun p hp => mul_ne_zero (prhoh p hp) hg1) |>.add (huu.div_const 2)
  refine contDiffOn_pi.mpr fun c => ?_
  cases c with
  | mass => exact hrhoh.mul hun
  | momentum α => exact (hrhoh.mul (huh α)).mul hun |>.add (hp1.mul contDiffOn_const)
  | energy => exact (hrhoh.mul hhh).mul hun

namespace IR19

variable {d : ℕ}

theorem physFlux_linear (g : Gas) (U : State d) : IsLinearMap ℝ (physFlux g U) := by
  constructor
  · intro x y
    funext c
    cases c <;> simp only [physFlux, Num.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  · intro a x
    have hd : ∀ v : Vec d, Num.dot v (a • x) = a * Num.dot v x := by
      intro v
      simp only [Num.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    funext c
    cases c <;> simp only [physFlux, hd, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The defect `F^IR(a, b; y) - ½(F(a) + F(b))·y` as a linear map of `y`. -/
def defect (g : Gas) (a b : State d) : Vec d →ₗ[ℝ] State d :=
  IsLinearMap.mk' _ (ismailRoe_linear g a b) -
    (1 / 2 : ℝ) • (IsLinearMap.mk' _ (physFlux_linear g a) + IsLinearMap.mk' _ (physFlux_linear g b))

theorem defect_apply (g : Gas) (a b : State d) (y : Vec d) :
    defect g a b y = ismailRoe g a b y - (1 / 2 : ℝ) • (physFlux g a y + physFlux g b y) := rfl

end IR19

theorem p5_19_3 : CFDLean.JST1.Spec.P5_19_3 := by
  intro d g u0 hu0
  obtain ⟨hO, hC⟩ := p5_19_2 d g 0
  set e : Fin d → Vec d := fun α j => if α = j then 1 else 0 with he
  have hbig : ∀ α : Fin d, (fun p : State d × State d => defect g p.1 p.2 (e α))
      =O[𝓝 (u0, u0)] (fun p => ‖p.2 - p.1‖ ^ 2) := by
    intro α
    obtain ⟨-, hCα⟩ := p5_19_2 d g (e α)
    exact p4_16_2 (State d) (State d) (fun Ua Ub => ismailRoe g Ua Ub (e α)) (fun U => physFlux g U (e α))
      {U : State d | Admissible g U} u0 hO hu0 (hCα 2) (fun a _ b _ => ismailRoe_symm g a b (e α))
      (fun a ha => ismailRoe_consistent g a (e α) ha)
  choose c hc hcw using fun α => (hbig α).exists_pos
  refine ⟨∑ α, c α, ?_⟩
  filter_upwards [Filter.eventually_all.mpr fun α => (hcw α).bound] with p hp y
  rw [← defect_apply, LinearMap.pi_apply_eq_sum_univ (defect g p.1 p.2) y]
  have hn : 0 ≤ ‖p.2 - p.1‖ ^ 2 := by positivity
  calc ‖∑ α, y α • defect g p.1 p.2 (fun j => if α = j then 1 else 0)‖
      ≤ ∑ α, ‖y α • defect g p.1 p.2 (e α)‖ := norm_sum_le _ _
    _ ≤ ∑ α, ‖y‖ * (c α * ‖p.2 - p.1‖ ^ 2) := by
        refine Finset.sum_le_sum fun α _ => ?_
        rw [norm_smul]
        have h1 := hp α
        rw [Real.norm_of_nonneg hn] at h1
        exact mul_le_mul (norm_le_pi_norm y α) h1 (norm_nonneg _) (norm_nonneg _)
    _ = (∑ α, c α) * ‖y‖ * ‖p.2 - p.1‖ ^ 2 := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring

end CFDLean.JST1.Proofs
