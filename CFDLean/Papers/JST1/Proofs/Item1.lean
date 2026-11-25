import CFDLean.Papers.JST1.Spec.Item1

/-! Proofs of item 1 (`lem:eps2`). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology
namespace CFDLean.JST1.Proofs

/-! ### The constants -/

theorem sqrt_gg_pos {γ : ℝ} (hγ : 1 < γ) : 0 < Real.sqrt (γ * (γ - 1)) :=
  Real.sqrt_pos.2 (by nlinarith)

theorem sqrt_gg_sq {γ : ℝ} (hγ : 1 < γ) : Real.sqrt (γ * (γ - 1)) ^ 2 = γ * (γ - 1) :=
  Real.sq_sqrt (by nlinarith)

theorem lamLow_lt_one {γ : ℝ} (hγ : 1 < γ) : lamLow γ < 1 := by
  have h1 := sqrt_gg_sq hγ
  have h2 := sqrt_gg_pos hγ
  unfold lamLow
  nlinarith

theorem three_quarter_lt_lamLow {γ : ℝ} (hγ : 1 < γ) : 3 / 4 < lamLow γ := by
  have h1 := sqrt_gg_sq hγ
  have h2 := sqrt_gg_pos hγ
  unfold lamLow
  nlinarith

theorem one_lt_lamHigh {γ : ℝ} (hγ : 1 < γ) : 1 < lamHigh γ := by
  have h2 := sqrt_gg_pos hγ
  unfold lamHigh
  linarith

theorem lamLow_formula {γ : ℝ} (hγ : 1 < γ) :
    lamLow γ = (1 + 1 / (1 + Real.sqrt (1 - γ⁻¹))) / 2 := by
  have hγ0 : 0 < γ := by linarith
  have hx : 0 ≤ 1 - γ⁻¹ := by
    have : γ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hγ
    linarith
  have hsq : Real.sqrt (γ * (γ - 1)) = γ * Real.sqrt (1 - γ⁻¹) := by
    have : γ * (γ - 1) = γ ^ 2 * (1 - γ⁻¹) := by field_simp
    rw [this, Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq hγ0.le]
  set t := Real.sqrt (1 - γ⁻¹) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 1 - γ⁻¹ := Real.sq_sqrt hx
  unfold lamLow
  rw [hsq]
  have h1t : (1 + t) ≠ 0 := by positivity
  field_simp
  have : γ * t ^ 2 = γ - 1 := by rw [ht2]; field_simp
  linear_combination (-1 : ℝ) * this

theorem p1_1_4 : CFDLean.JST1.Spec.P1_1_4 := by
  refine ⟨fun γ hγ => ⟨three_quarter_lt_lamLow hγ, lamLow_lt_one hγ, one_lt_lamHigh hγ⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Ioi] at hx hy
    rw [lamLow_formula hx, lamLow_formula hy]
    have hlt : 1 - x⁻¹ < 1 - y⁻¹ := by
      have : y⁻¹ < x⁻¹ := inv_strictAnti₀ (by linarith) hxy
      linarith
    have hx0 : 0 ≤ 1 - x⁻¹ := by
      have : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
      linarith
    have hs : Real.sqrt (1 - x⁻¹) < Real.sqrt (1 - y⁻¹) := Real.sqrt_lt_sqrt hx0 hlt
    have hs0 : 0 ≤ Real.sqrt (1 - x⁻¹) := Real.sqrt_nonneg _
    have : 1 / (1 + Real.sqrt (1 - y⁻¹)) < 1 / (1 + Real.sqrt (1 - x⁻¹)) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  · have hc : Continuous lamLow := by
      unfold lamLow
      fun_prop
    have h := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    have h1 : lamLow 1 = 1 := by unfold lamLow; norm_num
    rwa [h1] at h
  · have h : Tendsto (fun γ : ℝ => (1 + 1 / (1 + Real.sqrt (1 - γ⁻¹))) / 2) atTop
        (𝓝 ((1 + 1 / (1 + Real.sqrt (1 - 0))) / 2)) := by
      apply Tendsto.div_const
      apply Tendsto.const_add
      apply Tendsto.div tendsto_const_nhds
      · exact (tendsto_const_nhds.sub tendsto_inv_atTop_zero).sqrt.const_add 1
      · positivity
    have h' : ((1 + 1 / (1 + Real.sqrt (1 - 0))) / 2 : ℝ) = 3 / 4 := by norm_num
    rw [h'] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with γ hγ
    exact (lamLow_formula hγ).symm
  · unfold lamLow
    have : Real.sqrt ((14 / 10 : ℝ) * (14 / 10 - 1)) < 7484 / 10000 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  · unfold lamLow
    have : (7482 / 10000 : ℝ) < Real.sqrt ((14 / 10 : ℝ) * (14 / 10 - 1)) := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith

/-! ### The thermodynamic pencil -/

theorem lam_quad {γ : ℝ} (hγ : 1 < γ) :
    lamLow γ ^ 2 - (γ + 1) * lamLow γ + (3 * γ + 1) / 4 = 0 ∧
    lamHigh γ ^ 2 - (γ + 1) * lamHigh γ + (3 * γ + 1) / 4 = 0 := by
  have h1 := sqrt_gg_sq hγ
  unfold lamLow lamHigh
  constructor <;> linear_combination (1 / 4 : ℝ) * h1

/-- `4 A (q̃ - c q) = (2 A a - B b)²` with `A = γ(1-c)`, `B = γ+1-2c`, for a root `c` of the pencil. -/
theorem pencil_sq {γ c : ℝ} (hc : c ^ 2 - (γ + 1) * c + (3 * γ + 1) / 4 = 0) (a b : ℝ) :
    4 * (γ * (1 - c)) * (thermoQt γ a b - c * thermoQ γ a b) =
      (2 * (γ * (1 - c)) * a - (γ + 1 - 2 * c) * b) ^ 2 := by
  unfold thermoQ thermoQt
  linear_combination (4 * (γ - 1) * b ^ 2) * hc

theorem pencil_low {γ : ℝ} (hγ : 1 < γ) (a b : ℝ) : lamLow γ * thermoQ γ a b ≤ thermoQt γ a b := by
  have h := pencil_sq (lam_quad hγ).1 a b
  have hA : 0 < γ * (1 - lamLow γ) := mul_pos (by linarith) (by linarith [lamLow_lt_one hγ])
  have : 0 ≤ thermoQt γ a b - lamLow γ * thermoQ γ a b := by
    by_contra hneg
    push Not at hneg
    have : 4 * (γ * (1 - lamLow γ)) * (thermoQt γ a b - lamLow γ * thermoQ γ a b) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hneg
    nlinarith [sq_nonneg (2 * (γ * (1 - lamLow γ)) * a - (γ + 1 - 2 * lamLow γ) * b)]
  linarith

theorem pencil_high {γ : ℝ} (hγ : 1 < γ) (a b : ℝ) : thermoQt γ a b ≤ lamHigh γ * thermoQ γ a b := by
  have h := pencil_sq (lam_quad hγ).2 a b
  have hA : γ * (1 - lamHigh γ) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith [one_lt_lamHigh hγ])
  have : thermoQt γ a b - lamHigh γ * thermoQ γ a b ≤ 0 := by
    by_contra hneg
    push Not at hneg
    have : 4 * (γ * (1 - lamHigh γ)) * (thermoQt γ a b - lamHigh γ * thermoQ γ a b) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hneg
    nlinarith [sq_nonneg (2 * (γ * (1 - lamHigh γ)) * a - (γ + 1 - 2 * lamHigh γ) * b)]
  linarith

/-- Eigenvector of the pencil for a root `c`: `(a, b) = (γ+1-2c, 2γ(1-c))`. -/
theorem pencil_eig {γ c : ℝ} (hc : c ^ 2 - (γ + 1) * c + (3 * γ + 1) / 4 = 0) :
    thermoQt γ (γ + 1 - 2 * c) (2 * (γ * (1 - c))) = c * thermoQ γ (γ + 1 - 2 * c) (2 * (γ * (1 - c))) := by
  unfold thermoQ thermoQt
  linear_combination (4 * γ * (1 - c) * (γ - 1)) * hc

theorem thermoQ_eq (γ a b : ℝ) : thermoQ γ a b = (b - a) ^ 2 + (γ - 1) * a ^ 2 := by
  unfold thermoQ; ring

theorem thermoQ_nonneg {γ : ℝ} (hγ : 1 < γ) (a b : ℝ) : 0 ≤ thermoQ γ a b := by
  rw [thermoQ_eq]; nlinarith [sq_nonneg (b - a), sq_nonneg a]

theorem thermoQ_pos {γ : ℝ} (hγ : 1 < γ) {a : ℝ} (ha : a ≠ 0) (b : ℝ) : 0 < thermoQ γ a b := by
  rw [thermoQ_eq]
  have : 0 < a ^ 2 := by positivity
  nlinarith [sq_nonneg (b - a)]

theorem lamLow_gap {γ : ℝ} (hγ : 1 < γ) : γ + 1 - 2 * lamLow γ ≠ 0 := by
  have := sqrt_gg_pos hγ
  unfold lamLow; intro h; linarith

theorem lamHigh_gap {γ : ℝ} (hγ : 1 < γ) : γ + 1 - 2 * lamHigh γ ≠ 0 := by
  have := sqrt_gg_pos hγ
  unfold lamHigh; intro h; linarith

theorem p1_1_1 : CFDLean.JST1.Spec.P1_1_1 := by
  intro γ hγ
  refine ⟨fun a b => ⟨pencil_low hγ a b, pencil_high hγ a b⟩, ?_, ?_⟩
  · refine ⟨_, _, ?_, pencil_eig (lam_quad hγ).1⟩
    intro h
    exact lamLow_gap hγ (Prod.mk.inj h).1
  · refine ⟨_, _, ?_, pencil_eig (lam_quad hγ).2⟩
    intro h
    exact lamHigh_gap hγ (Prod.mk.inj h).1

/-! ### Thermodynamic two-state forms and the path in entropy variables -/

/-- Physical entropy in primitive variables. -/
def entS (γ r p : ℝ) : ℝ := Real.log p - γ * Real.log r

/-- Thermodynamic part of `[w]·[u]`. -/
def thQ (γ r1 p1 r2 p2 : ℝ) : ℝ :=
  -((entS γ r2 p2 - entS γ r1 p1) * (r2 - r1) + (r2 / p2 - r1 / p1) * (p2 - p1)) / (γ - 1)

/-- Thermodynamic part of `[w]·[ũ]`. -/
def thQt (γ r1 p1 r2 p2 : ℝ) : ℝ :=
  -((entS γ r2 p2 - entS γ r1 p1) * (r2 - r1) + γ * (r2 / p2 - r1 / p1) * (p2 - p1)) / (γ - 1)

theorem convex_comb_pos {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 < x + t * (y - x) := by
  rcases lt_or_eq_of_le h1 with h | h
  · have : 0 < (1 - t) * x := mul_pos (by linarith) hx
    nlinarith [mul_nonneg h0 hy.le]
  · subst h; linarith

/-- Path in entropy variables, `β = ρ/p = -w_E` component. -/
def pβ (β1 db t : ℝ) : ℝ := β1 + t * db

/-- Density along the path (`s` and `β` affine in `t`). -/
def pρ (γ s1 ds β1 db t : ℝ) : ℝ := Real.exp (-((s1 + t * ds) + Real.log (pβ β1 db t)) / (γ - 1))

/-- `μ Δw·u + ν Δw·ũ` (thermodynamic part) along the path. -/
def pK (γ μ ν s1 ds β1 db t : ℝ) : ℝ :=
  -((μ + ν) * ds * pρ γ s1 ds β1 db t + (μ + γ * ν) * db * (pρ γ s1 ds β1 db t / pβ β1 db t)) / (γ - 1)

theorem deriv_alg (γ μ ν ds db B R : ℝ) (hB : B ≠ 0) (hg : γ - 1 ≠ 0) :
    R / (γ - 1) * (μ * thermoQ γ (-(ds + db / B) / (γ - 1)) (-(ds + db / B) / (γ - 1) - db / B) +
      ν * thermoQt γ (-(ds + db / B) / (γ - 1)) (-(ds + db / B) / (γ - 1) - db / B)) =
    -((μ + ν) * ds * (R * (-(ds + db / B) / (γ - 1))) +
      (μ + γ * ν) * db * ((R * (-(ds + db / B) / (γ - 1)) * B - R * db) / B ^ 2)) / (γ - 1) := by
  set e := db / B with he
  set a := -(ds + e) / (γ - 1) with ha
  have hdb : db = e * B := by rw [he]; field_simp
  have h1 : (μ + γ * ν) * db * ((R * a * B - R * db) / B ^ 2) = (μ + γ * ν) * R * e * (a - e) := by
    rw [hdb]; field_simp
  have hds : ds = -(γ - 1) * a - e := by rw [ha]; field_simp; ring
  rw [h1]
  clear_value a e
  subst hds
  unfold thermoQ thermoQt
  ring

theorem hasDerivAt_pK {γ μ ν s1 ds β1 db t : ℝ} (hg : γ - 1 ≠ 0) (hb : 0 < pβ β1 db t) :
    HasDerivAt (pK γ μ ν s1 ds β1 db)
      (pρ γ s1 ds β1 db t / (γ - 1) *
        (μ * thermoQ γ (-(ds + db / pβ β1 db t) / (γ - 1)) (-(ds + db / pβ β1 db t) / (γ - 1) - db / pβ β1 db t) +
         ν * thermoQt γ (-(ds + db / pβ β1 db t) / (γ - 1)) (-(ds + db / pβ β1 db t) / (γ - 1) - db / pβ β1 db t)))
      t := by
  have hβd : HasDerivAt (pβ β1 db) db t := by
    have := ((hasDerivAt_id t).mul_const db).const_add β1
    simp only [id, one_mul] at this
    exact this
  have hLd : HasDerivAt (fun x => -((s1 + x * ds) + Real.log (pβ β1 db x)) / (γ - 1))
      (-(ds + db / pβ β1 db t) / (γ - 1)) t := by
    have h1 := ((hasDerivAt_id t).mul_const ds).const_add s1
    simp only [id, one_mul] at h1
    exact ((h1.add (hβd.log hb.ne')).neg).div_const (γ - 1)
  have hρd : HasDerivAt (pρ γ s1 ds β1 db)
      (pρ γ s1 ds β1 db t * (-(ds + db / pβ β1 db t) / (γ - 1))) t := hLd.exp
  have hPd := hρd.div hβd hb.ne'
  have hKd := (((hρd.const_mul ((μ + ν) * ds)).add (hPd.const_mul ((μ + γ * ν) * db))).neg).div_const
    (γ - 1)
  convert hKd using 1 <;> first | rfl | rw [deriv_alg γ μ ν ds db _ _ hb.ne' hg]

/-- Integral argument along the straight path in entropy variables (`v = 0` part): if
`μ q + ν q̃ ≥ 0` pointwise, then `μ [w]·[u] + ν [w]·[ũ] ≥ 0` for the thermodynamic parts. -/
theorem thermo_path {γ μ ν : ℝ} (hγ : 1 < γ) (hq : ∀ a b, 0 ≤ μ * thermoQ γ a b + ν * thermoQt γ a b)
    {r1 p1 r2 p2 : ℝ} (hr1 : 0 < r1) (hp1 : 0 < p1) (hr2 : 0 < r2) (hp2 : 0 < p2) :
    0 ≤ μ * thQ γ r1 p1 r2 p2 + ν * thQt γ r1 p1 r2 p2 := by
  have hg1 : 0 < γ - 1 := by linarith
  have hβpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < pβ (r1 / p1) (r2 / p2 - r1 / p1) t := by
    rintro t ⟨h0, h1⟩
    exact convex_comb_pos (div_pos hr1 hp1) (div_pos hr2 hp2) h0 h1
  have hd := fun t (ht : t ∈ Set.Icc (0 : ℝ) 1) =>
    hasDerivAt_pK (μ := μ) (ν := ν) (s1 := entS γ r1 p1) (ds := entS γ r2 p2 - entS γ r1 p1)
      hg1.ne' (hβpos t ht)
  have hcont : ContinuousOn (pK γ μ ν (entS γ r1 p1) (entS γ r2 p2 - entS γ r1 p1) (r1 / p1)
      (r2 / p2 - r1 / p1)) (Set.Icc 0 1) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t _ => mul_nonneg (div_nonneg (Real.exp_pos _).le hg1.le) (hq _ _))
  have hK01 := hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have hρ0 : pρ γ (entS γ r1 p1) (entS γ r2 p2 - entS γ r1 p1) (r1 / p1) (r2 / p2 - r1 / p1) 0 = r1 := by
    unfold pρ pβ entS
    rw [zero_mul, add_zero, zero_mul, add_zero, Real.log_div hr1.ne' hp1.ne']
    rw [show -(Real.log p1 - γ * Real.log r1 + (Real.log r1 - Real.log p1)) / (γ - 1) = Real.log r1 by
      field_simp; ring]
    exact Real.exp_log hr1
  have hρ1 : pρ γ (entS γ r1 p1) (entS γ r2 p2 - entS γ r1 p1) (r1 / p1) (r2 / p2 - r1 / p1) 1 = r2 := by
    unfold pρ pβ entS
    rw [one_mul, one_mul, show r1 / p1 + (r2 / p2 - r1 / p1) = r2 / p2 by ring,
      Real.log_div hr2.ne' hp2.ne']
    rw [show -(Real.log p1 - γ * Real.log r1 + (Real.log p2 - γ * Real.log r2 -
      (Real.log p1 - γ * Real.log r1)) + (Real.log r2 - Real.log p2)) / (γ - 1) = Real.log r2 by
      field_simp; ring]
    exact Real.exp_log hr2
  have hβ0 : pβ (r1 / p1) (r2 / p2 - r1 / p1) 0 = r1 / p1 := by unfold pβ; ring
  have hβ1 : pβ (r1 / p1) (r2 / p2 - r1 / p1) 1 = r2 / p2 := by unfold pβ; ring
  unfold pK at hK01
  rw [hρ0, hρ1, hβ0, hβ1] at hK01
  have e1 : r1 / (r1 / p1) = p1 := by field_simp
  have e2 : r2 / (r2 / p2) = p2 := by field_simp
  rw [e1, e2] at hK01
  have : μ * thQ γ r1 p1 r2 p2 + ν * thQt γ r1 p1 r2 p2 =
      -((μ + ν) * (entS γ r2 p2 - entS γ r1 p1) * r2 + (μ + γ * ν) * (r2 / p2 - r1 / p1) * p2) / (γ - 1) -
      -((μ + ν) * (entS γ r2 p2 - entS γ r1 p1) * r1 + (μ + γ * ν) * (r2 / p2 - r1 / p1) * p1) / (γ - 1) := by
    unfold thQ thQt
    ring
  rw [this]
  linarith

/-! ### States: channel sums and the two-state decomposition -/

variable {d : ℕ}

/-- The channels as a sum type. -/
def chanEquiv (d : ℕ) : Channel d ≃ (Unit ⊕ Fin d) ⊕ Unit where
  toFun
    | .mass => .inl (.inl ())
    | .momentum α => .inl (.inr α)
    | .energy => .inr ()
  invFun
    | .inl (.inl _) => .mass
    | .inl (.inr α) => .momentum α
    | .inr _ => .energy
  left_inv c := by cases c <;> rfl
  right_inv x := by rcases x with ((_ | _) | _) <;> rfl

theorem e1_sum_channel (f : Channel d → ℝ) :
    ∑ c, f c = f .mass + ∑ α, f (.momentum α) + f .energy := by
  rw [← (chanEquiv d).symm.sum_comp]
  simp [Fintype.sum_sum_type, chanEquiv]

theorem e1_pairF_channel (x y : State d) :
    pairF x y = x .mass * y .mass + ∑ α, x (.momentum α) * y (.momentum α) + x .energy * y .energy :=
  e1_sum_channel _

theorem e1_mom_eq {U : State d} (h : rho U ≠ 0) (α : Fin d) : U (.momentum α) = rho U * vel U α := by
  unfold vel mom; field_simp

theorem dot_mom {U : State d} (h : rho U ≠ 0) : Num.dot (mom U) (mom U) = rho U ^ 2 * Num.dot (vel U) (vel U) := by
  unfold Num.dot vel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  field_simp

theorem e1_energy_eq (g : Gas) {U : State d} (h : rho U ≠ 0) :
    U .energy = pressure g U / (g.γ - 1) + rho U * Num.dot (vel U) (vel U) / 2 := by
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  unfold pressure
  rw [dot_mom h]
  show U .energy = (g.γ - 1) * (U .energy - _) / (g.γ - 1) + _
  field_simp
  ring

/-- Velocity part of both `[w]·[u]` and `[w]·[ũ]`. -/
def velV (g : Gas) (Ui Uk : State d) : ℝ :=
  (rho Uk / pressure g Uk * rho Ui + rho Ui / pressure g Ui * rho Uk) * (∑ α, (vel Uk α - vel Ui α) ^ 2) / 2

theorem velV_nonneg (g : Gas) {Ui Uk : State d} (hi : Admissible g Ui) (hk : Admissible g Uk) :
    0 ≤ velV g Ui Uk := by
  obtain ⟨hri, hpi⟩ := hi
  obtain ⟨hrk, hpk⟩ := hk
  unfold velV
  have : 0 ≤ ∑ α, (vel Uk α - vel Ui α) ^ 2 := Finset.sum_nonneg fun α _ => sq_nonneg _
  positivity

theorem mom_sum (g : Gas) {Ui Uk : State d} (hi : rho Ui ≠ 0) (hk : rho Uk ≠ 0) :
    ∑ α, (entropyVars g Uk - entropyVars g Ui) (.momentum α) * (Uk - Ui) (.momentum α) =
      rho Uk * rho Uk / pressure g Uk * Num.dot (vel Uk) (vel Uk) -
        (rho Uk / pressure g Uk * rho Ui + rho Ui / pressure g Ui * rho Uk) * Num.dot (vel Uk) (vel Ui) +
        rho Ui * rho Ui / pressure g Ui * Num.dot (vel Ui) (vel Ui) := by
  simp only [Pi.sub_apply, entropyVars, e1_mom_eq hi, e1_mom_eq hk, Num.dot, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

theorem vel_sum (Ui Uk : State d) :
    ∑ α, (vel Uk α - vel Ui α) ^ 2 = Num.dot (vel Uk) (vel Uk) - 2 * Num.dot (vel Uk) (vel Ui) + Num.dot (vel Ui) (vel Ui) := by
  simp only [Num.dot, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

theorem enth_mom (g : Gas) (Ui Uk : State d) (α : Fin d) :
    (enthalpyState g Uk - enthalpyState g Ui) (.momentum α) = (Uk - Ui) (.momentum α) := by
  simp [enthalpyState, eE]

theorem pair_decomp (g : Gas) {Ui Uk : State d} (hi : Admissible g Ui) (hk : Admissible g Uk) :
    pairF (entropyVars g Uk - entropyVars g Ui) (Uk - Ui) =
        thQ g.γ (rho Ui) (pressure g Ui) (rho Uk) (pressure g Uk) + velV g Ui Uk ∧
      pairF (entropyVars g Uk - entropyVars g Ui) (enthalpyState g Uk - enthalpyState g Ui) =
        thQt g.γ (rho Ui) (pressure g Ui) (rho Uk) (pressure g Uk) + velV g Ui Uk := by
  obtain ⟨hri, hpi⟩ := hi
  obtain ⟨hrk, hpk⟩ := hk
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  have hS := mom_sum g hri.ne' hrk.ne'
  have hS' : ∑ α, (entropyVars g Uk - entropyVars g Ui) (.momentum α) *
      (enthalpyState g Uk - enthalpyState g Ui) (.momentum α) =
      ∑ α, (entropyVars g Uk - entropyVars g Ui) (.momentum α) * (Uk - Ui) (.momentum α) := by
    simp only [enth_mom]
  have hEi := e1_energy_eq g hri.ne'
  have hEk := e1_energy_eq g hrk.ne'
  rw [e1_pairF_channel, e1_pairF_channel, hS', hS]
  simp only [Pi.sub_apply, entropyVars, enthalpyState, Pi.add_apply, Pi.smul_apply, eE, smul_eq_mul,
    mul_one, mul_zero, add_zero]
  rw [hEi, hEk]
  unfold velV thQ thQt entS physEntropy
  rw [vel_sum]
  generalize Num.dot (vel Uk) (vel Uk) = Dkk
  generalize Num.dot (vel Uk) (vel Ui) = Dki
  generalize Num.dot (vel Ui) (vel Ui) = Dii
  generalize Real.log (pressure g Uk) = Lpk
  generalize Real.log (pressure g Ui) = Lpi
  generalize Real.log (rho Uk) = Lrk
  generalize Real.log (rho Ui) = Lri
  change 0 < Ui .mass at hri
  change 0 < Uk .mass at hrk
  unfold rho
  generalize pressure g Uk = pk at *
  generalize pressure g Ui = pi at *
  generalize Ui .mass = ri at *
  generalize Uk .mass = rk at *
  constructor
  · field_simp
    ring
  · field_simp
    ring

theorem pairF_smul_right {κ : Type} [Fintype κ] (x y : κ → ℝ) (c : ℝ) : pairF x (c • y) = c * pairF x y := by
  simp only [pairF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem p1_1_3 : CFDLean.JST1.Spec.P1_1_3 := by
  intro d g Ui Uk hi hk
  rw [(pair_decomp g hi hk).1]
  have h := thermo_path (μ := 1) (ν := 0) g.one_lt_γ (fun a b => by
      simpa using thermoQ_nonneg g.one_lt_γ a b) hi.1 hi.2 hk.1 hk.2
  have := velV_nonneg g hi hk
  linarith

theorem p1_1_2 : CFDLean.JST1.Spec.P1_1_2 := by
  intro d g Ui Uk hi hk
  simp only []
  rw [(pair_decomp g hi hk).1, (pair_decomp g hi hk).2]
  have hγ := g.one_lt_γ
  have hV := velV_nonneg g hi hk
  have hlo := thermo_path (μ := -lamLow g.γ) (ν := 1) hγ (fun a b => by
      have := pencil_low hγ a b; linarith) hi.1 hi.2 hk.1 hk.2
  have hhi := thermo_path (μ := lamHigh g.γ) (ν := -1) hγ (fun a b => by
      have := pencil_high hγ a b; linarith) hi.1 hi.2 hk.1 hk.2
  have h1 := lamLow_lt_one hγ
  have h2 := one_lt_lamHigh hγ
  constructor
  · nlinarith
  · nlinarith

theorem p1_1_5 : CFDLean.JST1.Spec.P1_1_5 := by
  intro d g Ui Uk lam eps2 hi hk hlam heps
  simp only []
  have hd2 : (lam * eps2) • (enthalpyState g Ui - enthalpyState g Uk) =
      (-(eps2 * lam)) • (enthalpyState g Uk - enthalpyState g Ui) := by
    ext c; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [hd2, pairF_smul_right]
  have h2 := (p1_1_2 d g Ui Uk hi hk).1
  have h3 := p1_1_3 d g Ui Uk hi hk
  have hl := three_quarter_lt_lamLow g.one_lt_γ
  have hel : 0 ≤ eps2 * lam := mul_nonneg heps hlam
  refine ⟨rfl, ?_, ?_⟩
  · nlinarith
  · have : 0 ≤ lamLow g.γ * eps2 * lam * pairF (entropyVars g Uk - entropyVars g Ui) (Uk - Ui) := by
      have : 0 ≤ lamLow g.γ := by linarith
      positivity
    linarith

/-! ### Sharpness: small jumps along a pencil eigenvector -/

theorem tendsto_expSlope (k : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (h * k) - 1) / h) (𝓝[≠] 0) (𝓝 k) := by
  have hd : HasDerivAt (fun h : ℝ => Real.exp (h * k)) (Real.exp (0 * k) * (1 * k)) 0 :=
    ((hasDerivAt_id 0).mul_const k).exp
  have := hd.tendsto_slope_zero
  simp only [zero_mul, Real.exp_zero, one_mul, zero_add, smul_eq_mul] at this
  refine this.congr fun h => ?_
  rw [div_eq_inv_mul]

theorem thQ_scaled {γ a b h : ℝ} (hγ : 1 < γ) (hh : h ≠ 0) :
    thQ γ 1 1 (Real.exp (h * a)) (Real.exp (h * b)) / h ^ 2 =
      -((b - γ * a) * ((Real.exp (h * a) - 1) / h) +
        ((Real.exp (h * (a - b)) - 1) / h) * ((Real.exp (h * b) - 1) / h)) / (γ - 1) ∧
    thQt γ 1 1 (Real.exp (h * a)) (Real.exp (h * b)) / h ^ 2 =
      -((b - γ * a) * ((Real.exp (h * a) - 1) / h) +
        γ * ((Real.exp (h * (a - b)) - 1) / h) * ((Real.exp (h * b) - 1) / h)) / (γ - 1) := by
  have hg : γ - 1 ≠ 0 := by linarith
  have e1 : entS γ 1 1 = 0 := by simp [entS]
  have e2 : entS γ (Real.exp (h * a)) (Real.exp (h * b)) = h * (b - γ * a) := by
    simp only [entS, Real.log_exp]; ring
  have e3 : Real.exp (h * a) / Real.exp (h * b) = Real.exp (h * (a - b)) := by
    rw [← Real.exp_sub]; ring_nf
  unfold thQ thQt
  rw [e1, e2, e3]
  constructor
  · field_simp; ring
  · field_simp; ring

theorem exists_jump {γ a b c ε : ℝ} (hγ : 1 < γ) (hq : 0 < thermoQ γ a b)
    (hc : thermoQt γ a b = c * thermoQ γ a b) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < thQ γ 1 1 (Real.exp (h * a)) (Real.exp (h * b)) ∧
      thQt γ 1 1 (Real.exp (h * a)) (Real.exp (h * b)) <
        (c + ε) * thQ γ 1 1 (Real.exp (h * a)) (Real.exp (h * b)) ∧
      (c - ε) * thQ γ 1 1 (Real.exp (h * a)) (Real.exp (h * b)) <
        thQt γ 1 1 (Real.exp (h * a)) (Real.exp (h * b)) := by
  have hg : 0 < γ - 1 := by linarith
  set F : ℝ → ℝ := fun h => thQ γ 1 1 (Real.exp (h * a)) (Real.exp (h * b)) / h ^ 2 with hF
  set G : ℝ → ℝ := fun h => thQt γ 1 1 (Real.exp (h * a)) (Real.exp (h * b)) / h ^ 2 with hG
  have hEa := tendsto_expSlope a
  have hEb := tendsto_expSlope b
  have hEab := tendsto_expSlope (a - b)
  have hFl : Tendsto F (𝓝[≠] 0) (𝓝 (thermoQ γ a b / (γ - 1))) := by
    have : Tendsto (fun h : ℝ => -((b - γ * a) * ((Real.exp (h * a) - 1) / h) +
        ((Real.exp (h * (a - b)) - 1) / h) * ((Real.exp (h * b) - 1) / h)) / (γ - 1)) (𝓝[≠] 0)
        (𝓝 (-((b - γ * a) * a + (a - b) * b) / (γ - 1))) :=
      (((hEa.const_mul (b - γ * a)).add (hEab.mul hEb)).neg).div_const _
    have e : -((b - γ * a) * a + (a - b) * b) / (γ - 1) = thermoQ γ a b / (γ - 1) := by
      unfold thermoQ; ring
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (thQ_scaled hγ hh).1.symm
  have hGl : Tendsto G (𝓝[≠] 0) (𝓝 (c * (thermoQ γ a b / (γ - 1)))) := by
    have : Tendsto (fun h : ℝ => -((b - γ * a) * ((Real.exp (h * a) - 1) / h) +
        γ * ((Real.exp (h * (a - b)) - 1) / h) * ((Real.exp (h * b) - 1) / h)) / (γ - 1)) (𝓝[≠] 0)
        (𝓝 (-((b - γ * a) * a + γ * (a - b) * b) / (γ - 1))) :=
      (((hEa.const_mul (b - γ * a)).add ((hEab.const_mul γ).mul hEb)).neg).div_const _
    have e : -((b - γ * a) * a + γ * (a - b) * b) / (γ - 1) = c * (thermoQ γ a b / (γ - 1)) := by
      rw [mul_div_assoc', ← hc]; unfold thermoQt; ring
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (thQ_scaled hγ hh).2.symm
  have hA : 0 < thermoQ γ a b / (γ - 1) := div_pos hq hg
  have h1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), 0 < F h := hFl.eventually_const_lt hA
  have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), G h - (c + ε) * F h < 0 := by
    have := hGl.sub (hFl.const_mul (c + ε))
    refine this.eventually_lt_const ?_
    nlinarith
  have h3 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), (c - ε) * F h - G h < 0 := by
    have := (hFl.const_mul (c - ε)).sub hGl
    refine this.eventually_lt_const ?_
    nlinarith
  obtain ⟨h, hh1, hh2, hh3, hh0⟩ := (h1.and (h2.and (h3.and self_mem_nhdsWithin))).exists
  have hh0' : h ≠ 0 := hh0
  have hpos : 0 < h ^ 2 := by positivity
  simp only [hF, hG] at hh1 hh2 hh3
  refine ⟨h, ?_, ?_, ?_⟩
  · exact (div_pos_iff_of_pos_right hpos).1 hh1
  · have := mul_neg_of_neg_of_pos hh2 hpos
    field_simp at this
    linarith
  · have := mul_neg_of_neg_of_pos hh3 hpos
    field_simp at this
    linarith

/-- A state at rest from `(ρ, p)`. -/
def restState (g : Gas) (r p : ℝ) : State d := primState g r 0 p

theorem rho_rest (g : Gas) (r p : ℝ) : rho (restState (d := d) g r p) = r := rfl

theorem vel_rest (g : Gas) (r p : ℝ) (α : Fin d) : vel (restState (d := d) g r p) α = 0 := by
  simp [vel, mom, rho, restState, primState]

theorem pressure_rest (g : Gas) {r : ℝ} (p : ℝ) : pressure g (restState (d := d) g r p) = p := by
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  simp only [pressure, energy, mom, restState, primState, Num.dot]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_div, sub_zero, add_zero]
  field_simp

theorem velV_rest (g : Gas) (r1 p1 r2 p2 : ℝ) :
    velV g (restState (d := d) g r1 p1) (restState g r2 p2) = 0 := by
  simp [velV, vel_rest]

theorem admissible_rest (g : Gas) {r p : ℝ} (hr : 0 < r) (hp : 0 < p) :
    Admissible g (restState (d := d) g r p) :=
  ⟨hr, by rw [pressure_rest]; exact hp⟩

theorem decomp_rest (g : Gas) {r1 p1 r2 p2 : ℝ} (h1 : 0 < r1) (hp1 : 0 < p1) (h2 : 0 < r2) (hp2 : 0 < p2) :
    let Ui := restState (d := d) g r1 p1
    let Uk := restState (d := d) g r2 p2
    pairF (entropyVars g Uk - entropyVars g Ui) (Uk - Ui) = thQ g.γ r1 p1 r2 p2 ∧
      pairF (entropyVars g Uk - entropyVars g Ui) (enthalpyState g Uk - enthalpyState g Ui) =
        thQt g.γ r1 p1 r2 p2 := by
  intro Ui Uk
  have h := pair_decomp g (admissible_rest (d := d) g h1 hp1) (admissible_rest (d := d) g h2 hp2)
  simp only [rho_rest, pressure_rest, velV_rest, add_zero] at h
  exact h

theorem p1_1_6 : CFDLean.JST1.Spec.P1_1_6 := by
  intro d g ε hε
  have hγ := g.one_lt_γ
  have hlo := lam_quad hγ
  constructor
  · obtain ⟨h, hq, hlt, -⟩ := exists_jump hγ (thermoQ_pos hγ (lamLow_gap hγ) _) (pencil_eig hlo.1) hε
    have hD := decomp_rest (d := d) g one_pos one_pos (Real.exp_pos (h * (g.γ + 1 - 2 * lamLow g.γ)))
      (Real.exp_pos (h * (2 * (g.γ * (1 - lamLow g.γ)))))
    refine ⟨restState g 1 1, restState g (Real.exp (h * (g.γ + 1 - 2 * lamLow g.γ)))
      (Real.exp (h * (2 * (g.γ * (1 - lamLow g.γ))))), admissible_rest g one_pos one_pos,
      admissible_rest g (Real.exp_pos _) (Real.exp_pos _), ?_⟩
    rw [hD.1, hD.2]
    exact ⟨hq, hlt⟩
  · obtain ⟨h, hq, -, hlt⟩ := exists_jump hγ (thermoQ_pos hγ (lamHigh_gap hγ) _) (pencil_eig hlo.2) hε
    have hD := decomp_rest (d := d) g one_pos one_pos (Real.exp_pos (h * (g.γ + 1 - 2 * lamHigh g.γ)))
      (Real.exp_pos (h * (2 * (g.γ * (1 - lamHigh g.γ)))))
    refine ⟨restState g 1 1, restState g (Real.exp (h * (g.γ + 1 - 2 * lamHigh g.γ)))
      (Real.exp (h * (2 * (g.γ * (1 - lamHigh g.γ))))), admissible_rest g one_pos one_pos,
      admissible_rest g (Real.exp_pos _) (Real.exp_pos _), ?_⟩
    rw [hD.1, hD.2]
    exact ⟨hq, hlt⟩

/-! ### The entropy variables are the gradient of the entropy -/

theorem p1_1_0 : CFDLean.JST1.Spec.P1_1_0 := by
  intro d g U hU
  obtain ⟨hr, hp⟩ := hU
  have hg : g.γ - 1 ≠ 0 := by linarith [g.one_lt_γ]
  have hR : HasFDerivAt (fun V : State d => V .mass)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Channel d => ℝ) Channel.mass) U :=
    hasFDerivAt_apply _ _
  have hE : HasFDerivAt (fun V : State d => V .energy)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Channel d => ℝ) Channel.energy) U :=
    hasFDerivAt_apply _ _
  have hK : HasFDerivAt (fun V : State d => ∑ α, V (.momentum α) * V (.momentum α))
      (∑ α, (U (.momentum α) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Channel d => ℝ)
          (Channel.momentum α) +
        U (.momentum α) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Channel d => ℝ)
          (Channel.momentum α))) U :=
    HasFDerivAt.fun_sum (fun α _ => (hasFDerivAt_apply _ U).mul (hasFDerivAt_apply _ U))
  have hI := (hasDerivAt_inv (mul_ne_zero two_ne_zero hr.ne')).comp_hasFDerivAt U (hR.const_mul (2 : ℝ))
  have hP := (hE.sub (hK.mul hI)).const_mul (g.γ - 1)
  have hP' := hP.congr_of_eventuallyEq (f₁ := fun V : State d => pressure g V)
    (Filter.Eventually.of_forall fun V => by
      simp only [pressure, energy, Num.dot, mom, rho, div_eq_mul_inv]; rfl)
  have hS := (hP'.log hp.ne').sub ((hR.log hr.ne').const_mul g.γ)
  have hF := ((hR.neg.mul hS).mul_const ((g.γ - 1)⁻¹))
  have hF' := hF.congr_of_eventuallyEq (f₁ := entropyFun g)
    (Filter.Eventually.of_forall fun V => by
      simp only [entropyFun, physEntropy, rho, div_eq_mul_inv]; rfl)
  refine hF'.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  simp [pairCLM]
  rw [e1_sum_channel]
  simp only [entropyVars, physEntropy]
  have h1 : ∑ α, rho U * vel U α / pressure g U * x (.momentum α) =
      (∑ α, U (.momentum α) * x (.momentum α)) / pressure g U := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← e1_mom_eq hr.ne']
    ring
  have h2 : ∑ α, (U (.momentum α) * x (.momentum α) + U (.momentum α) * x (.momentum α)) =
      2 * ∑ α, U (.momentum α) * x (.momentum α) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring
  have h3 : Num.dot (vel U) (vel U) = (∑ α, U (.momentum α) * U (.momentum α)) / rho U ^ 2 := by
    have := dot_mom hr.ne'
    rw [eq_div_iff (by positivity), mul_comm, ← this]
    rfl
  rw [h1, h2, h3]
  unfold rho at hr ⊢
  generalize ∑ α, U (.momentum α) * x (.momentum α) = S
  generalize ∑ α, U (.momentum α) * U (.momentum α) = K
  generalize Real.log (pressure g U) = Lp
  generalize Real.log (U .mass) = Lr
  generalize pressure g U = p at hp ⊢
  generalize U .mass = r at hr ⊢
  field_simp
  ring

end CFDLean.JST1.Proofs
