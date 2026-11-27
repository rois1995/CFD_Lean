import CFDLean.Schemes.Euler.FV1D
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace CFDLean.Euler1D

private abbrev admiss (γ : ℝ) (x : Vector 3) := (decode x).Admissible γ

private theorem pressure_eq (γ : ℝ) (x : Vector 3) :
    (decode x).pressure γ = (γ-1) * (x 2 - x 1 ^ 2 / (2*x 0)) := by
  simp [Conservative.pressure, squareSum, decode]

theorem endpointSpeed_pos {γ : ℝ} (hg : 1 < γ) {x : Vector 3} (h : (decode x).Admissible γ) :
    0 < endpointSpeed γ x := by
  exact add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.sqrt_pos.2 (div_pos (mul_pos (by linarith) h.2) h.1))

theorem faceSpeed_pos {γ : ℝ} (hg : 1 < γ) {x y : Vector 3} (hx : (decode x).Admissible γ) :
    0 < speed γ x y := lt_of_lt_of_le (endpointSpeed_pos hg hx) (le_max_left _ _)

private theorem det_iff {γ : ℝ} (hg : 1 < γ) (x : Vector 3) :
    admiss γ x ↔ 0 < x 0 ∧ 0 < 2*x 0*x 2 - x 1^2 := by
  change (0 < x 0 ∧ 0 < (decode x).pressure γ) ↔ _
  rw [pressure_eq, mul_pos_iff_of_pos_left (sub_pos.mpr hg), sub_pos]
  constructor <;> rintro ⟨hr, h⟩ <;> refine ⟨hr, ?_⟩
  · have := (div_lt_iff₀ (by positivity : 0 < 2*x 0)).mp h
    linarith
  · apply (div_lt_iff₀ (by positivity : 0 < 2*x 0)).mpr
    linarith

/-- A velocity test makes strict internal energy a family of linear inequalities in the state. -/
private def internal (x : Vector 3) (w : ℝ) := x 2 - w*x 1 + w^2*x 0/2

private theorem linear_iff {γ : ℝ} (hg : 1 < γ) (x : Vector 3) :
    admiss γ x ↔ 0 < x 0 ∧ ∀ w, 0 < internal x w := by
  rw [det_iff hg]
  constructor
  · rintro ⟨hr, hd⟩
    refine ⟨hr, fun w => ?_⟩
    have he : 2*x 0*internal x w = (2*x 0*x 2-x 1^2) + (w*x 0-x 1)^2 := by unfold internal; ring
    apply (mul_pos_iff_of_pos_left (by positivity : 0 < 2*x 0)).mp
    rw [he]
    exact add_pos_of_pos_of_nonneg hd (sq_nonneg _)
  · rintro ⟨hr, h⟩
    refine ⟨hr, ?_⟩
    have he : 2*x 0*internal x (x 1/x 0) = 2*x 0*x 2-x 1^2 := by
      unfold internal
      field_simp [ne_of_gt hr]; ring
    rw [← he]
    exact mul_pos (by positivity) (h _)

private theorem split_admiss {γ : ℝ} (hg : 1 < γ) (x : Vector 3) (hx : admiss γ x)
    (a t : ℝ) (ha : endpointSpeed γ x ≤ a) (ht : t = 1/a ∨ t = -(1/a)) :
    admiss γ (x + t • flux γ x) := by
  let r := x 0
  let m := x 1
  let e := x 2
  let p := (decode x).pressure γ
  let v := m/r
  let c := Real.sqrt (γ*p/r)
  let k := 1+t*v
  let D := 2*r*e-m^2
  have hr : 0 < r := hx.1
  have hp : 0 < p := hx.2
  have hD : 0 < D := ((det_iff hg x).mp hx).2
  have hgm : 0 < γ-1 := sub_pos.mpr hg
  have hrad : 0 < γ*p/r := div_pos (mul_pos (by linarith) hp) hr
  have hc : 0 < c := Real.sqrt_pos.2 hrad
  have hc2 : c^2 = γ*p/r := Real.sq_sqrt hrad.le
  have hav : |v|+c ≤ a := ha
  have hap : 0 < a := lt_of_lt_of_le (endpointSpeed_pos hg hx) ha
  have hk : c ≤ a*k := by
    unfold k
    rcases ht with h | h <;> rw [h]
    · have hid : a*(1+1/a*v) = a+v := by field_simp [ne_of_gt hap]
      rw [hid]; linarith [neg_abs_le v]
    · have hid : a*(1+ -(1/a)*v) = a-v := by field_simp [ne_of_gt hap]; ring
      rw [hid]; linarith [le_abs_self v]
  have hkp : 0 < k := (mul_pos_iff_of_pos_left hap).mp (lt_of_lt_of_le hc hk)
  have hdet : D = 2*r*p/(γ-1) := by
    have he : p = (γ-1)*(e-m^2/(2*r)) := pressure_eq γ x
    dsimp only [D]
    rw [he]
    field_simp [ne_of_gt hr, ne_of_gt hgm]
  have hmargin : p^2 < c^2*D := by
    calc
      p^2 = 1*p^2 := (one_mul _).symm
      _ < (2*γ/(γ-1))*p^2 := by
        apply mul_lt_mul_of_pos_right _ (sq_pos_of_pos hp)
        apply (lt_div_iff₀ hgm).2
        linarith
      _ = c^2*D := by rw [hc2, hdet]; field_simp [ne_of_gt hr, ne_of_gt hgm]
  have ht2 : (a*t)^2 = 1 := by
    rcases ht with h | h <;> rw [h] <;> field_simp [ne_of_gt hap]
  have hscaled : 0 < a^2*(k^2*D-t^2*p^2) := by
    have hbound : c^2*D ≤ (a*k)^2*D :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le hk 2) hD.le
    calc
      0 < (a*k)^2*D - p^2 := by linarith
      _ = a^2*(k^2*D-t^2*p^2) := by linear_combination p^2 * ht2
  have hpositive := (mul_pos_iff_of_pos_left (sq_pos_of_pos hap)).mp hscaled
  have hrv : r*v = m := by dsimp [v]; field_simp [ne_of_gt hr]
  have hf : flux γ x = ![m, m*v+p, (e+p)*v] := by
    funext j
    fin_cases j <;> simp [flux, physicalFlux, dot, encode, decode, p, r, m, e, v, Matrix.cons_val_two]
  rw [det_iff hg, hf]
  change 0 < r+t*m ∧ 0 < 2*(r+t*m)*(e+t*((e+p)*v))-(m+t*(m*v+p))^2
  constructor
  · have he : r*k = r+t*m := by dsimp only [k]; linear_combination t * hrv
    rw [← he]
    exact mul_pos hr hkp
  · have he : 2*(r+t*m)*(e+t*((e+p)*v))-(m+t*(m*v+p))^2 = k^2*D-t^2*p^2 := by
      dsimp only [k, D]
      rw [← hrv]
      ring
    rwa [he]

private theorem weighted_pos {b l r x y z : ℝ}
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hr : 0 ≤ r) (hs : b+l+r = 1)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 < b*x+l*y+r*z := by
  have hb' := mul_nonneg hb hx.le
  have hl' := mul_nonneg hl hy.le
  have hr' := mul_nonneg hr hz.le
  rcases hb.eq_or_lt with h | h
  · rcases hl.eq_or_lt with j | j
    · have : 0 < r := by linarith
      linarith [mul_pos this hz]
    · linarith [mul_pos j hy]
  · linarith [mul_pos h hx]

private theorem combine {γ b l r : ℝ} (hg : 1 < γ) (hb : 0 ≤ b) (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hs : b+l+r = 1) {x y z : Vector 3} (hx : admiss γ x) (hy : admiss γ y) (hz : admiss γ z) :
    admiss γ (b • x + l • y + r • z) := by
  rw [linear_iff hg] at hx hy hz ⊢
  refine ⟨weighted_pos hb hl hr hs hx.1 hy.1 hz.1, fun w => ?_⟩
  have he : internal (b • x + l • y + r • z) w = b*internal x w+l*internal y w+r*internal z w := by
    simp only [internal, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact weighted_pos hb hl hr hs (hx.2 w) (hy.2 w) (hz.2 w)

/-- The speed of the actual old-state face from j to its periodic successor. -/
def rightSpeed {N : ℕ} [NeZero N] (γ : ℝ) (U : ZMod N → Conservative 1) (j : ZMod N) : ℝ :=
  speed γ (encode (U j)) (encode (U ((Periodic.zmodGrid N).next j)))

/-- FVP-P. Both adjacent old-state speeds enter the sufficient non-strict local CFL bound. -/
theorem step_admissible {N : ℕ} [NeZero N] (γ dx dt : ℝ) (hg : 1 < γ) (hdx : 0 < dx)
    (hdt : 0 ≤ dt) (U : ZMod N → Conservative 1) (hU : ∀ j, (U j).Admissible γ)
    (hcfl : ∀ j, dt*(rightSpeed γ U ((Periodic.zmodGrid N).prev j)+rightSpeed γ U j) ≤ 2*dx)
    (i : ZMod N) : (step γ dx dt U i).Admissible γ := by
  let g := Periodic.zmodGrid N
  let X := fun j => encode (U j)
  let L := X (g.prev i)
  let C := X i
  let R := X (g.next i)
  let a := speed γ L C
  let b := speed γ C R
  let s := dt/dx
  have adm (j : ZMod N) : admiss γ (X j) := by simpa [admiss, X] using hU j
  have ha : 0 < a := faceSpeed_pos hg (adm (g.prev i))
  have hb : 0 < b := faceSpeed_pos hg (adm i)
  have hspeed : rightSpeed γ U (g.prev i) = a := by
    change speed γ L (X (g.next (g.prev i))) = a
    rw [Periodic.Grid.next_prev]
  have hbound := hcfl i
  rw [hspeed] at hbound
  change dt*(a+b) ≤ 2*dx at hbound
  have hs : 0 ≤ s := div_nonneg hdt hdx.le
  have hcenter : 0 ≤ 1-s*(a+b)/2 := by
    have he : s*(a+b) = (dt*(a+b))/dx := by dsimp [s]; ring
    have h := (div_le_iff₀ hdx).mpr hbound
    rw [he]
    linarith
  have hleft := split_admiss hg L (adm _) a (1/a) (le_max_left _ _) (Or.inl rfl)
  have hright := split_admiss hg R (adm _) b (-(1/b)) (le_max_right _ _) (Or.inr rfl)
  have hmix := combine hg hcenter (show 0 ≤ s*a/2 by positivity) (show 0 ≤ s*b/2 by positivity)
    (by ring) (adm i) hleft hright
  change admiss γ (FV1D.step g (flux γ) (speed γ) dx dt X i)
  suffices he : FV1D.step g (flux γ) (speed γ) dx dt X i =
      (1-s*(a+b)/2) • C + (s*a/2) • (L+(1/a) • flux γ L) +
        (s*b/2) • (R+(-(1/b)) • flux γ R) by
    rw [he]
    exact hmix
  funext k
  simp only [FV1D.step, FV1D.face, Periodic.Grid.next_prev, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change C k-s*((1/2*((flux γ C) k+(flux γ R) k)-b/2*(R k-C k))-
    (1/2*((flux γ L) k+(flux γ C) k)-a/2*(C k-L k))) = _
  field_simp [ne_of_gt ha, ne_of_gt hb] <;> ring

end CFDLean.Euler1D
