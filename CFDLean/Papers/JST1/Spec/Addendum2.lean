import CFDLean.Papers.JST1.Spec.Item9
import CFDLean.Papers.JST1.Spec.Item10
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! P2 addendum (review `reviews/P2/Review.md`, S1-S4): stronger forms of `thm:wall` sharpness and `thm:sst`, and
the admissibility step of `thm:closure` (line 1025). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec
open CFDLean.JST1.Wall

/-- Vertex mean `w̄_T`. -/
def vmean {d : ℕ} (w : Fin (d + 1) → State d) : State d := (1 / ((d : ℝ) + 1)) • ∑ a, w a

/-- P2-8.0b (`thm:closure`, line 1025): a convex combination of entropy variables with `w_E < 0` has `w_E < 0`, so
P2-8.0 gives the projected state `ũ_q` that P2-8.1 uses. -/
def P2_8_0b : Prop :=
  ∀ (ι : Type) [Fintype ι] (d : ℕ) (w : ι → State d) (φ : ι → ℝ),
    (∀ k, w k .energy < 0) → (∀ k, 0 ≤ φ k) → ∑ k, φ k = 1 → (∑ k, φ k • w k) .energy < 0

/-- P2-9.2b (`thm:wall`, "c ≥ 1 is sharp for a single wall element", lines 341-342, 1086-1090): with the
Navier-Stokes `K(w̄_T)` of the nodal values themselves, `μ > 0`, the adiabatic no-slip projector and `c < 1`, there
are admissible nodal entropy variables (`w_E < 0`) with `D^gal_T - Π^w_T < 0`. -/
def P2_9_2b : Prop :=
  ∀ (d : ℕ) (Pv : ViscParams) (T : Simplex d) (o : Fin (d + 1)) (c : ℝ),
    1 ≤ d → d ≤ 3 → 0 < Pv.μ → 0 ≤ Pv.κ → 0 < Pv.R → T.Nondeg → 0 < c → c < 1 →
    ∃ w : Fin (d + 1) → State d, (∀ a, w a .energy < 0) ∧
      Dgal T (viscFlux Pv (vmean w)) w - PiW T (viscFlux Pv (vmean w)) (momProj d) 0 {o} c w < 0

/-- P2-10.8b (`thm:sst`, lines 496-498, with the element operators): on one simplex with admissible nodal values,
`K = K(w̄_T)` with `μ + μ_t`, `D_t` the `μ_t` part, and any wall projector: `0 ≤ D_t ≤ D^gal`; without wall faces
`Π^w = 0` and (W_t) holds; with `c ≥ 1` and `D_t ≤ (1 - 1/c) D^gal`, (W_t) holds (by P2-9.1). -/
def P2_10_8b : Prop :=
  ∀ (d : ℕ) (T : Simplex d) (R μ μt κ c : ℝ) (P : Matrix (Channel d) (Channel d) ℝ) (gw : State d)
    (walls : Finset (Fin (d + 1))) (w : Fin (d + 1) → State d),
    1 ≤ d → d ≤ 3 → 0 < R → 0 ≤ μ → 0 ≤ μt → 0 ≤ κ → T.Nondeg → 0 < c → (∀ a, w a .energy < 0) →
    P.transpose = P → P * P = P → P.mulVec gw = gw →
    let K := viscFlux ⟨R, μ + μt, κ⟩ (vmean w)
    let Kt := viscFlux ⟨R, μt, 0⟩ (vmean w)
    let Dg := Dgal T K w
    let Dt := Dgal T Kt w
    let Pw := PiW T K P gw walls c w
    0 ≤ Dt ∧ Dt ≤ Dg ∧ (walls = ∅ → Pw = 0 ∧ Pw ≤ Dg - Dt) ∧
      (1 ≤ c → Dt ≤ (1 - 1 / c) * Dg → Pw ≤ Dg - Dt)

/-- P2-10.8c (`thm:sst`, chained with `lem:sstentropy`): for differentiable SST trajectories with
`V_i dU_i/dt = -R_i`, whose hat residual is `R̂_i + (X_i - R_k,i) e_E` (energy row `R̂_E + X`, `k` row `R_k`), the
rate `d/dt Σ V_i η0(U_i)` exists and obeys the bound of P2-10.8 under the same hypotheses. -/
def P2_10_8c : Prop :=
  ∀ (ι C : Type) [Fintype ι] [Fintype C] (d : ℕ) (g : Gas) (Ut : ι → ℝ → SState d) (Vv : ι → ℝ)
    (R : ι → SState d) (t : ℝ) (Rhat : ι → State d)
    (X Ck Bk Dh Sk Rrho Pst : ι → ℝ) (inD : ι → Bool) (kD : ℝ) (Dgal Dt PiW : C → ℝ) (Bhat Pi2 Pi4 : ℝ),
    (∀ i, SAdmissible g (Ut i t)) → (∀ i, 0 < Vv i) → (∀ i, HasDerivAt (Ut i) (-(Vv i)⁻¹ • R i) t) →
    let w : ι → State d := fun i => entropyVars g (hatState (Ut i t))
    let β2 : ι → ℝ := fun i => -(w i .energy)
    let Rk : ι → ℝ := fun i => if inD i then kD * Rrho i else Ck i + Bk i + Dh i - Vv i * Sk i
    (∀ i, hatState (R i) = Rhat i + (X i - Rk i) • eE) → (∀ i, 0 ≤ Pst i) →
    -(∑ i, pairF (w i) (Rhat i)) ≤ Bhat + Pi2 + Pi4 - ∑ T, (Dgal T - PiW T) →
    (∀ i, inD i = false → X i = Ck i + Bk i + Dh i) →
    (∀ i, inD i = false → Sk i ≤ Pst i) →
    (∀ i, inD i = true → X i - kD * Rrho i ≤ 0) →
    (∑ T, Dt T) = ∑ i, β2 i * Vv i * Pst i →
    (∀ T, PiW T ≤ Dgal T - Dt T) →
    ∃ r : ℝ, HasDerivAt (fun s => ∑ i, Vv i * eta0 g (Ut i s)) r t ∧
      r ≤ Bhat + Pi2 + Pi4 - (∑ T, (Dgal T - Dt T - PiW T)) -
        (∑ i, if inD i then 0 else β2 i * Vv i * (Pst i - Sk i)) - (∑ i, if inD i then β2 i * Vv i * Pst i else 0)

end CFDLean.JST1.Spec
