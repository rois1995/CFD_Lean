import CFDLean.Papers.JST1.SST.Basic
import CFDLean.Papers.JST1.SST.Balance
import CFDLean.Papers.JST1.Viscous.Flux
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Statements of item 10 (P2): `lem:sstentropy` (395-407, proof 1115-1121), `prop:sstpde` (411-422, proof
1123-1133; pointwise), `lem:matched` (470-475, proof 1135-1138), `rem:sstconsistent` (513-520, proof 1155-1157),
`thm:sst` (482-499, proof 1140-1153). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- `e_E + e_k` and `e_ω` in the SST state space. -/
def nullE {d : ℕ} : SState d := Pi.single (SChan.flow .energy) 1 + Pi.single SChan.tke 1
def nullW {d : ℕ} : SState d := Pi.single SChan.omg 1

/-- P2-10.1: `ker T = span{e_E + e_k, e_ω}`, and `η0` is constant along it. -/
def P2_10_1 : Prop :=
  ∀ (d : ℕ) (g : Gas),
    (∀ U : SState d, hatState U = 0 ↔ ∃ a b : ℝ, U = a • nullE + b • nullW) ∧
    (∀ (U : SState d) (a b : ℝ), eta0 g (U + a • nullE + b • nullW) = eta0 g U)

/-- P2-10.2: `v^η` is the gradient of `η0`; `v^η · R = w(û) · (R_ρ, R_m, R_E - R_k)`; and the exact semi-discrete
rate `d/dt Σ_i V_i η0(U_i) = -Σ_i w_i · (R_ρ, R_m, R_E - R_k)_i` for `V_i dU_i/dt = -R_i`. -/
def P2_10_2 : Prop :=
  ∀ (d : ℕ) (g : Gas),
    (∀ U : SState d, SAdmissible g U → HasFDerivAt (eta0 g) (pairCLM (vEta g U)) U) ∧
    (∀ U R : SState d, pairF (vEta g U) R = pairF (entropyVars g (hatState U)) (hatState R)) ∧
    (∀ (ι : Type) [Fintype ι] (Ut : ι → ℝ → SState d) (V : ι → ℝ) (R : ι → SState d) (t : ℝ),
      (∀ i, SAdmissible g (Ut i t)) → (∀ i, V i ≠ 0) → (∀ i, HasDerivAt (Ut i) (-(V i)⁻¹ • R i) t) →
      HasDerivAt (fun s => ∑ i, V i * eta0 g (Ut i s))
        (-∑ i, pairF (entropyVars g (hatState (Ut i t))) (hatState (R i))) t)

/-- P2-10.3 (convexity, first-order form of "Hessian ⪰ 0 with null space `ker T`"): the admissible set is convex,
`η0` is convex on it, `(v^η_2 - v^η_1)·(U_2 - U_1) ≥ 0`, with equality iff `T U_1 = T U_2`. -/
def P2_10_3 : Prop :=
  ∀ (d : ℕ) (g : Gas),
    ConvexOn ℝ {U : SState d | SAdmissible g U} (eta0 g) ∧
    ∀ U1 U2 : SState d, SAdmissible g U1 → SAdmissible g U2 →
      0 ≤ pairF (vEta g U2 - vEta g U1) (U2 - U1) ∧
      (pairF (vEta g U2 - vEta g U1) (U2 - U1) = 0 ↔ hatState U1 = hatState U2)

/-- P2-10.4 (`prop:sstpde`, pointwise): `Π = -θ[μQ + (μ_t Q - P_k) + ε] - κ|∇T|²/(RT²) + r_D`, `r_D = 0` with
the turbulent diffusion in the energy flux; `Q ≥ 0` (`d ≤ 3`); `Π ≤ 0` then if `P_k ≤ μ_t Q`; and with
`P_k ≤ μ_t 2S:S` the remainder is at most `θ (2/3) μ_t (div v)²`. -/
def P2_10_4 : Prop :=
  ∀ (d : ℕ) (D : SSTPoint.Data d), 0 < D.R → 0 < D.T →
    let θ := SSTPoint.theta D
    SSTPoint.Pi D = -θ * (D.μ * SSTPoint.Q D + (D.μt * SSTPoint.Q D - D.Pk) + D.ε) -
        D.κ * Num.dot D.GT D.GT / (D.R * D.T ^ 2) +
        (if D.withDk then 0 else -(D.Dk * Num.dot D.Gk (SSTPoint.Gtheta D))) ∧
    (d ≤ 3 → 0 ≤ SSTPoint.Q D) ∧
    (d ≤ 3 → D.withDk = true → 0 ≤ D.μ → 0 ≤ D.κ → 0 ≤ D.ε → D.Pk ≤ D.μt * SSTPoint.Q D →
      SSTPoint.Pi D ≤ 0) ∧
    (0 ≤ D.μt → D.Pk ≤ D.μt * (2 * SSTPoint.SS D) →
      -θ * (D.μt * SSTPoint.Q D - D.Pk) ≤ θ * ((2 / 3) * D.μt * SSTPoint.divv D ^ 2))

/-- P2-10.5 (`lem:matched`): with antisymmetric mass fluxes and upwind `k`, the matched `k` transport is
conservative; a uniform `k` equal to the inflow data gives `X_i = k R_ρ,i`; at a wall node with `k_i = 0`, no
boundary mass flux and `k ≥ 0`, `X_i ≤ 0` (M5 with `k_D = 0`). -/
def P2_10_5 : Prop :=
  ∀ (ι : Type) [Fintype ι] (mdot : ι → ι → ℝ) (kv kin bmass : ι → ℝ),
    (∀ i j, mdot j i = -mdot i j) →
    let kup : ι → ι → ℝ := fun i j => if 0 ≤ mdot i j then kv i else kv j
    let kb : ι → ℝ := fun i => if 0 ≤ bmass i then kv i else kin i
    let X : ι → ℝ := fun i => (∑ j, mdot i j * kup i j) + bmass i * kb i
    let Rrho : ι → ℝ := fun i => (∑ j, mdot i j) + bmass i
    (∑ i, ∑ j, mdot i j * kup i j) = 0 ∧
    (∀ k0 : ℝ, (∀ i, kv i = k0) → (∀ i, kin i = k0) → ∀ i, X i = k0 * Rrho i) ∧
    (∀ i, kv i = 0 → bmass i = 0 → (∀ j, 0 ≤ kv j) → X i ≤ 0)

/-- P2-10.6 (`rem:sstconsistent`): `P_k = max(0, min(P*, c_l ε))` with `ε, P* ≥ 0` gives (M4) `P_k - ε ≤ P*`. -/
def P2_10_6 : Prop :=
  ∀ (Pst cl ε : ℝ), 0 ≤ ε → 0 ≤ Pst → max 0 (min Pst (cl * ε)) - ε ≤ Pst

/-- P2-10.7: the Galerkin dissipation with `μ + μ_t` splits into the laminar part and the `μ_t` part `D_t`, both
`≥ 0` (`K` is linear in `μ`). -/
def P2_10_7 : Prop :=
  ∀ (d : ℕ) (R μ μt κ : ℝ) (wb : State d) (G : Matrix (Channel d) (Fin d) ℝ),
    d ≤ 3 → 0 < R → 0 ≤ μ → 0 ≤ μt → 0 ≤ κ → wb .energy < 0 →
    frob G (viscFlux ⟨R, μ + μt, κ⟩ wb G) = frob G (viscFlux ⟨R, μ, κ⟩ wb G) + frob G (viscFlux ⟨R, μt, 0⟩ wb G) ∧
    0 ≤ frob G (viscFlux ⟨R, μ, κ⟩ wb G) ∧ 0 ≤ frob G (viscFlux ⟨R, μt, 0⟩ wb G)

/-- P2-10.8 (`thm:sst`): the hat scheme enters through its proved balance (items 2, 4, 8, 9) as a hypothesis;
`R_E = R̂_E + X`; `R_k = C_k + B_k + D^h_k - V S_k` off `𝒟` and `k_D R_ρ` on `𝒟`; `w_E = -2β`. Under (M1)-(M5)
(here: `X = C + B + D^h` off `𝒟`, `S_k ≤ P*`, `X - k_D R_ρ ≤ 0` on `𝒟`), `Σ D_t = Σ 2β V P*` and (W_t), the rate
obeys the bound of the theorem, and every term except `B̂` and `Π̂^(4)` is `≤ 0`. Also the two sufficient
conditions for (W_t). -/
def P2_10_8 : Prop :=
  (∀ (ι C : Type) [Fintype ι] [Fintype C] (d : ℕ) (w Rhat : ι → State d)
    (X Ck Bk Dh Sk Rrho Pst V β2 : ι → ℝ) (inD : ι → Bool) (kD : ℝ) (Dgal Dt PiW : C → ℝ) (Bhat Pi2 Pi4 : ℝ),
    (∀ i, w i .energy = -β2 i) → (∀ i, 0 ≤ β2 i) → (∀ i, 0 ≤ V i) → (∀ i, 0 ≤ Pst i) →
    -(∑ i, pairF (w i) (Rhat i)) ≤ Bhat + Pi2 + Pi4 - ∑ T, (Dgal T - PiW T) → Pi2 ≤ 0 →
    (∀ i, inD i = false → X i = Ck i + Bk i + Dh i) →
    (∀ i, inD i = false → Sk i ≤ Pst i) →
    (∀ i, inD i = true → X i - kD * Rrho i ≤ 0) →
    (∑ T, Dt T) = ∑ i, β2 i * V i * Pst i →
    (∀ T, PiW T ≤ Dgal T - Dt T) →
    let Rk : ι → ℝ := fun i => if inD i then kD * Rrho i else Ck i + Bk i + Dh i - V i * Sk i
    let rate := -∑ i, pairF (w i) (Rhat i + (X i - Rk i) • eE)
    rate ≤ Bhat + Pi2 + Pi4 - (∑ T, (Dgal T - Dt T - PiW T)) -
        (∑ i, if inD i then 0 else β2 i * V i * (Pst i - Sk i)) - (∑ i, if inD i then β2 i * V i * Pst i else 0) ∧
    (∀ T, 0 ≤ Dgal T - Dt T - PiW T) ∧
    (∀ i, 0 ≤ (if inD i then 0 else β2 i * V i * (Pst i - Sk i))) ∧
    (∀ i, 0 ≤ (if inD i then β2 i * V i * Pst i else 0))) ∧
  (∀ (Dgal Dt PiW c : ℝ),
    (PiW = 0 → Dt ≤ Dgal → PiW ≤ Dgal - Dt) ∧
    (0 < c → PiW ≤ Dgal / c → Dt ≤ (1 - 1 / c) * Dgal → PiW ≤ Dgal - Dt))

end CFDLean.JST1.Spec
