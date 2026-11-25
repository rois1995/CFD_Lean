import CFDLean.Papers.JST1.Euler.IsmailRoe
import CFDLean.Discrete.Mesh
set_option cleanup.letToHave false -- v4.36 port: keep the v4.19 `let` binders (no let-to-have cleanup)

/-! Frozen statements of item 2: `lem:ec` (lines 153-158, proof 881-884) and `prop:consistency`(a) (line 278,
proof 928-930). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num
namespace CFDLean.JST1.Spec

/-- P1-2.0: `ψ = w·F - Q` with `Q = U v`. -/
def P1_2_0 : Prop :=
  ∀ (d : ℕ) (g : Gas) (U : State d) (y : Vec d), Admissible g U →
    pairF (entropyVars g U) (physFlux g U y) - entropyFun g U * Num.dot (vel U) y = Num.dot (fluxPot U) y

/-- P1-2.1: antisymmetric pair fluxes: conservation and production. -/
def P1_2_1 : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (F : ι → ι → κ → ℝ) (w : ι → κ → ℝ),
    (∀ i k, F k i = -F i k) →
    (∑ i, ∑ k, F i k) = 0 ∧
    -(∑ i, pairF (w i) (∑ k, F i k)) = (1 / 2) * ∑ i, ∑ k, pairF (w k - w i) (F i k)

/-- P1-2.2 (`lem:ec`): an entropy-conservative central part produces only `Σ_i ψ_i·β_i`. -/
def P1_2_2 : Prop :=
  ∀ (ι S κ : Type) [Fintype ι] [Fintype κ] (d : ℕ) (w : S → κ → ℝ) (ψ : S → Vec d)
    (Fec : S → S → Vec d → κ → ℝ) (n : ι → ι → Vec d) (u : ι → S),
    (∀ i k, n k i = -n i k) →
    (∀ a b y, Fec a b y = Fec b a y) →
    (∀ a b, IsLinearMap ℝ (Fec a b)) →
    (∀ a b y, pairF (w b - w a) (Fec a b y) = Num.dot (ψ b - ψ a) y) →
    let beta : ι → Vec d := fun i => -∑ k, n i k
    let Rc : ι → κ → ℝ := fun i => ∑ k, Fec (u i) (u k) (n i k)
    (-(∑ i, pairF (w (u i)) (Rc i))) = (1 / 2) * ∑ i, ∑ k, Num.dot (ψ (u k) - ψ (u i)) (n i k) ∧
    (1 / 2) * ∑ i, ∑ k, Num.dot (ψ (u k) - ψ (u i)) (n i k) = ∑ i, Num.dot (ψ (u i)) (beta i)

/-- P1-2.3: the P1 operator of any dual has `Σ_k n_ik = -β_i`; at a closed vertex `β_i = 0`. -/
def P1_2_3 : Prop :=
  ∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d)
    (W : C → Fin (d + 1) → ℝ), M.Valid → (∀ T, ∑ a, W T a = M.vol T) →
    (∀ i, ∑ k, M.nW W i k = -M.beta i) ∧ (∀ i, M.Closed i → M.beta i = 0)

/-- P1-2.4: log mean. -/
def P1_2_4 : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    logMean a b = logMean b a ∧ logMean a a = a ∧ 0 < logMean a b ∧
    b - a = logMean a b * (Real.log b - Real.log a)

/-- P1-2.5: the Ismail-Roe flux is entropy conservative (Tadmor), symmetric, linear in `y`, consistent. -/
def P1_2_5 : Prop :=
  ∀ (d : ℕ) (g : Gas),
    (∀ (Ua Ub : State d) (y : Vec d), Admissible g Ua → Admissible g Ub →
      pairF (entropyVars g Ub - entropyVars g Ua) (ismailRoe g Ua Ub y) = Num.dot (fluxPot Ub - fluxPot Ua) y) ∧
    (∀ (Ua Ub : State d) (y : Vec d), ismailRoe g Ua Ub y = ismailRoe g Ub Ua y) ∧
    (∀ Ua Ub : State d, IsLinearMap ℝ (ismailRoe g Ua Ub)) ∧
    (∀ (U : State d) (y : Vec d), Admissible g U → ismailRoe g U U y = physFlux g U y)

/-- P1-2.6 (conservation): central flux plus scalar dissipation with symmetric coefficients. -/
def P1_2_6 : Prop :=
  ∀ (ι S κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] (d : ℕ) (Fec : S → S → Vec d → κ → ℝ)
    (n : ι → ι → Vec d) (u : ι → S) (ut : ι → κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ)
    (Nstar : ι → Finset ι) (b : ι → κ → ℝ),
    (∀ i k, n k i = -n i k) → (∀ a b y, Fec a b y = Fec b a y) → (∀ a b, IsLinearMap ℝ (Fec a b)) →
    (∀ i k, lam k i = lam i k) → (∀ i k, eps2 k i = eps2 i k) → (∀ i k, eps4 k i = eps4 i k) →
    let L : ι → κ → ℝ := fun i => ∑ k ∈ Nstar i, (ut k - ut i)
    let F : ι → ι → κ → ℝ := fun i k =>
      Fec (u i) (u k) (n i k) + lam i k • (eps2 i k • (ut i - ut k) - eps4 i k • (L i - L k))
    (∀ i k, F k i = -F i k) ∧ ∑ i, (-(∑ k, F i k) - b i) = -∑ i, b i

/-- P1-2.7 (free stream): a uniform state with the matching boundary data has zero residual. -/
def P1_2_7 : Prop :=
  ∀ (ι S κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] (d : ℕ) (Fec : S → S → Vec d → κ → ℝ)
    (phys : S → Vec d → κ → ℝ) (n : ι → ι → Vec d) (U : S) (ut0 : κ → ℝ) (lam eps2 eps4 : ι → ι → ℝ)
    (Nstar : ι → Finset ι),
    (∀ a b, IsLinearMap ℝ (Fec a b)) → (∀ y, Fec U U y = phys U y) →
    let beta : ι → Vec d := fun i => -∑ k, n i k
    let L : ι → κ → ℝ := fun i => ∑ _k ∈ Nstar i, (ut0 - ut0)
    let F : ι → ι → κ → ℝ := fun i k =>
      Fec U U (n i k) + lam i k • (eps2 i k • (ut0 - ut0) - eps4 i k • (L i - L k))
    ∀ i, -(∑ k, F i k) - phys U (beta i) = 0

end CFDLean.JST1.Spec
