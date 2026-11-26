import CFDLean.Papers.JST1.Spec.Item7
set_option cleanup.letToHave false -- keep the `let` binders of the statements (as P1-P3)

/-! Statements of item 16 (P4): `prop:consistency`(b), (c) (lines 282-298, proof 938-955), the parts not stated in P2
(P2-6.7 and P2-7.4 are the other parts). -/
noncomputable section
open scoped BigOperators
open CFDLean.Num Filter Topology Asymptotics
namespace CFDLean.JST1.Spec

/-- Barycentric coordinate `φ_b(x) = δ_b0 + g_b · (x - x_0)` of a simplex (affine with gradient `g_b`). -/
def bary {d : ℕ} (T : Simplex d) (b : Fin (d + 1)) (x : Vec d) : ℝ :=
  (if b = 0 then 1 else 0) + Num.dot (T.grad b) (x - T.x 0)

/-- P1 interpolant `F_h(x) = Σ_b φ_b(x) F_b` of nodal fluxes on a simplex. -/
def p1Interp {κ : Type} {d : ℕ} (T : Simplex d) (F : Fin (d + 1) → Matrix κ (Fin d) ℝ) (x : Vec d) :
    Matrix κ (Fin d) ℝ :=
  ∑ b, bary T b x • F b

/-- P4-16.1 (`prop:consistency`(b), "`= ∫_Ω φ_i ∇·F_h` with `F_h` the P1 interpolant, exact for linear `F`"): on a
nondegenerate simplex the P1 interpolant takes the nodal values, has the constant partial derivatives
`∂_β F_h = Σ_b g_bβ F_b` (so `∇·F_h = Σ_b F_b g_b` on `T`), and equals every affine flux whose nodal values it takes.
On a valid mesh, at a closed vertex, the mean flux is `Σ_{T ∋ i} ω_T m_T ∇·F_h|_T`, i.e. `∫_Ω φ_i ∇·F_h` with the
quadrature fact `∫_T φ_i = m_T` (not formalized: decision D1 of `P4-proposal.md`). -/
def P4_16_1 : Prop :=
  (∀ (κ : Type) [Fintype κ] (d : ℕ) (T : Simplex d) (F : Fin (d + 1) → Matrix κ (Fin d) ℝ), T.Nondeg →
    (∀ a, p1Interp T F (T.x a) = F a) ∧
    (∀ (x : Vec d) (β : Fin d) (c : κ) (γ : Fin d),
      HasDerivAt (fun s : ℝ => p1Interp T F (x + s • Pi.single β 1) c γ) (∑ b, T.grad b β * F b c γ) 0) ∧
    (∀ (F0 : Matrix κ (Fin d) ℝ) (A : Vec d →ₗ[ℝ] Matrix κ (Fin d) ℝ),
      (∀ b, F b = F0 + A (T.x b)) → ∀ x, p1Interp T F x = F0 + A x)) ∧
  (∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
    (F : ι → Matrix κ (Fin d) ℝ) (i : ι), M.Valid → M.Closed i →
    (∑ k, ((1 / 2 : ℝ) • (F i + F k)).mulVec (M.n i k)) = fun c =>
      ∑ T, ∑ a, if M.vert T a = i then
        M.ω T * M.m T * ∑ β, ∑ b, (M.simplex T).grad b β * F (M.vert T b) c β else 0)

/-- P4-16.2 (`prop:consistency`(b), last clause; proof: "expand about the midpoint, the odd terms cancel"): a
symmetric, consistent two-point flux that is `C²` near the diagonal differs from the mean flux by
`O(|u_k - u_i|²)`, locally uniformly: big-O at `(u0, u0)` for every `u0` of the open set where it is smooth. Stated
for an abstract flux, as the paper's proof argues; that the scheme's Ismail-Roe flux (piecewise log mean) is `C²`
across the diagonal is not stated (`PAPER_GAPS.md` G6). -/
def P4_16_2 : Prop :=
  ∀ (E Fs : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Fs] [NormedSpace ℝ Fs]
    (Fec : E → E → Fs) (F : E → Fs) (Ω : Set E) (u0 : E),
    IsOpen Ω → u0 ∈ Ω → ContDiffOn ℝ 2 (Function.uncurry Fec) (Ω ×ˢ Ω) →
    (∀ a ∈ Ω, ∀ b ∈ Ω, Fec a b = Fec b a) → (∀ a ∈ Ω, Fec a a = F a) →
    (fun p : E × E => Fec p.1 p.2 - (1 / 2 : ℝ) • (F p.1 + F p.2)) =O[𝓝 (u0, u0)] (fun p => ‖p.2 - p.1‖ ^ 2)

/-- Pressure sensor `ς_i = |Σ_{k∈ℰ(i)} (p_k - p_i)| / Σ_{k∈ℰ(i)} (p_k + p_i)`. -/
def sensor {ι : Type} (E : ι → Finset ι) (p : ι → ℝ) (i : ι) : ℝ :=
  |∑ k ∈ E i, (p k - p i)| / ∑ k ∈ E i, (p k + p i)

/-- `τ_ik = 3(|ℰ(i)| + |ℰ(k)|) / (|ℰ(i)| |ℰ(k)|)`. -/
def tauC {ι : Type} (E : ι → Finset ι) (i k : ι) : ℝ :=
  3 * (((E i).card : ℝ) + (E k).card) / (((E i).card : ℝ) * (E k).card)

/-- `ε2_ik = κ2 ½(ς_i + ς_k) τ_ik`. -/
def eps2C {ι : Type} (κ2 : ℝ) (E : ι → Finset ι) (p : ι → ℝ) (i k : ι) : ℝ :=
  κ2 * ((1 / 2) * (sensor E p i + sensor E p k)) * tauC E i k

/-- `ε4_ik = max(0, κ4 - ε2_ik) τ_ik² / 4`. -/
def eps4C {ι : Type} (κ2 κ4 : ℝ) (E : ι → Finset ι) (p : ι → ℝ) (i k : ι) : ℝ :=
  max 0 (κ4 - eps2C κ2 E p i k) * tauC E i k ^ 2 / 4

/-- Euclidean norm of a state vector. -/
def snorm {κ : Type} [Fintype κ] (x : κ → ℝ) : ℝ := Real.sqrt (pairF x x)

/-- P4-16.3 (`prop:consistency`(c), weak effect): with the paper's `ε2, ε4` (sensor from positive pressures, edge
counts `1 ≤ |ℰ(i)| ≤ n_E`), `ε2 ≤ 6κ2` and `ε4 ≤ 9κ4`; and with `λ_ik = Φ_ik λ̂_ik` (`0 ≤ Φ ≤ Φmax`, `λ̂` on `ν_ik`,
`σ ≤ σmax`), `L_i` over `N*(i) ⊆ ℰ(i)`, and smooth data given by the bounds they imply along the pairs and the
Laplacian edges (`|φ_k - φ_i| ≤ Gφ |e_ik|`, `|ũ_k - ũ_i| ≤ Gu |e_ik|`, `|e_ik| ≤ h`), the weak effect of the
scalar dissipation is `|Σ_pairs (φ_k - φ_i)·d_ik| ≤ C Φmax σmax h |Ω| Gφ Gu`, `C = d (6κ2 + 18 n_E κ4)` (pairs as
ordered pairs with `½`). -/
def P4_16_3 : Prop :=
  ∀ (ι C κ : Type) [Fintype ι] [DecidableEq ι] [Fintype C] [Fintype κ] (d : ℕ) (M : WMesh ι C d)
    (vb : ι → ι → Vec d) (cb Φ : ι → ι → ℝ) (E Nst : ι → Finset ι) (p : ι → ℝ) (ut φ : ι → κ → ℝ)
    (κ2 κ4 σmax Φmax h Gφ Gu : ℝ) (nE : ℕ),
    M.Valid → 0 ≤ κ2 → 0 ≤ κ4 → 0 ≤ h → 0 ≤ Gφ → 0 ≤ Gu →
    (∀ i k, 0 ≤ cb i k ∧ |Num.dot (vb i k) (WMesh.unit (M.e i k))| + cb i k ≤ σmax) →
    (∀ i k, 0 ≤ Φ i k ∧ Φ i k ≤ Φmax) →
    (∀ i, 0 < p i) → (∀ i, 1 ≤ (E i).card ∧ (E i).card ≤ nE) → (∀ i, Nst i ⊆ E i) →
    (∀ i k, (M.n i k ≠ 0 ∨ k ∈ Nst i) → len (M.e i k) ≤ h ∧
      snorm (φ k - φ i) ≤ Gφ * len (M.e i k) ∧ snorm (ut k - ut i) ≤ Gu * len (M.e i k)) →
    let L : ι → κ → ℝ := fun i => ∑ k ∈ Nst i, (ut k - ut i)
    let lam : ι → ι → ℝ := fun i k => Φ i k * lamHat (vb i k) (cb i k) (M.e i k) (M.n i k)
    let dd : ι → ι → κ → ℝ := fun i k =>
      lam i k • (eps2C κ2 E p i k • (ut i - ut k) - eps4C κ2 κ4 E p i k • (L i - L k))
    (∀ i k, eps2C κ2 E p i k ≤ 6 * κ2 ∧ eps4C κ2 κ4 E p i k ≤ 9 * κ4) ∧
    |(1 / 2) * ∑ i, ∑ k, pairF (φ k - φ i) (dd i k)| ≤
      d * (6 * κ2 + 18 * nE * κ4) * Φmax * σmax * h * M.volΩ * Gφ * Gu

/-- `sec ϑ` of a vector `y` against the edge `e`: `|y||e| / (y·e)`. -/
def secOf {d : ℕ} (y e : Vec d) : ℝ := len y * len e / Num.dot y e

/-- P4-16.4 (`prop:consistency`(c), last sentence): with the face vector `n_ik` in place of `ν_ik`,
`λ̂(n)|e| = (|v̄·n| + c̄|n|)|e| ≥ c̄ (n·e) sec ϑ` on every pair (with `n·e > 0` and `sec ϑ ≥ 1` on the coupled pairs),
so the sum is at least `Σ c̄ (n·e) sec ϑ`; and this lower bound is not bounded independently of the aspect ratio:
for every `K` there is a valid one-triangle mesh with `|Ω| = 1` and `Σ_pairs (n·e) sec ϑ ≥ K` (`c̄ = 1`), while the
sum on `ν_ik` stays `≤ d σmax |Ω|` (P2-7.4). -/
def P4_16_4 : Prop :=
  (∀ (ι C : Type) [Fintype ι] [DecidableEq ι] [Fintype C] (d : ℕ) (M : WMesh ι C d) (vb : ι → ι → Vec d)
    (cb : ι → ι → ℝ), M.Valid → (∀ i k, 0 ≤ cb i k) →
    (∀ i k, i ≠ k → M.n i k ≠ 0 → 0 < Num.dot (M.n i k) (M.e i k) ∧ 1 ≤ secOf (M.n i k) (M.e i k)) ∧
    (∀ i k, cb i k * Num.dot (M.n i k) (M.e i k) * secOf (M.n i k) (M.e i k) ≤
      radFull (vb i k) (cb i k) (M.n i k) * len (M.e i k)) ∧
    (∑ i, ∑ k, cb i k * Num.dot (M.n i k) (M.e i k) * secOf (M.n i k) (M.e i k)) ≤
      ∑ i, ∑ k, radFull (vb i k) (cb i k) (M.n i k) * len (M.e i k)) ∧
  (∀ K : ℝ, ∃ M : WMesh (Fin 3) Unit 2, M.Valid ∧ M.volΩ = 1 ∧
    K ≤ (1 / 2) * ∑ i, ∑ k, Num.dot (M.n i k) (M.e i k) * secOf (M.n i k) (M.e i k))

end CFDLean.JST1.Spec
