# P1 proposal: Lean statements for the algebraic core of paper 1 (items 1-5)

**Status: proposal. Waiting for the user's approval. No Lean code is written yet.**

Written 2026-11-25. Step 1 of section 4 of `LEAN_AGENT_INSTRUCTIONS.md`.

## 0. Inputs, pins, layout

- Paper: `SU2_NativeIntegrated/Handbook/LEAN_HANDOFF_PAPER1/paper1.tex` (frozen). `sha256sum -c SHA256SUMS`: both files OK
  on 2026-11-25. Line numbers below refer to this file.
- Toolchain: Lean `v4.19.0`, Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` (same as CFD_Lean and SU2_Lean).
- Folder: `/media/rausa/4TB/SU2_Versions/JST_Paper_Lean` (the user chose this folder in place of `Paper1_Lean`).
- Two namespaces in one Lake package:
  - `NumCore` = generic building blocks. They know nothing about JST or paper 1: pair sums, two-point entropy
    fluxes, log mean, P1 simplex calculus, weighted simplex meshes and their P1 operators. Reason: the user wants to
    reuse them for other numerical methods. One package now; it can be split into its own package later at no cost.
  - `Paper1` = the statements of the paper. It imports `NumCore`.
- Optional dependency for item 5, d = 3 only: CFD_Lean at its accepted pin (M4/M5 revision, recorded in
  `specifications/accepted-*.json` of CFD_Lean). Only `CFDLean.Geometry.MedianDual` is used. See decision D1.
- Style: exact reals, total definitions, physical hypotheses as explicit arguments. `Fintype` sums. No floats.
- The Lean below is a sketch of the statements. At step 2 (frozen specification) I elaborate every statement in a
  scratch file outside the accepted build, so the frozen text is type-correct. No `sorry` enters the accepted build.

## 1. Symbol table

| Paper | Lean (proposed) | Notes |
|---|---|---|
| d, R^d | `d : ℕ`, `Vec d := Fin d → ℝ`, `dot` | dimension generic unless stated |
| state u = (ρ, ρv, ρE) | `State d := Channel d → ℝ`, `Channel d = mass \| momentum α \| energy` | pattern of `SU2_Lean/SU2/Spec.lean` |
| a·b on states | `pair x y := ∑ c, x c * y c` | written ⟪x, y⟫ below |
| γ > 1 | `Gas` with `γ`, `one_lt_γ` | |
| p | `pressure g U := (γ-1)(E - |m|²/(2ρ))` | |
| admissible (ρ, p > 0) | `Admissible g U := 0 < ρ ∧ 0 < p` | |
| s, U = -ρs/(γ-1) | `physEntropy g U := log(p) - γ log(ρ)`, `entropyFun g U := -ρ s/(γ-1)` | |
| w = U'(u) | `entropyVars g U := ((γ-s)/(γ-1) - ρ|v|²/(2p), ρv/p, -ρ/p)` | proved = gradient, P1-1.0 |
| ψ = ρv | `fluxPot U := mom U` | proved = w·F - Q, P1-2.0 |
| ũ = (ρ, ρv, ρH) | `enthalpyState g U := U + p • e_E` | paper proof line 259 |
| [f]_ik = f_k - f_i | `jump f i k` | |
| λ_γ, Λ_γ | `lamLow γ`, `lamHigh γ` := (γ+1 ∓ √(γ(γ-1)))/2 | |
| F(u)·y | `physFlux g U y` | Euler flux on vector y |
| F^ec, Tadmor condition | `TwoPointFlux`, `Tadmor w ψ F` | `NumCore` |
| n_ik, β_i | `n i k`, `beta i` | abstract (item 2) or from a mesh (item 5) |
| T, |T|, g_a^T, m_T | `Simplex d`, `vol`, `grad T a`, `vol/(d+1)` | `NumCore.Simplex` |
| mesh, splits with ω_s | `WMesh ι d`: cells with weights `ω ≥ 0` | ω = 1 on a simplex mesh |
| c_ik, V_i, μ_ik, e_ik | `c`, `V`, `mu`, `e` | median dual, W^T_a = m_T |
| B = c + c^T (boundary mass) | `B i k` | |
| interior vertex | `Closed M i := ∀ k, B i k = 0` | see 5.0 |
| ν_ik, G_i(y) | `nu`, `Gtensor` | |
| ∇w_h on T | `gradW T w := ∑ a, w a ⊗ g_a` | |
| K(w)G | `viscFlux g R μ κ w G` | defined from the NS fluxes |

## 2. Item 1 — `lem:eps2` (lines 247-270)

Files: `Paper1/Euler/State.lean`, `Paper1/Euler/Entropy.lean`, `Paper1/Dissipation/SecondDifference.lean`.

- **P1-1.0 (entropy variables are the gradient).** `Admissible g U → HasFDerivAt (entropyFun g) (pair-with (entropyVars g U)) U`.
  Not in the lemma, but it makes w the paper's w. (Checked with sympy for d = 2.)
- **P1-1.1 (thermodynamic pencil, pointwise).** For all real `a b`, with `Q(a,b) = γa² - 2ab + b²`,
  `Q̃(a,b) = γa² - (γ+1)ab + γb²`: `lamLow γ * Q ≤ Q̃ ≤ lamHigh γ * Q`, and each bound is an equality for some
  `(a,b) ≠ 0`. Hypothesis: `1 < γ`.
- **P1-1.2 (main bounds).** For `Admissible g Ui`, `Admissible g Uk`, with `Δw = wk - wi`, `Δu = Uk - Ui`,
  `Δũ = ũk - ũi`:
  `lamLow γ * ⟪Δw, Δu⟫ ≤ ⟪Δw, Δũ⟫ ∧ ⟪Δw, Δũ⟫ ≤ lamHigh γ * ⟪Δw, Δu⟫`.
- **P1-1.3 (convexity).** Same hypotheses: `0 ≤ ⟪Δw, Δu⟫`.
- **P1-1.4 (constants).** `1 < γ →` `3/4 < lamLow γ`, `lamLow γ < 1`, `1 < lamHigh γ`;
  `StrictAntiOn lamLow (Ioi 1)`; limits 1 at γ → 1⁺ and 3/4 at γ → ∞; `0.8258 < lamLow 1.4 < 0.8259`.
- **P1-1.5 (production of the second difference).** For any reals `lam ≥ 0`, `eps2 ≥ 0` and admissible states, the
  pair flux `d2 := lam * eps2 • (ũi - ũk)` has production
  `⟪Δw, d2⟫ = -eps2*lam*⟪Δw, Δũ⟫ ≤ -lamLow γ * eps2*lam*⟪Δw, Δu⟫ ≤ 0`.
- **P1-1.6 (sharpness of the two-state bounds).** For every `ε > 0` there are admissible `Ui, Uk` with
  `0 < ⟪Δw, Δu⟫` and `⟪Δw, Δũ⟫ < (lamLow γ + ε) ⟪Δw, Δu⟫`; the same for `lamHigh` from above. See D2.

Proof plan. Along the straight path w(s) = wi + sΔw (stays in {w_E < 0}), put f(s) = ⟪Δw, ũ(w(s))⟫ - λ⟪Δw, u(w(s))⟫.
Its derivative is q̃ - λq, with q, q̃ the forms of line 264-265 in a = ρ'/ρ, b = p'/p, v'. Then f is monotone (no
integral needed). This needs the inverse map u(w) on {w_E < 0} (exp/log, real powers).

Differences from the paper: none in the statement. The paper's Galilean reduction to v = 0 is not needed: the formulas
of lines 264-265 hold for any v (checked with sympy). "Both bounds are sharp" is proved as P1-1.6 (best constants).
Equality for a finite jump is probably never reached; equality holds only for the pointwise forms (P1-1.1).

Estimate: M (4-6 days, most of it the calculus along the path).

## 3. Item 2 — `lem:ec` (153-158, proof 881-884) and `prop:consistency`(a) (278, proof 928-930)

Files: `NumCore/PairSum.lean`, `NumCore/EntropyFlux.lean`, `NumCore/LogMean.lean`, `Paper1/Euler/IsmailRoe.lean`,
`Paper1/Central.lean`.

Generic part (`NumCore`), for a finite vertex type `ι`, a state space with a pairing, and `n : ι → ι → Vec d`:

- **P1-2.1 (antisymmetric pair sums).** If `F k i = -F i k` for all i, k:
  `∑ i, ∑ k, F i k = 0` and `-(∑ i, ⟪w i, ∑ k, F i k⟫) = (1/2) ∑ i, ∑ k, ⟪w k - w i, F i k⟫`.
- **P1-2.2 (lem:ec).** Hypotheses: `n k i = -n i k`; the two-point flux `Fec` is symmetric
  (`Fec a b y = Fec b a y`), linear in `y`, and satisfies Tadmor's condition
  `⟪w b - w a, Fec a b y⟫ = dot (ψ b - ψ a) y` for all states and all `y`. Put `beta i := -∑ k, n i k` and
  `Rc i := ∑ k, Fec (u i) (u k) (n i k)`. Then
  `-(∑ i, ⟪w (u i), Rc i⟫) = (1/2) ∑ i, ∑ k, dot (ψ (u k) - ψ (u i)) (n i k) = ∑ i, dot (ψ (u i)) (beta i)`.
  Corollary: if `beta i = 0` for every i except a set ∂, the production is `∑ i ∈ ∂, ψ_i·β_i`.
- **P1-2.3 (link to the P1 operator, any dual).** On a weighted simplex mesh (item 5) with any dual weights `W` with
  `∑ a, W T a = |T|`: `∑ k, n^W i k = -beta i` with `beta i := ∑ T ∋ i, ω_T |T| g_i^T` (the paper's
  ∫∇φ_i = ∮φ_i N, line 872). With `Closed M i` (5.0): `beta i = 0`.

Ismail–Roe (the paper's example):

- **P1-2.4.** `logMean a b := if a = b then a else (b - a)/(log b - log a)`; basic facts (symmetric, `logMean a a = a`,
  positive, `(b - a) = logMean a b * (log b - log a)`).
- **P1-2.5.** Definition `ismailRoe g Ua Ub y` (parameter vector z = √(ρ/p)(1, v, p), Ismail–Roe 2009). For admissible
  states: Tadmor's condition with `entropyVars` and `fluxPot`; symmetry; linearity in `y`;
  consistency `ismailRoe g U U y = physFlux g U y`. (Tadmor checked numerically to 1e-15 for d = 2.)
- **P1-2.0 (correspondence).** `⟪entropyVars g U, physFlux g U y⟫ - entropyFun g U * dot (vel U) y = dot (fluxPot U) y`,
  i.e. ψ = w·F - Q with Q = U v.

Consistency (a):

- **P1-2.6 (conservation).** The pair flux `F i k := Fec (u i) (u k) (n i k) + dissip i k` with
  `dissip i k := lam i k • (eps2 i k • (ũ i - ũ k) - eps4 i k • (L i - L k))`, `L i := ∑ k ∈ Nstar i, (ũ k - ũ i)`,
  and symmetric coefficients `lam, eps2, eps4` (all reals, any `Nstar`), is antisymmetric. Hence
  `∑ i, Res i = -∑ i, b i` for `Res i := -∑ k, F i k - b i`.
- **P1-2.7 (free stream).** Uniform state `u i = U`, consistency `Fec U U y = physFlux g U y`, and boundary data
  `b i = physFlux g U (beta i)`: then `Res i = 0` for every i.

Differences from the paper:
- The boundary closure (`thm:closure`) is not in this task. P1-2.7 takes its free-stream property
  (`b_i = F(u)·β_i` for a uniform state, line 1027) as a hypothesis.
- "Σ_k n_ik = 0 at interior vertices" uses `Closed M i` of 5.0 (proved from a facet pairing; see item 5).

Estimate: P1-2.1/2.2/2.6/2.7 S; P1-2.4/2.5 M (2-3 days).

## 4. Item 3 — `lem:splitmean` (590-610)

File: `Paper1/Mixed/SplitMean.lean`. All in one pair `ik` and its two end nodes; generic over the splits.

Data: finite split type `σ`, weights `ω s ≥ 0`, `∑ s, ω s = 1`; containment `χ s i k : Prop` (decidable,
symmetric); `pi i k := ∑ s, ω s * [χ s i k]`; assembled coefficients `n i k`; pair vectors `e i k`; mean state data
`vbar i k`, `cbar i k` (symmetric). Radii `lamHat y := |dot vbar (nuOf y)| + cbar * ‖nuOf y‖` with
`nuOf y := (dot y e / dot e e) • e`, and `rad y := |dot vbar y| + cbar * ‖y‖` (for Λ). Boundary part `bnd i ≥ 0`.

Closure (A), as definitions: `nS s i k := if χ s i k then (pi i k)⁻¹ • n i k else 0`; nodal quantities use their
split means.

- **P1-3.1 (Λ mean, first part of (A) only).** `∑ s, ω s * LamS s i = ∑ k, rad (n i k) + bnd i`, where
  `LamS s i := ∑ k, rad (nS s i k) + bnd i`. Needs `pi i k > 0` where some χ holds.
- **P1-3.2 (exact means, no (A)).** `∑ s, ω s • LS s i = ∑ k ∈ Nstar i, pi i k • (ũ k - ũ i)`; the same for the
  sensor numerator and denominator sums and for the counts `∑ s, ω s * #{k | χ s i k} = ∑ k, pi i k`.
- **P1-3.3 (main).** With `PsiS s i := (Lam i / (4 * lamHat (nS s i k)))^a` (real power, any real `a`),
  `PhiS := 4 PsiS_i PsiS_k / (PsiS_i + PsiS_k)`, `lamS := PhiS * lamHat (nS s i k)`, and any split-independent bracket
  `D` (the second- and fourth-difference part with mean nodal data):
  `∑ s, ω s • (if χ s i k then lamS s • D else 0) = (pi i k)^a * Phi i k * lamHat (n i k) • D`,
  with `Phi`, `Psi` on the assembled `n` and the mean `Lam`. Hypotheses: `0 < pi i k`, `0 < lamHat (n i k)`,
  `0 < Lam i`, `0 < Lam k`.
- **P1-3.4 (simplex mesh).** If `pi i k = 1`, the coefficient is `Phi * lamHat`, i.e. eq. (jst).

Differences from the paper (to confirm in the proof; candidates for `PAPER_GAPS.md`):
- (A) says "every nodal quantity is replaced by its mean". For the sensor ς (a ratio) the lemma uses the ratio of the
  mean sums, not the mean of the ratio. I state (A) as "the sums inside the nodal quantities are replaced by their
  means".
- The boundary-face part of Λ_i under a split is not defined in the paper. I assume it is split-independent (`bnd i`).
- The lemma needs `π_ik > 0`, `λ̂_ik > 0` (true if c̄ > 0 and n·e > 0) and `Λ_i > 0`; the paper does not write them.

Estimate: S-M (1-2 days).

## 5. Item 4 — `thm:visc` (319-324, proof 1034-1044)

Files: `NumCore/P1Gradient.lean`, `Paper1/Viscous/Flux.lean`, `Paper1/Viscous/Galerkin.lean`.

- **P1-4.1 (identity, generic).** On a weighted mesh, for nodal vectors `w i : Fin m → ℝ`, `G T := gradW T w`, and any
  element fluxes `Fl T : Matrix (Fin m) (Fin d) ℝ`, with `Rv i := -∑ T ∋ i, ω_T |T| • (Fl T *ᵥ g_i^T)`:
  `∑ i, ⟪w i, Rv i⟫ = -∑ T, ω_T |T| * (G T : Fl T)` (Frobenius product). No hypothesis on `Fl`.
- **Definition `viscFlux g R μ κ wbar G`.** With `θ := -wbar_E`, `v := wbar_m / θ`, `Gθ := -G_E`,
  `Dv := (G_m - v ⊗ Gθ)/θ`, `DT := -Gθ/(R θ²)`, `τ := μ(Dv + Dvᵀ - (2/3)(tr Dv) I)`:
  `viscFlux := (0, τ, τ v + κ DT)`. It is linear in `G`.
- **P1-4.0 (correspondence).** If `G` is the derivative of `w` along any variation `(δρ, δv, δT)` of a state with
  `ρ, T > 0` (with `p = ρRT`), then `viscFlux w G` is the NS viscous and heat flux
  `(0, τ(δv), τ(δv) v + κ δT)`. This shows `viscFlux = K(w)∇w` as in the paper.
- **P1-4.2 (K is PSD).** Hypotheses: `d ≤ 3`, `0 ≤ μ`, `0 ≤ κ`, `0 < R`, `wbar_E < 0`. For every `G`:
  `G : viscFlux wbar G = θ (τ : Dv) + κ θ² R |DT|² ≥ 0`, with `τ : Dv = 2μ(S:S - (1/3)(tr S)²)`.
- **P1-4.3 (thm:visc).** Hypotheses: `d ≤ 3`, `μ, κ ≥ 0`, `R > 0`, `ω_T ≥ 0`, every vertex value has `w_E,i < 0`.
  With `wbar T := mean of the vertex values of T` and `Fl T := viscFlux (wbar T) (G T)`:
  `∑ i, ⟪w i, Rv i⟫ = -∑ T, ω_T |T| (G T : K(wbar T) G T) ≤ 0`. Plus: `Admissible g U → (entropyVars g U)_E < 0`,
  and the vertex mean keeps `w_E < 0`.
- **P1-4.4 (symmetry, optional).** `G : viscFlux w H = H : viscFlux w G` (the paper's K_αβ = K_βα^T).

Differences from the paper: the paper writes "K(w)∇w" without a formula; P1-4.0 makes it exact. `d ≤ 3` is an explicit
hypothesis (the paper states d = 2, 3; the proof needs (tr S)² ≤ 3 S:S). The theorem holds for any `ω_T ≥ 0`, so it
also covers split means on mixed meshes.

Estimate: P1-4.1 S; P1-4.0/4.2/4.3 M (2-3 days).

## 6. Item 5 — `prop:fv` (325-330, proof 1046-1054) and `lem:dissgeom`(a)-(c) (189-204, proof 898-918)

Files: `NumCore/Simplex.lean`, `NumCore/WMesh.lean`, `NumCore/MedianDual.lean`, `Paper1/Geometry/DissGeom.lean`,
`Paper1/Geometry/FiniteVolume.lean`, optional `Paper1/Geometry/CFDBridge.lean`.

Generic simplex calculus (`NumCore`, any d):

- `Simplex d`: vertices `x : Fin (d+1) → Vec d`, nondegenerate edge matrix. `grad T a` from the inverse edge matrix;
  `vol T := |det|/d!`.
- **P1-5.1.** `∑ a, grad T a = 0`; `dot (grad T a) (x b - x c) = δ_ab - δ_ac`; `∑ a, grad T a ⊗ x a = 1`;
  `0 < vol T`; facet area vector `facet T o := -(d * vol T) • grad T o` with `∑ o, facet T o = 0`.

Weighted mesh `WMesh ι d`: positions `pos : ι → Vec d`; finite cells, each `Fin (d+1) ↪ ι`, nondegenerate, weight
`ω ≥ 0` (ω = 1: simplex mesh; ω = ω_s on split sub-simplices: mixed mesh). Median dual (W = m_T):
`c i k := ∑ T ∋ i,k, ω m_T g_k`, `n i k := c i k - c k i`, `V i := ∑ T ∋ i, ω m_T`, `mu i k := ∑ T ∋ i,k, ω m_T`,
`e i k := pos k - pos i`, `B i k := c i k + c k i`, `vol Ω := ∑ T, ω |T|`.

- **5.0 (interior vertex).** `Closed M i := ∀ k, B i k = 0` (B is the boundary mass matrix, so this is the paper's
  algebraic meaning of "interior", line 906). Then `beta i = ∑ k, B i k = 0`.
  **P1-5.0a.** A facet pairing at `i` (every facet of a cell at `i` is matched with a facet of another cell with the
  same vertex set, the same weight and the opposite area vector) implies `Closed M i`.
  **P1-5.0b (d = 3, with D1 = A).** For CFD_Lean's `MeshData` with `Conforming`, a vertex on no boundary face has a
  facet pairing, hence `Closed`.
- **P1-5.2 (a).** `i ≠ k → dot (n i k) (e i k) = 2 * mu i k`; `mu i k > 0` if a cell with `ω > 0` contains `i, k`.
  Hence `nu i k = (dot (n i k) (e i k) / |e|²) • e i k` is a positive multiple of `e i k` and
  `‖nu i k‖ = dot (n i k) (e i k) / ‖e i k‖`.
- **P1-5.3 (b).** Every vertex: `∑ k, c i k ⊗ e i k = V i • 1`. `Closed M i → ∑ k, n i k ⊗ e i k = (2 * V i) • 1`.
  Global, no hypothesis: `∑ i, ∑ k, n i k ⊗ e i k = (2 * vol Ω) • 1` (each pair twice) and `∑ i, V i = vol Ω`.
- **P1-5.4 (c).** `Closed M i → trace (Gtensor i nu) = ∑ k, ‖nu i k‖ ‖e i k‖ = 2 d V i`; global
  `∑ i, ∑ k, ‖nu‖‖e‖ = 2 d vol Ω` (= d|Ω| per unordered pair); `Closed M i → 2 d V i ≤ trace (Gtensor i n)`, with
  equality iff `n i k` is a non-negative multiple of `e i k` for every k. Cartesian model: a vertex with the 2d
  neighbours `±h_α ê_α` and `n = ±(V/h_α) ê_α` has `Gtensor i nu = Gtensor i n = (2V) • 1`.
- **P1-5.5 (prop:fv, generic).** If the dual facet area vectors inside `T` satisfy `S T i k = m_T (g_k - g_i)`, the FV
  residual `∑ T ∋ i, ∑ k ∈ T, ω • (Fl T *ᵥ S T i k)` equals `Rv i` of P1-4.1, for any constant element flux `Fl T`.
- **P1-5.6 (prop:fv, geometric).** The real median-dual facets satisfy the hypothesis of P1-5.5:
  d = 3: `CFDLean.MedianDual.localInterface p i k = m_T (g_k - g_i)` for positively oriented tetrahedra (from
  CFD_Lean's `localInterface_eq`); d = 2: own dual segment (edge midpoint to centroid, rotated), same identity.

Differences from the paper:
- "Interior vertex" is `Closed M i`, proved from a facet pairing (P1-5.0a), and for d = 3 from CFD_Lean's conforming
  predicate (P1-5.0b). For general d, the step "conforming mesh ⇒ facet pairing" is not in this task.
- prop:fv is proved geometrically for d = 2 and d = 3 only. For general d, P1-5.5 is the algebraic core.
- "Σ over coupled pairs" is a sum over all k: uncoupled pairs and k = i give zero (`n = 0`, `e = 0`).
- (a)-(c) on mixed meshes: (a) and the global (b), (c) need nothing more. The vertex statements need `Closed M i`,
  which on mixed meshes comes from face balance (`lem:avg`, not in this task).

Estimate: M overall (6-9 days); P1-5.1 3-4 days, P1-5.0a 2 days, P1-5.0b and P1-5.6 2-3 days.

## 7. Process after approval

1. Approval record `specifications/P1-approval.md`; frozen `specifications/P1.md` with the elaborated statements;
   `specifications/P1-results.json` (ID → Lean declaration).
2. Proofs. `KernelAudit.lean` prints the axioms of every bound declaration (only `propext`, `Classical.choice`,
   `Quot.sound`); a check script for 0 `sorry`/`admit`/new `axiom`.
3. Independent review by a fresh agent with the frozen spec and the code only.
4. Report, `PAPER_GAPS.md`, one sentence for the paper.
- Builds at `nice 19`, `-j 2`, `LEAN_NUM_THREADS=2`. Mathlib by `lake exe cache get`. To save ~5 GB I will try to
  share the Mathlib build of CFD_Lean (same revision). Disk use is reported.
- Total estimate: 3-4 weeks of proof work.

## 8. Decisions for the user

- **D1 (item 5 geometry).** A: generic d algebra + real median-dual geometry for d = 3 via CFD_Lean (pinned) and for
  d = 2 by own code. B: generic d algebra only; prop:fv takes the facet identity as a hypothesis. A is recommended:
  it makes prop:fv and "interior vertex" real theorems for the two dimensions of the paper. Cost of A: +3-4 days and
  one dependency.
- **D2 (sharpness in item 1).** A: prove P1-1.6 (best constants for two states, +2 days). B: prove only the pointwise
  equality (P1-1.1) and write in the report that the two-state sharpness is not checked. A is recommended, because the
  paper says "both bounds are sharp".

## 9. Paper notes found so far (to confirm during the proofs)

- `lem:eps2`: the Galilean step is not needed (the forms hold for any v). Sharpness is a best-constant statement; the
  proof shows equality only for the pointwise forms. Possible wording fix.
- `lem:splitmean`: closure (A) for the sensor ratio, the split of the boundary part of Λ_i, and the positivity
  hypotheses (see section 4).
