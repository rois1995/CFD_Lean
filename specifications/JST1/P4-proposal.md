# P4 proposal: the remaining items of paper 1

Written 2026-11-26. Same process as P1-P3. Paper input unchanged: `Handbook/paper1/paper1.tex`, sha256
`32e1f260…`. P1-P3 stay frozen; P4 only adds files. The user authorized the whole cycle (proposal, independent
statement review, self-freeze, proofs, audit, commit) without stopping for approvals.

## 1. Items

| # | Paper (line) | What | Size |
|---|---|---|---|
| 15 | `prop:wallJST` (347), proof 1092-1113 | scalar dissipation at weak walls: wall-normal model, wall slip, cut edges, removed production, spectrum | M |
| 16 | `prop:consistency`(b),(c) (282), proof 938-955 | P1 interpolant and divergence; `F^ec` - mean = O(\|Δu\|²); weak-effect bound; face-vector lower bound | M |
| 17 | `prop:sstpde` (411), proof 1123-1133 | the continuous balance ∂_t η0 + ∇·(v η0 + G) = Π for smooth solutions | M-L |
| 18 | `lem:sstentropy` (395), proof 1115-1121 | Hessian form: ∇²η ≻ 0 (Euler); ∇²η0 ⪰ 0 with null space span{e_E + e_k, e_ω} | M |

## 2. Statement sketches

### Item 15 — `prop:wallJST`

- **P4-15.1 (a), expansion.** Wall-normal model with nodes `0, h, (1+r)h` and a C³ profile `f` (one component of
  ũ): `L_k(h) = (f(0) - f(h)) + (f((1+r)h) - f(h)) = (r-1)h f'(h) + ½(1+r²)h² f''(h) + O(h³)` as `h → 0`;
  `L_k/h → (r-1) f'(0)` (first order, so not a third difference, if `r ≠ 1`), and `L_k/h² → f''(0)` if `r = 1`.
  `L_s` has boundary-only neighbours at `y = 0`: its normal part is 0 in the model.
- **P4-15.2 (a), wall slip (trivial algebra).** The one-node balance `ε4λ(L⁰ + u_s) + σu_s = 0` has the unique
  solution `u_s = -ϱL⁰/(1+ϱ)`, `ϱ = ε4λ/σ`; it is `< 0` for `L⁰ > 0`, `ε4λ > 0`; for the linear profile `u = ay`,
  `a > 0`, `r > 1`: `L⁰ = u_2 - 2u_k > 0`.
- **P4-15.3 (b) (trivial).** The momentum rows of the second-difference flux of the scheme are `λε2(ρv_s - ρv_k)`.
  The scaling `ε2ρch/μ` is not stated (the paper: "a scaling, not an estimate").
- **P4-15.4 (i), (ii).** For the complete scheme `S` and its copy `S'` with `ε2 = ε4 = 0` exactly on the edges with
  one end on the wall: both terms vanish on those edges; central flux, closure, viscous and wall terms and the
  dissipation of the other edges are unchanged; the residual changes exactly by the removed dissipation; the removed
  second-difference terms produce `≤ 0` pair by pair; `Π^(2)` of `S` = `Π^(2)` of `S'` + the removed productions; and
  `SchemeHyp S → SchemeHyp S'`, so P3-14.1-14.3 hold for `S'` unchanged.
- **P4-15.5 (iii).** Linear profile on the geometric nodes: `L_k - L_s = (r-1)(ũ_k - ũ_s)` exactly, and the removed
  fourth-difference flux produces `Π = ε4(r-1)λ [w]·[ũ] ≥ 0` (admissible states, `r ≥ 1`, `λ, ε4 ≥ 0`).
- **P4-15.6 (spectrum).** Linear constant-coefficient model: a symmetric graph with wall nodes, `L` with
  `N*(i)` = all neighbours at interior nodes and the wall neighbours at wall nodes, `R_i = Σ (L_k - L_i)` over the
  edges that are not cut. Every complex eigenvalue of `R` is real and `≥ 0`.

### Item 16 — `prop:consistency`(b), (c)

- **P4-16.1 (b).** On a nondegenerate simplex the P1 interpolant `F_h = Σ_b φ_b F_b` (barycentric `φ_b`) takes the
  nodal values, has the constant partial derivatives `∂_β F_h = Σ_b g_bβ F_b` (so `∇·F_h = Σ_b F_b g_b`), and equals
  an affine flux whose nodal values it takes (exact for linear `F`). On a valid mesh, at a closed vertex, the mean
  flux is `Σ_T ω_T m_T ∇·F_h|_T`.
- **P4-16.2 (b).** Any symmetric, consistent two-point flux that is C² near the diagonal differs from the mean by
  `O(|u_k - u_i|²)` (big-O at `(u0, u0)`, locally uniform).
- **P4-16.3 (c).** `ε2 ≤ 6κ2`, `ε4 ≤ 9κ4` (sensor ≤ 1, counts ≥ 1), and the weak effect
  `|Σ_pairs (φ_k - φ_i)·d_ik| ≤ d(6κ2 + 18 n_E κ4) Φmax σmax h |Ω| Gφ Gu` with the discrete smooth-data bounds
  `|φ_k - φ_i| ≤ Gφ|e_ik|`, `|ũ_k - ũ_i| ≤ Gu|e_ik|` on pairs and Laplacian neighbours.
- **P4-16.4 (c).** With the face vector: `λ̂(n)|e| ≥ c̄ (n·e) sec ϑ` pair by pair, and this lower bound is not bounded
  at fixed `|Ω|`: for every `K` there is a valid one-triangle mesh with `|Ω| = 1` and `Σ (n·e) sec ϑ ≥ K`.

### Item 17 — `prop:sstpde`

- **P4-17.1.** At a point `(t, x)` where `U` is admissible and differentiable (in `t` and along the coordinate
  lines), with the SST convective flux, the viscous fluxes of all rows (no mass flux; at `x` the SST fluxes built from
  the gradients of `v, T, k` there) and the source `P_k - ε` in the `k` row, if the PDE holds at `(t, x)`, then
  `∂_t η0 + Σ_β ∂_β(v_β η0 + G_β) = -θ[μQ + (μ_tQ - P_k) + ε] - κ|∇T|²/(RT²) + r_D` with `G = -v^η·F^v`; and
  `G = θκ∇T` (minus `θD_k∇k` without the turbulent diffusion in the energy flux).

### Item 18 — `lem:sstentropy` (Hessian form)

- **P4-18.1.** Euler: `η` has a second derivative `H` at admissible states and `H δ δ > 0` for `δ ≠ 0`.
- **P4-18.2.** SST: `η0` has a second derivative `H` at admissible states, `H δ δ ≥ 0`, and `H δ = 0` iff
  `H δ δ = 0` iff `δ ∈ span{e_E + e_k, e_ω}`.

## 3. Decisions (self-decided under the user's instruction; reason given)

- **D1 — `∫_Ω φ_i ∇·F_h` (16.1).** Mathlib has no Lebesgue integral of a barycentric function over a simplex
  (`Affine.Simplex.volume` is a height formula, not a measure). Choice: state the interpolant, its divergence and
  the identity with `Σ_T ω_T m_T ∇·F_h|_T`; the quadrature fact `∫_T φ_i = |T|/(d+1) = m_T` stays outside Lean.
  Reason: it is a textbook fact, the rest is exact algebra.
- **D2 — smoothness (15.1, 16.2, 16.3).** 15.1: `f` C³ on ℝ (a C³ profile on `[0, a)` extends; O(h³) needs C³).
  16.2: C² on `Ω × Ω`, `Ω` open (weakest standard "smooth" with an O(|Δu|²) conclusion). 16.3: "smooth data" is
  replaced by the discrete bounds it implies along the edges (mean value theorem), which is weaker as a hypothesis.
- **D3 — `H̄` in (iii) (15.5).** The production is stated as `ε4(r-1)λ[w]·[ũ]`; `[ũ] = H̄[w]` with
  `H̄ = ∫∂ũ/∂w ds` is the fundamental theorem of calculus of P3-13.1 (`Φ = ũ ∘ u(w)`) and is not restated.
- **D4 — the PDE (17.1).** Pointwise: derivatives at one point `(t, x)` along `t` and the coordinate lines
  (`HasDerivAt`), the PDE as a hypothesis at that point. The fluxes and the gradients of `v, T, k` are tied to `U` by
  `HasDerivAt` hypotheses (they determine them uniquely). The `ω` viscous flux and source are free (weight 0).
- **D5 — Hessian (18).** `H` is the Fréchet derivative of `fderiv η0` (existence stated); "null space" stated both as
  `{δ : H δ = 0}` and as `{δ : H δ δ = 0}`.
- **D6 — the spectrum (15.6).** The model of the proof: nodes are wall or interior (no other boundary nodes), unit
  coefficients, `ε2 = 0`; operator over ℂ; claim on every eigenpair.

Not stated: the scaling of (b) of `prop:wallJST` (the paper calls it a scaling); `∫_T φ_i = m_T` (D1).
