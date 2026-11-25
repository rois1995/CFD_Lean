# P2 proposal: Lean statements for the larger results of paper 1

**Status: proposal. Waiting for the user's approval. No Lean code is written yet.**

Written 2026-11-25. Same process as P1 (section 4 of `LEAN_AGENT_INSTRUCTIONS.md`): proposal, approval, frozen
specification, proofs, independent review, report. P1 stays frozen; P2 only adds files.

## 0. Input, pins

- Paper: `SU2_NativeIntegrated/Handbook/paper1/paper1.tex`, the version with G1-G4 fixed,
  sha256 `32e1f2602ae6d55876ed22cd35ebe46b1752402bf272a0bd2ab44a66d9e779db` (2026-11-25 13:54). The user said the
  fixes are done; this file is the new input. Line numbers below refer to it. (The `paper1.pdf` next to it is older
  than the fix; I use the `.tex` only.) Diff to the P1 input: only the G1-G4 text (lines 234, 254-255, 271-274,
  593-598, 609-610, 614-615). No P1 statement changes.
- Toolchain, Mathlib, CFD_Lean pins: unchanged from P1.
- New files: `Paper1/Spec/Item6..10.lean`, proofs in `Paper1/Proofs/`, new generic blocks in `NumCore`.

## 1. Scope (decision D1)

Results of the paper not yet in Lean, with my size guess (S < 1 day, M days, L weeks):

| # | Paper (line) | What | Size |
|---|---|---|---|
| 6 | `prop:sbp` (143), `lem:bdefect` (300), `prop:consistency`(b) (284) | SBP form c + cᵀ = B_c + 2s; boundary from boundary facets; standard closure defect Π | M |
| 7 | `lem:dissgeom`(d) (205), `prop:consistency`(c) first part (288) | dissipation tensor K_i, sec-factor, Loewner minimum, trace | S-M |
| 8 | `thm:closure` (309) | hybridized closure: exact entropy identity, slip wall, far field, conservation, free stream, linear limit | M |
| 9 | `thm:wall` (336) | weak no-slip wall: Π^w_T ≤ D^gal_T / c, and c ≥ 1 is sharp | M |
| 10 | `lem:sstentropy` (395), `prop:sstpde` (411, pointwise), `lem:matched` (470), `thm:sst` (482), `rem:sstconsistent` (513) | SST coupled entropy | M |
| 11 | `lem:avg` (683), `prop:splits` (691) | mixed meshes: face balance, pulling splits, slivers, Kuhn angles | L |
| 12 | `prop:defect` (162) | other duals: E^T ≠ 0, exact pair production, Euler sign is indefinite | M-L |
| 13 | `thm:complete` (530) | the full entropy balance, assembled from 6-12 | M |

Not proposed: `prop:wallJST` (a model analysis and a scaling, not a theorem; only its part (iii) and the spectrum
are algebra, and can come later).

**D1.** A = P2 is items 6-10 now; items 11-13 become P3 after P2 is accepted. B = items 6-13 in one go.
**Recommended: A.** 6-10 all live on one simplex mesh and reuse P1. 11 is combinatorics of cells and splits, a
different kind of work. 13 needs all others.

## 2. New generic blocks (`NumCore`)

- `BoundaryFacets`: on a `WMesh` with ω = 1, a facet pairing of all interior facets (an involution on the
  facets `(T, o)` with the same vertex set and opposite facet vectors). The unpaired facets are the boundary facets
  `f`, with area vector `A_f N_f`. This is the global form of P1-5.0a. It closes review point M1: β and B_c become
  sums over boundary facets, proved, not assumed.
- `faceQuad`: a rule on a boundary facet, points given by their barycentric weights `φ_qk ≥ 0`, `∑_k φ_qk = 1`, weights
  `a_q > 0`, with (H1) `∑_q a_q φ_qi = A_f/d` and (H2) `∑_q a_q φ_qi φ_qk = A_f(1+δ_ik)/(d(d+1))`.
- `SIPForm`: a symmetric positive semidefinite bilinear form `K` on gradients, a projector `P`, the Cauchy-Schwarz
  and Young steps in the K-seminorm.

## 3. Statement sketches

### Item 6 — `prop:sbp`, `lem:bdefect`, `prop:consistency`(b)

- **P2-6.1** For a weighted dual `W` (`∑_a W T a = vol T`): `c^W + (c^W)ᵀ = B_c + 2 s` with `s` symmetric, zero row
  and column sums, off-diagonal entries `E_ik` of eq. (nE). (`B_c` here = the median-dual `c + cᵀ`.)
- **P2-6.2** On one simplex, the element part of `s` is zero iff `W T = m T` (needs `Nondeg`: `g_a ≠ 0`).
- **P2-6.3** With `BoundaryFacets`: `β_i = ∑_{f ∋ i} A_f N_f / d` and
  `B_c i k = ∑_{f ∋ i,k} A_f N_f (1 + δ_ik) / (d(d+1))`. Hence `Closed i` for every vertex on no boundary facet.
- **P2-6.4** (eq. pf-B2) for any symmetric `B` with row sums `β`: the edge form plus `½(B F + diag β F)` equals `c F`.
- **P2-6.5** (`lem:bdefect`) Standard closure `b_i = ∑_f ∑_{j ∈ f} A_f ω_ij F*_j`: then
  `∑_i [ψ_i·β_i − w_i·b_i] = ∑_f (A_f/d) ∑_{i∈f} [ψ_i·N_f − w_i·F*_i] + ∑_f A_f/(2d(d+1)) ∑_{i<j ∈ f} [w]·[F*]`, and the
  weights of `½(B_c + diag β)` are `(d+3) : 1`.
- **P2-6.6** (slip wall, both signs) with the Euler pressure flux the lumped term is zero, and there are admissible
  states with `Π > 0` and with `Π < 0`.
- **P2-6.7** (`prop:consistency`(b)) at a closed vertex `∑_k ½(F_i + F_k)·n_ik = ∑_{T∋i} m_T ∑_k g_k^T · F_k`. The
  `O(|u_k − u_i|²)` part is not proposed (it is a Taylor estimate, not used by any other result).

### Item 7 — `lem:dissgeom`(d), `prop:consistency`(c)

- **P2-7.1** For λ_ik ≥ 0 and any quadratic `q(x) = q0 + g·x + ½ xᵀHx`:
  `½ ∑_k λ_ik (q_k − q_i) = (first-order part) + V_i K_i : H` with `K_i = (1/(4V_i)) ∑_k λ_ik e_ik ⊗ e_ik`. (D2.)
- **P2-7.2** With `λ = σ |y|` and a fixed edge projection: each term of `K_i` is the edge-projection term times
  `sec ϑ ≥ 1`; `K_i(y) ⪰ K_i(ν)` in the Loewner order (`Matrix.PosSemidef` of the difference), with equality iff every
  `y_ik ∥ e_ik` (on pairs with σ > 0).
- **P2-7.3** If `σ_ik |e_ik| = s` on all pairs at i: `K_i = s G_i(y)/(4V_i)`; at a closed vertex `tr K_i(ν) = d s / 2`;
  and in general `tr K_i(ν) ≤ (d/2) σ_max h_i`.
- **P2-7.4** `∑_pairs λ̂_ik |e_ik| ≤ d σ_max |Ω|` with λ̂ on ν (uses P1-5.4b).

### Item 8 — `thm:closure`

Inputs: Tadmor flux `F^ec` (P1 `NumCore`), states at the vertices, a `faceQuad` per boundary facet, projected
entropy variables `w̃_q = ∑_k φ_qk w_k`, a state `ũ_q` with `w(ũ_q) = w̃_q`, boundary fluxes `F*_q`.

- **P2-8.0** (entropy projection, Euler) every `w` with `w_E < 0` has exactly one admissible `u` with `w(u) = w`.
- **P2-8.1** exact identity `∑_i [ψ_i·β_i − w_i·b_i] = ∑_q [ψ̃_q·N_q − w̃_q·F*_q]`.
- **P2-8.2** slip wall: with `F*_q = (0, p̃_q N_q, 0)` every point term is zero, for any admissible states.
- **P2-8.3** far field: if `(w_g − w̃_q)·F*_q ≤ (ψ_g − ψ̃_q)·N_q`, the point term is at most `ψ_g·N_q − w_g·F*_q`; and
  `F^ec(ũ_q, u_g; N_q) − ½λ(u_g − ũ_q)`, `λ ≥ 0`, meets that hypothesis.
- **P2-8.4** conservation `∑_i b_i = ∑_q F*_q`; free stream; and for linear fluxes `b = ½(diag β + B_c) F`.

### Item 9 — `thm:wall` (appendix lines 1067-1090)

On one simplex, with `K̄ = K(w̄_T)` ⪰ 0 (P1-4.3), a constant orthogonal projector `P`, wall faces with `h_f = d|T|/A_f`,
`σ_f = c N_T d / h_f`, the terms `Π^w_T` and `D^gal_T` as in the appendix:

- **P2-9.1** `A_f G:K̄G = (d/h_f) D^gal_T` (exact).
- **P2-9.2** `c > 0 → Π^w_T ≤ D^gal_T / c`; hence `c ≥ 1 → D^gal_T − Π^w_T ≥ (1 − 1/c) D^gal_T ≥ 0`.
- **P2-9.3** (sharp) `N_T = 1`, `c < 1`, `μ > 0`: there are vertex values with `D^gal_T − Π^w_T < 0`.
- **P2-9.4** the wall flux term is zero for the adiabatic wall (the isothermal value is a definition).

### Item 10 — SST (`lem:sstentropy`, `prop:sstpde`, `lem:matched`, `thm:sst`, `rem:sstconsistent`)

- **P2-10.1** `η0 = η ∘ T` with the linear map `T U = (ρ, ρv, ρE − ρk)`; `ker T = span{e_E + e_k, e_ω}`.
- **P2-10.2** entropy variables `v^η = Tᵀ w(û)` (as `HasFDerivAt`, reuses P1-1.0); the exact semi-discrete identity
  `v^η·(R, R_k, R_ω) = w·(R_ρ, R_m, R_E − R_k)`.
- **P2-10.3** Hessian of `η0` is `Tᵀ ∇²η T`: positive semidefinite with null space `ker T` (needs the Hessian of η
  positive definite on admissible states; proved from P1-1.1 style algebra).
- **P2-10.4** (`prop:sstpde`, pointwise) for values and gradients at one point: the algebraic formula of `Π`, and
  `Π ≤ 0` when `r_D = 0`, `P_k ≤ μ_t Q`, `μ, κ, ε ≥ 0`; `Q ≥ 0` for `d ≤ 3`. (The PDE itself is not formalized.)
- **P2-10.5** (`lem:matched`) the matched pair and boundary terms give (M1), (M2), conservation of ρE and ρk,
  uniform k stays uniform, and (M5) at walls with `k_D = 0`.
- **P2-10.6** (`rem:sstconsistent`) `P_k = max(0, min(P*, c_l ε))` and `ε ≥ 0` give (M4).
- **P2-10.7** (`thm:sst`) given (M1)-(M6), (W_t), and the productions of the hat scheme as terms with the signs of
  items 2, 4, 8, 9: the bound of the theorem, and every term except `B̂` and `Π̂^(4)` is ≤ 0. Here the hat scheme
  enters as named terms with their proved properties, not as one big definition (the full definition is item 13).

## 4. Decision D2 — `lem:dissgeom`(d), "for smooth q its second-order part"

- A = state it for quadratic `q`, exactly (P2-7.1). The operator is linear, so this is the second-order part of
  the Taylor polynomial of any smooth `q`. S.
- B = state it for `C³` functions with a remainder `O(|e|³)` (Mathlib Taylor). M, and adds no new fact about `K_i`.

**Recommended: A.**

## 5. Risks

- Item 9: the theorem text is short; the appendix defines the terms. If the appendix and the theorem disagree, I
  write it in `PAPER_GAPS.md` and follow the appendix.
- Item 10: P2-10.7 is an assembly of named terms. A reviewer may ask for the full scheme; that is item 13 (P3).
- Item 6: P2-6.3 needs ω = 1 (simplex mesh). Mixed meshes are item 11.
