# Independent review of P2 (paper 1, items 6-10): the statements

- Reviewed: commit `2f7bade` (detached HEAD). The 10 frozen files pass `sha256sum -c specifications/P2-frozen.sha256`.
- Paper: `SU2_NativeIntegrated/Handbook/paper1/paper1.tex` (read only).
- Scope: the 32 statements in `Paper1/Spec/Item6..10.lean` and their definitions. The proofs were not re-checked
  (the kernel check passes, 68 of 68).
- Files of this review: `reviews/P2/Review.md` (this file) and `reviews/P2/NonVacuity.lean`. The second file compiles
  with `lake env lean reviews/P2/NonVacuity.lean`: no errors, no warnings, no `sorry`. Nothing outside `reviews/P2/` was
  edited.

## Verdict: **Accept with conditions**

I found no wrong sign, constant or definition. The wall terms, the SST Π, the hybridized closure and the standard
closure weights match the paper. No statement is vacuous. The conditions: one claim of the paper is proved only in a
weaker, frozen-K form (S1). Some statements are true for trivial reasons, or carry the content of the paper in their
hypotheses. The project must say so where it reports the results (S2, S3), and list the parts of the paper that are not
stated (S4). None of these needs a change to a frozen statement. Each can be met by adding a statement or a line in
`P2.md`.

## Findings

### Blocking

None.

### Should-fix

**S1. P2-9.2 (`thm:wall`, lines 341-342, proof 1086-1090): the sharpness is shown only for a frozen `K` that does not
depend on the nodal values.**
The paper builds an admissible counterexample (`w_o = w_f - t h_f e`, "admissible: e has no energy part if adiabatic").
There `K̄ = K(w̄_T)` is evaluated at the mean of the same nodal values. The Lean statement fixes `K` first and only says
some `w` exists. It does not require `w_a .energy < 0`, and `K` is not tied to `w`. The proof's witness is
`w_a = gw + e + [a = o] s e`. For the Navier-Stokes case of P2-9.3 (`gw = 0`, `e` momentum only) this witness has
`w_E = 0` at every node, so it is not admissible, and its mean is not the `w̄` used in `K`. So P2-9.2 and P2-9.3 together
do not give the paper's claim "c ≥ 1 is sharp for a single wall element".
The claim is still true: with `e` momentum only, `D^gal` and `Π^w` use only the momentum rows of `K(w̄)`, and these
depend on `w̄` only through `θ̄ = -w̄_E`. So adding `-θ e_E` to every node makes the witness admissible and keeps the
numbers.
Fix: add a statement (for example P2-9.2b) for the Navier-Stokes case: for `1 ≤ d ≤ 3`, `μ > 0`, `κ ≥ 0`, `R > 0`,
`T.Nondeg`, `0 < c < 1`, there is `w : Fin (d+1) → State d` with `∀ a, w a .energy < 0` and
`Dgal T (viscFlux Pv w̄) w - PiW T (viscFlux Pv w̄) (momProj d) 0 {o} c w < 0`, where `w̄ = (1/(d+1)) Σ_a w a`.

**S2. P2-10.8, second part (`thm:sst`, lines 496-497): trivial, and not linked to the real objects.**
"(W_t) holds without wall faces, and on wall elements with `D_t ≤ (1-1/c) D^gal`" is stated over four free reals. Both
implications are one `linarith` (`NonVacuity.lean`, section 5, proves them without the project's proofs). The facts
that make the paper's sentence true are `Π^w_T = 0` without walls, `D_t ≤ D^gal` (P2-10.7) and `Π^w_T ≤ D^gal_T / c`
(P2-9.1). The Lean statement uses none of them.
Fix: add a statement with the real objects. Take `Dgal := Wall.Dgal T (viscFlux ⟨R, μ+μt, κ⟩ wb) w`,
`Dt := T.vol * frob G (viscFlux ⟨R, μt, 0⟩ wb G)` with `G = gradT T w`, and `PiW := Wall.PiW … walls c w`. Prove
(W_t) for `walls = ∅`, and for `0 < c`, `Dt ≤ (1-1/c) Dgal`. If not, mark P2-10.8(ii) as "trivial" in `P2.md`.

**S3. P2-10.8, first part (`thm:sst`, lines 482-499, proof 1140-1153): bookkeeping. Report it as such.**
The statement is linear arithmetic plus one split of a sum. The content of the theorem is in its hypotheses: the
balance of the hat scheme (an inequality, assumed), `Σ D_t = Σ 2β V P*` (assumed), (W_t) (assumed), and
(M1)-(M3) in the form `X = C_k + B_k + D^h_k` (assumed). P2-10.5 does not state (M1) or (M2). `rate` is an expression.
It is not tied to `d/dt Σ V η0` of P2-10.2: the step `hatState R = R̂ + (X - R_k) e_E` is done by hand in the
statement. `P2.md` says only that "the hat scheme enters through its balance as a hypothesis".
Fix: in `P2.md` (differences list and table) say that P2-10.8 is the bookkeeping step of `thm:sst`. Say that (M1)-(M3),
`Σ D_t = Σ 2βVP*` and the hat balance are hypotheses. Optional: state `rate` as
`-Σ_i pairF (entropyVars g (hatState U_i)) (hatState R_i)` for an `SState` residual `R_i` with
`R_i E = R̂_i E + X_i`, so that it chains with P2-10.2.

**S4. `P2.md` does not list all the parts of the paper that are not stated.**
- `prop:consistency`(b) (lines 284-287): "= ∫ φ_i ∇·F_h, exact for linear F" and "F^ec differs from the mean by
  O(|u_k − u_i|²)" are not stated. The proposal says the O(·) part is left out. `P2.md` does not.
- `prop:consistency`(c) (lines 289-296): the bound on the weak effect of the dissipation (`C Φ_max σ_max h |Ω| …`) and
  the lower bound with `n_ik` in place of `ν_ik` are not stated. Only the first sentence is (P2-7.4).
- `thm:closure` (line 1025): "the projected states are admissible". Nothing states that `w̃_q = Σ_k φ_qk w_k` has
  `w̃_E < 0` when `φ_q· ≥ 0` and `Σ_k φ_qk = 1`. Without it, P2-8.0 cannot be applied to give the `ũ_q` that P2-8.1
  assumes. P2-8.4 also drops the rule's own conditions (`a_q > 0`, `φ_qk ≥ 0`, `Σ_k φ_qk = 1`). That only makes it
  more general, but the link to "exact for quadratics" is a hypothesis (already listed).
- `thm:wall` (line 1079): "the last sum is the discrete physical wall flux (zero if adiabatic, `Σ A_f/d q̂_a/(RT_w)` if
  isothermal)" is not stated. The adiabatic case is trivial (`gw = 0`).
- `lem:matched` (line 471): (M1) and (M2) are not stated ("by construction").
Fix: add these lines to "Where the Lean statement differs from the paper". Optional: add a one-line statement for the
admissibility of `w̃_q`.

### Minor

**M1. Statements that are true for elementary reasons.** None of them is wrong. Do not count them as results of
substance:
- P2-6.7, second conjunct: the definition of `c` with the sums reordered.
- P2-6.5b, second conjunct: `(d+3)/(2d(d+1)) = (d+3) · 1/(2d(d+1))`.
- P2-8.5: `w·(0, p y, 0) = (ρv/p)·p y = ρv·y`.
- P2-8.6, first part: a rearrangement of its hypothesis (one `linarith`, `NonVacuity.lean` section 5).
- P2-9.4: `w_m = v/(RT)` and `w_E = -1/(RT)`.
- P2-10.1, second part, and P2-10.2, second part: `hatState` is linear and kills `e_E + e_k` and `e_ω`.
- P2-10.6: `max(0, min(P*, c_l ε)) - ε ≤ P*` (one `linarith`, section 5).
- P2-10.8: see S2 and S3.
- P2-7.1 and P2-8.2 are short algebra too, but they are what the paper states.

**M2. Hypotheses that the proofs do not use** (I agree with the provers' list, from reading the statements):
- P2-9.0: `IsLinearMap K` and `P gw = gw` are not needed. The balance uses `K` symmetric (`frob G (K E) = frob E (K G)`),
  `Pᵀ = P` and `P² = P` only. Fix: keep `WallHyp` for uniformity, and add a line in `P2.md`.
- P2-10.4, fourth part: `0 ≤ μ_t` is not needed (`μ_t 2S:S = μ_t Q + (2/3) μ_t (div v)²` for any `μ_t`). Fix: drop it, or
  leave it and note it.
- P2-10.8: `Pi2 ≤ 0` is not used, because the conclusion does not list the sign of `Π̂^(2)`. The paper does list it
  ("every term except B̂ and Π̂^(4) is non-positive"). Fix: add `Pi2 ≤ 0` to the conclusion with a note that it is
  P1-1.5, or drop the hypothesis.

**M3. P2-10.3 (`lem:sstentropy`, lines 398-399): the first-order form is weaker than "Hessian ⪰ 0 with null space
ker T".** Strict monotonicity off `ker T` does not exclude a Hessian that is singular in a direction outside `ker T`
at single points (as with `x⁴`). The difference is listed in `P2.md`. Fix (optional): state `fderiv (fderiv η0) U`
`= Tᵀ ∇²η T` and its null space, if P1 has the Hessian of η.

**M4. P2-9.3 covers only the adiabatic no-slip wall** (`P` = momentum projector, `g = 0`). The isothermal projector
(momentum plus energy, `g = -1/(R T_w) e_E`, `P g = g`) is not shown to meet `WallHyp`. Fix: add it to P2-9.3, or
note it.

**M5. P2-10.7: `D_t` is the `μ_t` part `frob G (K_{μ_t, κ=0} G)`.** Its value `θ̄ μ̄_t Q(G_eff)` (line 447) is not
stated. P2-10.8 uses `D_t` only as a free input, so nothing breaks. Fix (optional): state the identity.

**M6. Docstrings.** The docstring of P2-6.5 also describes the linear-flux part, which is P2-6.5b. Harmless.

## Faithfulness checks done (no finding)

- Standard closure weights (lines 1006-1016): `stdWeight = ½μ_ij + ½δ_ij/d` equals `δ_ij/d + ½(μ_ij - δ_ij/d)`. The
  ratio is `(d+3):1`. The defect `A/(4d(d+1)) Σ_{i,j}` over ordered pairs equals `A/(2d(d+1)) Σ_{i<j}`. I checked the
  identity of P2-6.5 by hand: the zero-row-sum part of `ω` gives `-½ Σ a_ij [w][F]`.
- `B_c` per face (line 1006), `(1+δ)/(d(d+1)) A_f N_f`. I checked it by hand on the diamond at vertex 0:
  `B_00 = (2/3, 0) = ∮ φ_0² N`.
- `P2-6.4` drops "B symmetric". The identity holds without it, so the statement is more general.
- `P2-7.3`: "tr K(ν) = ds/2 at every vertex" is stronger than the paper ("interior"). It is true: the trace kills the
  boundary part, `Σ_k c_ki · e_ik = -d V_i` at every vertex, and `n_ik · e_ik = 2μ_ik ≥ 0`.
- `thm:closure` (lines 309-321, 1022-1043): the closure `b_i` of P2-8.1 is line 314 term for term. (H1) and (H2) in
  P2-8.4 are the paper's (H1) and (H2) with `a_q` relative to the area (`N_q = a_q A_f N_f`).
- Wall terms (lines 1067-1090): `h_f = d|T|/A_f`, `A_f = d|T||g_o|`, `N_f = -g_o/|g_o|`, `σ_f = c N_T d/h_f`,
  `e_a = P(w_a - g)`, `M_f e = P K(Pe ⊗ N) N`, `F̂_a = P F_T N - σ_f M_f e_a`, `X_f`, and `Π^w` with `1 + ς = 2` all
  match. The adjoint term `(K E_f) g_b` is the exact SIPG adjoint term (K is linear and `∫_f φ_a = A_f/d`). Its
  `w`-pairing is `(A_f/d) Σ_a e_a·F_T N_f`, and it sums to zero over the nodes. I checked P2-9.0 by hand: `w_b·F̂_b`
  splits into `e_b·F_T N - σ_f |e_b⊗N|²_K + g·F̂_b`.
- SST Π (lines 411-422, 1123-1133): `SSTPoint.Pi` is `-∇v^η : F^v + v^η·S` with `v^η = (w_0, θv, -θ, θ, 0)`,
  `∇θ = -∇T/(RT²)`, `τ` with `μ + μ_t`, the energy row `τv + κ∇T (+ D_k∇k)`, the `k` row `D_k∇k`, and the source `P_k - ε`
  in the `k` row. Expanding it gives `-θ(μ+μ_t)Q - κ|∇T|²/(RT²) + r_D + θ(P_k - ε)`, which is the formula of P2-10.4.
  `r_D = -D_k ∇k·∇θ` matches line 416.
- `vEta` `.tke` component `-w_E = 2β` matches line 400. `P2-10.8`: `-Σ w·(X - R_k)e_E = Σ 2β(X - R_k)`, and the bound
  is the paper's line 489-491 term for term.
- `lem:matched`: the upwind choice `k^up = k_i` if `ṁ_ij ≥ 0` and `k_b` = node value on outflow (`ṁ_b ≥ 0`) match lines
  464-467.

## Non-vacuity checks (`reviews/P2/NonVacuity.lean`)

- `diamond_conforming`: the 2D diamond of the P1 review (four right triangles around the origin) is `Conforming` with
  the four outer edges as boundary facets. The pairing is explicit: `(T,1) ↔ (T+1,2)`. `centre_off_boundary`: vertex 4
  is on no boundary facet. Through `p2_6_3` this gives `diamond.Closed 4`. So the hypotheses of P2-6.3, 6.5, 6.5b and
  8.4 hold on a real mesh with an interior vertex.
- Simpson's rule on every outer edge (points `(1,0), (½,½), (0,1)`, relative weights `1/6, 2/3, 1/6`) satisfies
  (H1) and (H2), and the support condition. Through `p2_8_4` this gives `Σ_q φ_qi N_q = β_i` on the diamond.
- `WallHyp` holds for `K = id`, `P = 1`, any `g`. On the reference triangle, `p2_9_3` (Navier-Stokes `K`, μ = 1, κ = 0,
  R = 1, `w̄_E = -1`, momentum projector, `N = N_f` of face 0) gives the hypotheses of P2-9.2. Then `p2_9_2` with
  `c = 1/2` gives nodal values with `D^gal - Π^w < 0`. So P2-9.2 is not vacuous, but see S1 about admissibility.
- Other hypotheses are easy to meet, and I checked them by hand: Tadmor flux in P2-8.1 (for example linear advection,
  `w = u`, `ψ = u²/2`, `F^ec = ½(a+b)y`); `w_E < 0` (P2-8.0); `y·e > 0` (P2-7.2); `V_i > 0` (P2-7.3, the diamond);
  `R, T > 0` (P2-10.4); P2-10.8 (all zero, or `β2 = V = P* = 1`, `S_k = 0`, `D_t = 1`, `D^gal = 2`, `Π^w = 0`).
- Section 5 of the file proves P2-8.6(i), P2-10.6 and P2-10.8(ii) in one or two lines each, without the project's
  proofs (M1, S2).

## Statement table

| Id | Faithful | Vacuity | Trivial | Notes |
|---|---|---|---|---|
| P2-6.1 | yes | none | no | `B` is the median `c + cᵀ`; boundary form in 6.3 |
| P2-6.2 | yes | none | no | off-diagonal form, the stronger direction |
| P2-6.3 | yes | none (diamond) | no | closes review M1 of P1 |
| P2-6.4 | yes, more general | none | no | `B` need not be symmetric |
| P2-6.5 | yes | none (diamond) | no | |
| P2-6.5b | yes | none | ratio part | |
| P2-6.6 | yes | none | no | one pair is enough (2D face = one edge) |
| P2-6.7 | partly | none (diamond, P1) | 2nd conjunct | S4, M1 |
| P2-7.1 | yes (D2 = A) | none | short algebra | |
| P2-7.2 | yes | none | no | |
| P2-7.3 | yes, stronger | none | no | trace at every vertex |
| P2-7.4 | first sentence of (c) | none | no | S4 |
| P2-8.0 | yes | none | no | |
| P2-8.1 | yes | none | no | |
| P2-8.2 | yes | none | short | needs 8.4 and 6.1 to chain |
| P2-8.3 | yes | none | no | |
| P2-8.4 | yes, (H1)/(H2) as hypotheses | none (Simpson) | no | S4 |
| P2-8.5 | yes | none | yes | M1 |
| P2-8.6 | yes | none | part (i) | M1 |
| P2-9.0 | yes | none | no | M2 |
| P2-9.1 | yes | none | no | |
| P2-9.2 | weaker (frozen K) | none | no | **S1** |
| P2-9.3 | yes, adiabatic only | none | no | M4 |
| P2-9.4 | yes | none | yes | M1 |
| P2-10.1 | yes | none | part 2 | |
| P2-10.2 | yes | none | part 2 | |
| P2-10.3 | first-order form | none | no | M3 |
| P2-10.4 | yes (pointwise) | none | no | M2 |
| P2-10.5 | yes, without (M1)/(M2) | none | no | S4 |
| P2-10.6 | yes | none | yes | M1 |
| P2-10.7 | yes | none | no | M5 |
| P2-10.8 | bookkeeping; (ii) trivial | none | yes | **S2, S3**, M2 |
