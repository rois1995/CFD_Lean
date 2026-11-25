# P3 stage 2: independent review of the statements (before the freeze)

Files reviewed: `Paper1/Scheme/Complete.lean`, `Paper1/Spec/Item14.lean` (P3-14.1-14.3), `Paper1/Spec/Item11b.lean`
(P3-11.4-11.6), along with the definitions they use (`NumCore/Balance.lean`, `NumCore/WMesh.lean`,
`Paper1/Mixed/RefCells.lean`, `Paper1/Spec/Item11a.lean`, `Paper1/Viscous/Wall.lean`, `Paper1/Viscous/Flux.lean`,
`Paper1/Spec/Addendum2.lean`). Paper: `paper1.tex`, live copy.

## Verdict

**OK to freeze once S1 has been handled.** S1 can be handled by documenting it and getting the user's ack, or by
adding one more statement. I found no false, vacuous or wrongly signed statement. P3-14.1, 14.2, 14.3 and 11.4 are true
by the derivations below, and 11.5 and 11.6 evaluate to `true`. `SchemeHyp` is satisfiable for every admissible state
field; there is a Lean witness for this. S1 is about scope, not truth. The plan the user approved (P3 proposal, D2 = A:
"full geometric chain for `lem:avg`") is not delivered by stage 2 as written.

Lean files written for this review (all compile; nothing outside `reviews/P3/` was touched):

- `reviews/P3/Stage2Eval.lean`: `#eval` of every conjunct of P3-11.5 and P3-11.6 gives `true`. Other checks:
  6/3/2 sub-tetrahedra per split, 64 distinct hexahedron splits, each hexahedron face triangle used by exactly 32
  splits, interior triangles of the hexahedron splits always counted 2.
- `reviews/P3/SchemeHypNonVacuity.lean`: `schemeHyp_diamond`. On the P2 diamond mesh with Simpson points,
  `SchemeHyp (Sd g u hu) bd fq aq u` holds for **every** `g` and every admissible `u`, with λ = ε2 = ε4 = 1, μ = κ = R
  = 1 and projected states from P2-8.0/P2-8.0b. It uses only `[propext, Classical.choice, Quot.sound]`. It includes a
  self-contained proof of "conforming ⇒ facet balanced", because `Proofs/Item11a` is not built. The momentum projector
  of a real wall also meets the projector part (through P2-9.3).
- `reviews/P3/Stage2Sides.lean`: on integer reference geometries (unit cube, right prism, square pyramid), every
  pulling sub-tetrahedron is nondegenerate. In every split, every interior triangle has its two tetrahedra on opposite
  sides, and the split volumes add up to the cell volume. This is the geometric premise that S1 is about.

## (1)-(2) Faithfulness and truth, statement by statement

### `Scheme/Complete.lean` (the scheme)

`resid i = -Σ_k (F^ec_ik + d2_ik - d4_ik) - b_i + R^v_i + R^w_i`, with `d_ik = λ[ε2(ũ_i-ũ_k) - ε4(L_i-L_k)]`:

- This matches eq. scheme (88-90) and eq. jst (225-228), including `ũ = (ρ, ρv, ρH)` = `enthalpyState` and
  `L_i = Σ_{N*(i)} (ũ_k - ũ_i)`.
- The sum runs over all `k`. That is equivalent to `N(i)`, because `n_ik = 0` off the stencil and λ is free.
- The closure is literally the one of `thm:closure` (309-321) and matches P2-8.1.
- The viscous term is `galerkinRes` with weights `ω_T|T|`, which is `thm:visc` on a weighted mesh.
- The wall term is `ω_T · Rwall`, assembled per element. With `K` symmetric and `P = Pᵀ = P²`, `Pg = g`, the
  algebra `Σ_a w_a·Rwall_a = Π^w_T + Σ_f (A_f/d) Σ_a g·F̂_a` checks out by hand: `P w_a = e_a + g`, `P e_a = e_a`,
  and the adjoint term pairs to `frob(G_T, K E_f) = frob(E_f, K G_T)`. This is P2-9.0.
- Mixed meshes: the weights `ω` on the viscous and wall terms are "the mean over the splits of the element forms"
  (paper line 1171). Closure points on split triangles with weights `ω` are what line 700 says ("both diagonals with
  weight 1/2 in the hybridized closure ... and in the weak wall").

### P3-14.1: true

My derivation, which is also the proof route:

- **Central part.** `-Σ_i w_i·Σ_k F^ec_ik = ½Σ_ik (w_k-w_i)·F^ec_ik = ½Σ_ik (ψ_k-ψ_i)·n_ik = Σ_i ψ_i·β_i`. It uses
  P1-2 (EC, symmetric, linear in `y`) and `Σ_k n_ik = -β_i`. The latter holds on every `WMesh` by P2-6.1 (row sums 0,
  column sums β), with no mesh hypothesis.
- **Closure.** `-Σ_i w_i·b_i = -Σ_i ψ_i·(Σ_q φ_qi N_q) + Bterm`, by P2-8.1 with `w̃_q = Σ φ_qk w_k` and
  `Σ_k φ_qk = 1`. So the identity needs `Σ_q φ_qi N_q = β_i` for all `i`. That **is derivable from `SchemeHyp`**:
  - `φ_qi = 0` off the facet of `q`, `fq q` is a boundary facet, and H1 together give
    `Σ_q φ_qi N_q = Σ_{p bd, i∈p} (1/d) areaVec p`.
  - P3-11.1, from Valid, 1 ≤ d and FacetBalanced, gives the same sum for `β_i`.
  - For a vertex on no boundary facet, both sides are 0.
  - H2 is not used. It is harmless: it holds for any rule exact for quadratics.
- **Dissipation.** With symmetric coefficients, `diss2_ki = -diss2_ik`, so the d2 part gives `Pi2`. P1-1 gives
  `(w_k-w_i)·(ũ_k-ũ_i) ≥ λ_γ (w_k-w_i)·(u_k-u_i) ≥ 0`, which with λε2 ≥ 0 gives `Pi2 ≤ 0`. The d4 part gives `Pi4`.
  Lean's `Pi4 = ½Σ_{i,k}` over ordered pairs is the paper's `Σ_{ik}` over pairs (each pair produces
  `-[w]_ki·d_ik`, line 1173).
- **Viscous and wall.** Viscous: `-Σ_T ω_T Dg_T` (P1-4.1). Wall: `+Σ_T ω_T Pw_T + wallFlux`, by P2-9.0 per element.
  P2-9.0 needs `WallHyp` for `K = viscFlux (Pv T) (wbar T)`:
  - linear (P1-4.2);
  - symmetric (P1-4.4, needs `wbar_E ≠ 0`);
  - PSD (P1-4.2, needs μ, κ ≥ 0, R > 0, d ≤ 3 and `wbar_E < 0`).
  `wbar_E < 0` holds because each `w_E = -ρ/p < 0`. All of these are in `SchemeHyp`.
- **Element bound.** Per element, by P2-9.1 (needs Nondeg from Valid, `1 ≤ d`, `c ≥ 1 > 0`).
- **Antisymmetry.** Follows from P1-2 (symmetric in the states, linear in `y`), `n_ki = -n_ik`, and symmetric
  coefficients.
- **Signs**, checked against the paper: `V du/dt = -ΣF_ik - b_i + visc + wall` (eq. scheme, `thm:visc` "contribution
  to V_i du_i/dt", the appendix "closure adds to V_a du_a/dt"). The `B` of the paper is `Bterm + wallFlux` (proof of
  `thm:complete`, lines 1167-1168).

### P3-14.2: true

- Slip points: `ψ̃·N - w̃·pressFlux = ρṽ·N - (ρṽ/p)·pN = 0` (P2-8.5).
- Far-field points: the hypothesis rearranges to the bound (P2-8.6(i)).
- It is close to a corollary of P2-8.5 and P2-8.6, but it is the paper's claim. See M6 for a docstring point.

### P3-14.3: true, and consistent with P2-10.8c

Instantiate P2-10.8c with:

- `Rhat i := -resid S u i`;
- `Dgal' T := ω_T Dg_T`, `PiW' T := ω_T Pw_T`, `Dt' T := ω_T Dt_T`;
- `Bhat := Bterm + wallFlux`.

Then:

- The balance hypothesis of 10.8c is the P3-14.1 identity, so it holds with equality.
- (W_t) for the primed terms follows from `Pw ≤ Dg - Dt` and `ω_T ≥ 0` (Valid).
- `SAdmissible` is `Admissible ∘ hatState`, which is in `SchemeHyp`.
- `w` and `β2` coincide (`w S u i = entropyVars g (hatState (Ut i t))`).

The conclusion is exactly the conclusion of P3-14.3. The hypotheses are jointly satisfiable:
- take the diamond witness with `Ut` affine in `t`;
- take `inD = false`, `X = Ck+Bk+Dh`, `Sk = Pst = Dt = 0` and `walls = ∅`, so that `Pw = 0 ≤ Dg`;
- take `R i` with `hatState (R i)` prescribed (`hatState` is onto).

### P3-11.4: true

- For a facet `p` with sorted vertex triple `a < b < c`, the vector `nv_S = (x_b-x_a)×(x_c-x_a)` depends only on `S`.
- By P3-11.2(i) and Nondeg (so the triple product is ≠ 0), `facetVec p = -(½)·sign_p·nv_S`.
- Hence `Σ_{p int, nodes p = S} ω_p facetVec p = -(½)(Σ ω_p sign_p) nv_S = 0`.
- Sets `S` that are not triangles give empty sums.

The `[LinearOrder ι]` and `[DecidableEq ι]` instances coexist, but `Decidable` is a subsingleton, so this is harmless
(see M5).

### P3-11.5 and P3-11.6: true (evaluated)

Both are finite Bool claims, and every conjunct evaluates to `true` (`Stage2Eval.lean`). Their reading matches the
docstrings:

- P3-11.5 is the pseudomanifold property: interior triangles are in 2 sub-tetrahedra, cell-face triangles in 1.
- P3-11.6 is the face weights: 1/2 per quadrilateral-face triangle, 1 per triangular face.

## (3) Vacuity

`SchemeHyp` is satisfiable, and generically so. `ReviewP3.schemeHyp_diamond` proves it for every gas and every
admissible nodal field on a 4-triangle mesh with real (nonzero) dissipation and viscosity. The free data of 14.3 are
consistent (see above). The hypotheses of P3-11.4 are satisfiable by any conforming tetrahedral mesh.

## (4) Trivial statements

- P3-14.2 is a two-line rearrangement once P2-8.5 is available. That is acceptable because it is a paper claim.
- P3-14.3 is a chaining corollary. That is acceptable because it is the headline.
- The antisymmetry conjunct of 14.1 is easy.
- No statement is trivial by accident. In particular, no hypothesis is contradictory, and no conclusion holds by
  `rfl`.

## Findings

### Blocking

None.

### Should-fix

**S1. The face balance ⇒ facet balance chain of `lem:avg` is not formal: it is the scope approved as D2 = A.**

What the stage covers:

- `SideBalanced` is `FacetBalanced` rewritten through P3-11.2. All facets with vertex set `S` share the vector
  `nv_S`, so the two are equivalent under Nondeg.
- P3-11.5 and 11.6 are combinatorial.

What is missing is the step that uses the paper's hypothesis ("both cells sharing the face contribute the mean over
the two diagonals, so the interior traces cancel in assembly"). Two premises are not formalised:

- (a) inside a split, the two sub-tetrahedra of an interior triangle lie on opposite sides;
- (b) two cells sharing a face lie on opposite sides of it.

Without them, "face balance ⇒ SideBalanced" exists only in the docstring of P3-11.6. The proposal (P3-11.4: "a mixed
mesh given as cells with weighted splits ... the assembled weighted mesh is FacetBalanced") and the approval (D2 = A,
"removes the last geometric assumption") promised more. Its caveat ("only the facet sums" are needed) does not hold:
the facet sums need (a) and (b).

Fix, either or both:

- **Add P3-11.7 (premise (a) on the reference cells, decidable over ℤ).** `Stage2Sides.lean` already evaluates it to
  `true`. Suggested statement, reusing that file's definitions (`side`, `oppV`, `splitOK`, `hexX`, `prismX`, `pyrX`
  moved to `Mixed/RefCells.lean`):
  ```lean
  def P3_11_7 : Prop :=
    (hex.splits.all fun s => splitOK hex hexX (hex.pull s.1 s.2)) = true ∧
    (prism.splits.all fun s => splitOK prism prismX (prism.pull s.1 s.2)) = true ∧
    (pyramid.splits.all fun s => splitOK pyramid pyrX (pyramid.pull s.1 s.2)) = true
  ```
  Optionally add the affine-invariance lemma: an affine map with `det > 0` multiplies every triple product by `det`,
  so sides are kept. This covers all affine images of the reference cells.
- **Record the deviation.** In any case, record in `specifications/P3.md` under "Differences from the paper" that:
  - premise (b), and premise (a) for non-affine cells, are mesh-validity assumptions;
  - the assembly "cells + splits ⇒ `SideBalanced`" is not a Lean theorem;
  - the mixed-mesh case of P3-14 therefore rests on `FacetBalanced` as a hypothesis.

  Because this changes an approved decision, ask the user before the freeze.

**S2. 2D mixed meshes (quadrilaterals) have no counterpart of P3-11.4.** P3-11.2 and 11.4 are `d = 3` only, but the
paper's mixed meshes include quadrilaterals for `d = 2` (line 550), and `SchemeHyp` allows `d = 2`. Fix: add the 2D
analogue (cheap). The facet vector of an edge is `±` the rotated edge, pointing away from `o`:
```lean
def perp2 (v : Vec 2) : Vec 2 := ![v 1, -v 0]
-- P3_11_2b: T.Nondeg → [o, a, b].Nodup →
--   T.facet o = (if 0 < dot (perp2 (T.x b - T.x a)) (T.x o - T.x a) then -1 else 1 : ℝ) • perp2 (T.x b - T.x a)
-- facetSide2 / SideBalanced2 with the sorted pair a < b, and P3_11_4b : M.Valid → SideBalanced2 M bd → FacetBalanced bd
```
The alternative is to state in `P3.md` that the 2D mixed case rests on `FacetBalanced` as a hypothesis.

### Minor

- **M1.** H2 (and `aq > 0`, `φ ≥ 0`) are not needed for P3-14.1. Keeping H2 is fine for faithfulness ("exact for
  quadratics"), but the proof will not use it. A one-line note in the spec would prevent a "where is H2 used?" question
  at proof time.
- **M2.** The laminar/SA case of `thm:complete` is stated as the identity for `Σ_i w_i·(V du/dt)_i`, not as a
  `d/dt Σ V_i η` bound. Only 14.3 has a `HasDerivAt`. This is equivalent by the chain rule, so only a docstring
  sentence is needed. An optional conjunct `HasDerivAt (fun s => Σ V_i U(u_i s)) (Σ w·resid) t`, under
  `V_i u_i' = resid_i`, would mirror the paper literally.
- **M3.** `walls` is not tied to `bd`, and the inviscid part at wall points (`Fs = pressFlux`) is not tied to `walls`.
  Truth is unaffected: the identity is algebraic, and this is a generalisation. Optionally document "wall facets may be
  any facets" in the docstring of `SchemeHyp`. Do not add the hypothesis; it would only weaken the theorem.
- **M4.** Wall on mixed meshes: `σ_f` uses the sub-tetrahedron's `h_f` and `N_T`. Line 700 says "with the cell height
  in the penalty". For pulling splits of bricks, and of prisms with the wall on a triangular face, the apex is on the opposite face, so
  the two coincide. For general cells they do not, and the bound `Π^w ≤ D^gal/c` is per sub-tetrahedron. Record this
  as a modelling choice, or as a paper/code gap if the code uses the cell height.
- **M5.** `P3_11_4`, `facetSide` and `SideBalanced` carry both `[DecidableEq ι]` and `[LinearOrder ι]`. This is
  harmless for truth, but expect `convert`/`Subsingleton.elim` friction where a `Finset ι` equality instance meets the
  one from `LinearOrder`.
- **M6.** The docstring of P3-14.2 says "slip-wall point (pressure flux)". No-slip wall points also use the pressure
  flux (line 1078), so say "wall point (slip or no-slip: pressure flux)".
- **M7.** P3-14.3 leaves `Vv` and `Dt` free (not `S.M.V` and not the `μ_t` part of `K`), as in P2-10.8c. This is a
  generalisation and is fine. The docstring says "with `μ + μ_t` in `Pv`" but nothing enforces it. It may help to say
  "`Dt` is any family with `Σ ω Dt = Σ 2βVP*`".
- **M8.** The docstring of P3-11.6 ("this is the side balance of P3-11.4 for a mesh whose split tetrahedra lie on
  opposite sides ...") reads as if a Lean statement makes that step. Reword it to "gives, with premises (a), (b) of
  S1, the side balance" until S1 is resolved.
- **M9.** The proof of 14.1 needs a facet-balanced form of P2-8.4(i), `Σ_q φ_qi N_q = β_i`. Only the conforming
  version is frozen. This is a proof-plan note, not a statement change. `balanced_of_conforming` in
  `SchemeHypNonVacuity.lean` (about 30 lines, via `Finset.sum_ninvolution`) can be reused for P3-11.1(i).
