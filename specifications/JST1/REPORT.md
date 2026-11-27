# P1 report: Lean 4 check of the algebraic core of paper 1

Paper: frozen `paper1.tex` (SHA256SUMS OK). Lean v4.19.0, Mathlib `c44e0c8`, CFD_Lean pinned at `3a586a4`.
Repository: `rois1995/JST_Paper_Lean` (private), branch `p1-spec`. Reproduce: `./scripts/check.sh`.

## Result

36 frozen statements, 36 proved. 0 `sorry`, 0 `admit`, 0 new axioms, 0 `native_decide`. Every theorem uses only
`propext`, `Classical.choice`, `Quot.sound` (`KernelAudit.lean`). One local heartbeat raise
(`Paper1/Proofs/DualFacets.lean`, `rot_eq`, 18 polynomial cases). Bindings: `specifications/P1-results.json`.

| Item | Paper | Lean (Paper1.Proofs.…) | Proved |
|---|---|---|---|
| 1 | `lem:eps2` | `p1_1_0` … `p1_1_6` | yes |
| 2 | `lem:ec`, `prop:consistency`(a) | `p1_2_0` … `p1_2_7` (Ismail-Roe: `p1_2_5`) | yes |
| 3 | `lem:splitmean` | `p1_3_1` … `p1_3_4` | yes |
| 4 | `thm:visc` | `p1_4_0` … `p1_4_4`, `p1_4_3b` | yes |
| 5 | `prop:fv`, `lem:dissgeom`(a)-(c) | `p1_5_0a`, `p1_5_0b`, `p1_5_1` … `p1_5_8`, `p1_5_4b` | yes |

## Where the Lean statement differs from the paper

- `lem:eps2`: "sharp" is proved as "best constants" (P1-1.6); the bounds are not attained by two states (G1).
  The paper's reduction to v = 0 is not needed.
- `lem:ec` / `prop:consistency`(a): "interior vertex" is `Closed` (zero row of the boundary mass matrix); proved
  from a facet pairing for any d (P1-5.0a) and from CFD_Lean's conforming tetrahedral meshes (P1-5.0b). Free stream
  takes the closure's free-stream property as a hypothesis (the closure, `thm:closure`, is not in this task).
- `lem:splitmean`: G2 (sensor is a fixed input from π-weighted sums), G3 (boundary part of Λ_i is a given
  split-independent input), G4 (π, λ̂, Λ_i, Λ_k > 0 explicit), and one more hypothesis found while freezing: a pair
  that no split contains has n_ik = 0.
- `thm:visc`: `d ≤ 3` explicit; K(w)∇w is defined from the NS fluxes and proved equal to them (P1-4.0). Holds for
  any cell weights ω ≥ 0 (so also for split means).
- `prop:fv`: proved with the real median-dual facets for d = 2 (own segments) and d = 3 (CFD_Lean flag triangles);
  for general d only the algebraic core (P1-5.5).
- `lem:dissgeom`(a)-(c): sums run over ordered pairs (each pair twice); vertex statements need `Closed`. On mixed
  meshes `Closed` would come from `lem:avg` (not in this task).

## Notes on the larger results (not in this task)

- `lem:dissgeom`(d): Taylor expansion of the scalar dissipation and Loewner order of K_i. Needs second-order Taylor
  with remainder for smooth q (Mathlib `taylor_mean_remainder` / `ContDiff`), and `Matrix.PosSemidef` order. M.
- `thm:closure`: quadrature rules exact for quadratics on faces (H1, H2), entropy projection u(w̃), Tadmor for the
  hybridized pair terms. Reuses P1-2.2/2.5; needs the inverse map u(w) and face quadrature. M-L.
- `thm:wall`: interior penalty, Cauchy–Schwarz in the K-seminorm, Young; reuses P1-4.2. M.
- SST theorems: coupled entropy η∘T, matching conditions; mostly algebra once the discrete operators are defined. L.
- `lem:avg`, `prop:splits`: combinatorics of pulling splits and face balance (counting 32:32 etc.), sliver
  geometry. `lem:avg` would give `Closed` on mixed meshes. L.
- `thm:complete`: assembly of all the above. After the others, S-M.

## Reusable building blocks (`NumCore`, for other numerical methods)

Pair-sum identities, two-point entropy-conservative fluxes (Tadmor), log mean, P1 simplex calculus (gradients,
facets, edge expansion), weighted simplex meshes with their P1 operators (SBP-type identities, closure from facet
pairing), Galerkin/finite-volume equivalence.

## Sentence for the paper

Use this only after the paper fixes G1-G4 of `PAPER_GAPS.md` (else add "with the hypotheses of the repository"):

"Lemma \ref{lem:eps2} (with best constants), Lemma \ref{lem:ec}, Proposition \ref{prop:consistency}(a) (with the
free-stream property of the closure assumed), Lemma \ref{lem:splitmean}, Theorem \ref{thm:visc},
Proposition \ref{prop:fv} (for $d=2,3$) and Lemma \ref{lem:dissgeom}(a)--(c) are checked in Lean~4
(repository JST\_Paper\_Lean, commit ⟨final⟩)."

## Independent review

`reviews/P1/Review.md`: Accept with conditions, no blocking finding, no false or vacuous statement
(`reviews/P1/NonVacuity.lean`: admissible states, a valid 2D mesh with one closed and one non-closed vertex, a
facet-paired 1D vertex). Should-fix items S2-S4 are done (pins hashed, bindings cross-checked, trivial checks
labelled); S1 is the scope of the sentence above. Open minor points: M1 (β as ∫∇φ, divergence theorem not
formalized), M3 (no concrete interior vertex for P1-5.0b), M5 (Ismail-Roe not plugged into P1-2.2 by a theorem).

## P2: items 6-10 (larger results)

Paper input: `Handbook/paper1/paper1.tex` sha256 `32e1f260…` (G1-G4 fixed). 32 frozen statements, 32 proved
(`specifications/P2.md`, `P2-results.json`). `./scripts/check.sh`: 68 of 68 theorems, standard axioms only, no
heartbeat raise in P2.

| Item | Paper | Lean (Paper1.Proofs.…) |
|---|---|---|
| 6 | `prop:sbp`, `lem:bdefect`, `prop:consistency`(b), `prop:defect` (1st sentence) | `p2_6_1` … `p2_6_7`, `p2_6_5b` |
| 7 | `lem:dissgeom`(d) (quadratic q), `prop:consistency`(c) first part | `p2_7_1` … `p2_7_4` |
| 8 | `thm:closure` | `p2_8_0` … `p2_8_6` |
| 9 | `thm:wall` | `p2_9_0` … `p2_9_4` |
| 10 | `lem:sstentropy`, `prop:sstpde` (pointwise), `lem:matched`, `rem:sstconsistent`, `thm:sst` | `p2_10_1` … `p2_10_8` |

Gains: β and B_c are now proved sums over boundary facets (closes P1 review point M1); the closure's free-stream
property assumed in P1-2.7 is proved (P2-8.2). Review: `reviews/P2/Review.md`, Accept with conditions, no blocking
finding; scope notes in `P2.md`. Review follow-up (user choice A): addendum `Paper1/Spec/Addendum2.lean`, 4 more
statements, all proved: P2-8.0b (projected states are admissible), P2-9.2b (`thm:wall` sharpness with K(w̄_T) and
admissible states), P2-10.8b ((W_t) from the real element operators), P2-10.8c (`thm:sst` bound for the actual rate
d/dt Σ V η0). `./scripts/check.sh`: 72 of 72.

## P3: mixed meshes, other duals, complete theorem (items 11-14)

20 frozen statements in three stages, 20 proved (`specifications/P3.md`, `P3-results.json`). `./scripts/check.sh`:
92 of 92 theorems in total, standard axioms only (some use only `propext`). Statement reviews:
`reviews/P3/StatementReview-stage2.md` (no blocking finding); stage 3 was added for its point S1.

| Item | Paper | Lean (Paper1.Proofs.…) |
|---|---|---|
| 11 | `lem:avg` | `p3_11_1` … `p3_11_8`, `p3_11_2b`, `p3_11_4b` |
| 12 | `prop:splits` | `p3_12_1` … `p3_12_5` |
| 13 | `prop:defect` | `p3_13_1`, `p3_13_2` |
| 14 | `thm:complete` | `p3_14_1` … `p3_14_3` |

- `thm:complete` is proved for the scheme defined in Lean (`Paper1/Scheme/Complete.lean`: Ismail-Roe, JST
  dissipation, hybridized closure, P1 Galerkin viscous with K(w̄_T), weak wall) on any valid facet-balanced weighted
  simplex mesh; SST through P2-10.8c.
- Mixed meshes: a conforming mesh of affine hexahedra, prisms and pyramids averaged over their pulling splits is
  proved facet balanced (P3-11.8), so the complete theorem applies to it. Not covered: non-affine (trilinear) cells.
- Finite checks use `decide` / `decide +kernel` (kernel evaluation, no `native_decide`).
- Not formalized in P3: `prop:wallJST` (model analysis), the Taylor parts of `prop:consistency`(b),(c), the PDE form of
  `prop:sstpde`, the Hessian form of `lem:sstentropy` (first-order form proved). All four are P4 (below).

## Disk

Project `.lake`: about 5.7 GB. The CFD_Lean backup was deleted (38 GB free on 2026-11-25).

## P4: the remaining items (items 15-18), written in CFD_Lean

13 frozen statements, 13 proved (`specifications/JST1/P4.md`, `P4-results.json`), standard axioms only; with P1-P3:
105 of 105. Statement review: `reviews/JST1/P4-statement-review.md` (no blocking finding).

| Item | Paper | Lean (`CFDLean.JST1.Proofs.…`) |
|---|---|---|
| 15 | `prop:wallJST` (expansion, wall slip, cut edges, removed production, spectrum) | `p4_15_1` … `p4_15_6` |
| 16 | `prop:consistency`(b),(c) (P1 interpolant, O(\|Δu\|²), weak effect, face vector) | `p4_16_1` … `p4_16_4` |
| 17 | `prop:sstpde` (the PDE balance at a point) | `p4_17_1` |
| 18 | `lem:sstentropy` (Hessian: ∇²η ≻ 0; ∇²η0 ⪰ 0 with null space span{e_E + e_k, e_ω}) | `p4_18_1`, `p4_18_2` |

Not covered: `∫_T φ_i = m_T` (no simplex integration in Mathlib), the C² smoothness of the Ismail-Roe flux near the
diagonal (G6), the scaling of `prop:wallJST`(b). Paper gaps G5-G7 in `PAPER_GAPS.md`.

## P5: Ismail-Roe smoothness (G6) and the M1 bridge (items 19-20), written in CFD_Lean

7 frozen statements, 7 proved (`specifications/JST1/P5.md`, `P5-results.json`), standard axioms only; with P1-P4:
112 of 112. Statement review: `reviews/JST1/P5-statement-review.md` (no blocking finding).

- Item 19: the log mean is smooth on (0, ∞)² (`L(a, b) = a·E(ln b - ln a)`, `E = dslope exp 0` analytic); the
  Ismail-Roe flux is smooth on admissible × admissible; `prop:consistency`(b) "F^ec - mean = O(|Δu|²)" holds for the
  Ismail-Roe flux with one constant for all face vectors (P5-19.3, from P4-16.2). Closes G6 on the Lean side.
- Item 20: the paper's Euler state, pressure, admissibility, velocity, primitive map and flux equal M1's
  (bookkeeping); the differences (M1 has no entropy; the paper has no Jacobian or Roe flux) are listed in `P5.md`.

## P6: the simplex integral (item 21), written in CFD_Lean

3 frozen statements, 3 proved (`specifications/JST1/P6.md`), standard axioms only; with P1-P5: 115 of 115. The closed
simplex has Lebesgue measure `|det|/d!`, `∫_T φ_b = m_T`, and the Galerkin form of `prop:consistency`(b) holds with a
real integral (closes D1 of P4). Statement review: `reviews/JST1/P6-statement-review.md` (no blocking finding).

## P7: mixed meshes beyond affine cells (item 22), written in CFD_Lean

4 frozen statements, 4 proved (`specifications/JST1/P7.md`), standard axioms only; with P1-P6: 119 of 119. The closure
of `lem:avg` holds for hexahedra, prisms and pyramids with free vertex positions if every pulling sub-tetrahedron
keeps one orientation (P7-22.1, 22.2; the affine result P3-11.8 is a special case, 22.3); a twisted cube with
positive trilinear Jacobian violates it and its closure fails (22.4, paper gap G8). Statement review:
`reviews/JST1/P7-statement-review.md` (no blocking finding).

## P8: Kuhn split and interior-vertex failure (item 23), written in CFD_Lean

2 frozen statements, 2 proved (`specifications/JST1/P8.md`), standard axioms only; with P1-P7: 121 of 121. A valid
trilinear hexahedron (top face turned by about 106°) has a Kuhn split that is not a triangulation (P8-23.1); a
conforming 8-cell mesh of valid hexahedra has `Σ_k n_13,k = (0, 0, 7/30) ≠ 0` at the interior vertex 13 (P8-23.2,
paper gap G8). Proofs are closed kernel checks on integer coordinates. Statement review:
`reviews/JST1/P8-statement-review.md` (round 1 blocking finding fixed; round 2 not blocking). Maintainer acceptance:
2026-11-26.
