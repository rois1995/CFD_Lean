# P3 proposal: mixed meshes, other duals, and the complete entropy balance

**Status: proposal. Waiting for the user's approval. No Lean code is written yet.**

Written 2026-11-25. Same process as P1 and P2. Paper input unchanged: `Handbook/paper1/paper1.tex`, sha256
`32e1f260…`. Pins unchanged. P1 and P2 stay frozen; P3 only adds files.

## 1. Items

| # | Paper (line) | What | Size |
|---|---|---|---|
| 11 | `lem:avg` (683), proof 957-966 | averaged operator of mixed cells: closure from face balance; pulling splits are face balanced | M-L |
| 12 | `prop:splits` (691), proof 968-982 | slivers in thin hexahedra, weight 1/16, neighbour-fan (Kuhn) subset, dihedral angles ≤ 90° on bricks | M |
| 13 | `prop:defect` (162), proof 897-907 | exact pair production of a defect; Euler: it takes both signs for arbitrarily small jumps | M-L |
| 14 | `thm:complete` (530), proof 1165-1177 | the full semi-discrete operator, defined in Lean, and its entropy balance | L |

Optional at the end (D2 = B below would drop them): `prop:wallJST` (iii) and its spectrum claim (algebra), and the
parts of `prop:consistency`(b), (c) listed as "not stated" in `P2.md`.

## 2. Statement sketches

### Item 11 — `lem:avg`

- **P3-11.1 (closure from balance, any d).** `FacetBalanced bd`: for every vertex set `S`, the weighted area vectors
  of the interior facets with vertex set `S` sum to zero. This is weaker than the pairing of P2-6.3 (no equal
  weights, no one-to-one match). Then β and `B_c` are sums over boundary facets, and a vertex on no boundary facet is
  closed. It generalizes P2-6.3 and P1-5.0a.
- **P3-11.2 (shared facets, d = 3).** Two nondegenerate tetrahedra that share a triangle, with the opposite vertices
  on opposite sides, have opposite facet vectors. Also: the facet vector is ½ of the cross product of two facet
  edges, oriented away from the opposite vertex.
- **P3-11.3 (pulling splits).** The reference cells (quadrilateral, prism, pyramid, hexahedron) with their local
  numbering; the pulling splits as explicit lists of sub-simplices. Each quadrilateral face gets its two diagonals
  equally often: 2:2, 6:6, 3:3, 32:32 (proved by `decide` on finite data). The counts 12 (prism) and 64 (hexahedron)
  of splits.
- **P3-11.4 (face balance ⇒ closure).** A mixed mesh given as cells with weighted splits, where triangular faces
  match and every quadrilateral face is face balanced from both sides: the assembled weighted mesh is
  `FacetBalanced`. With P3-11.1: `Σ_k n_ik = 0` at every vertex on no boundary facet, `= -β_i` otherwise.
- **P3-11.5.** The averaged operator has no defect (`W^t = m_t`), is exact for linear fluxes, and its entropy
  production is the weighted mean of the productions of the splits (the flux is linear in `n`).

### Item 12 — `prop:splits`

- **P3-12.1.** Hexahedron: 32 of the 64 pulling splits contain a sliver tetrahedron; each of the 8 slivers is in 4
  splits, so it has weight 1/16 in the mean (`decide`).
- **P3-12.2.** For the brick `[0,a]×[0,b]×[0,h]`, the sliver's cosine of two dihedral angles tends to -1 as
  `h → 0` (angles → 180°). Stated for one sliver; the other seven by the cube symmetries.
- **P3-12.3.** Any sum of positive semidefinite element forms with weight ≥ 1/16 on a sliver is ≥ 1/16 of the
  sliver's form.
- **P3-12.4.** Neighbour-fan subset: for hexahedra it is the four Kuhn triangulations, it is face balanced, and it
  commutes with the 48 symmetries of the cube (so it does not depend on the numbering). On prisms, pyramids and
  quadrilaterals it contains all pulling splits.
- **P3-12.5.** On a brick every Kuhn tetrahedron has `g_a · g_b ≤ 0` for `a ≠ b`, so all dihedral angles are ≤ 90°.

### Item 13 — `prop:defect`

- **P3-13.1 (exact production).** For a C¹ flux in entropy variables along the straight path `w(s)`:
  `(F_k - F_i)·E = B̄(E) [w]` with `B̄ = ∫_0^1 B(w(s); E) ds`, and the production is `[w]·B̄(E)[w]` exactly.
- **P3-13.2 (Euler, both signs).** For an admissible state with `|v·E| < c|E|` and every ε > 0, there are admissible
  states within ε of it whose pair term `(F_k - F_i)·E` has production > 0, and others with production < 0.
  Proof route: jumps along the acoustic eigenvectors of `A(u; E)` (eigenvalues `v·E ± c|E|`) and strict convexity.

### Item 14 — `thm:complete`

- **P3-14.0 (the scheme as one definition).** On a weighted simplex mesh with boundary facets: Ismail-Roe central
  flux on `n_ik`; scalar dissipation with any `λ, ε2, ε4 ≥ 0`, set to zero on wall-crossing edges; the hybridized
  closure on boundary facets with a face rule (H1, H2); the P1 Galerkin viscous operator with `K(w̄_T)`, `μ + μ_t`;
  the weak no-slip wall per element.
- **P3-14.1 (balance).** For admissible states: `Σ_i w_i · R_i = -(B + Π^(2) + Π^(4) - Σ_T (D^gal_T - Π^w_T))`
  exactly, with `B` the closure point terms plus the physical wall flux, `Π^(2) ≤ 0` pair by pair, and
  `D^gal_T - Π^w_T ≥ (1 - 1/c) D^gal_T ≥ 0` for `c ≥ 1`.
- **P3-14.2 (boundary term).** `B` is zero at slip walls and bounded by the ghost entropy flux at the far field.
- **P3-14.3 (SA, SST).** SA: the same with `μ_t ≥ 0`. SST: with the matched form and the energy-consistent variant,
  the bound of P2-10.8c with all node terms ≤ 0.
- **P3-14.4 (mixed meshes).** The same on the averaged operator (uses item 11).

## 3. Decisions

**D1 — scope.**
- A = all of items 11-14 in this plan, done in stages: 12 and 13 first, then 11, then 14.
- B = only item 14 on simplex meshes now (the headline theorem); 11, 12, 13 later.
- **Recommended: A.** Item 14 on mixed meshes needs item 11 anyway, and 12, 13 are independent and can run in
  parallel.

**D2 — geometry of `lem:avg`.**
- A = the full chain from cell geometry: shared-facet orientation (P3-11.2), explicit pulling splits (P3-11.3),
  face balance ⇒ closure (P3-11.4). L.
- B = closure from an assumed `FacetBalanced` hypothesis (P3-11.1) plus the combinatorial counts only. M.
- **Recommended: A.** It removes the last geometric assumption of the mixed-mesh results.

Not proposed in either case: that a pulling split really fills its cell without overlap (a geometric fact about
convex polytopes; the operator identities do not need it, only the facet sums).
