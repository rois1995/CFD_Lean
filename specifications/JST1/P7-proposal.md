# P7 proposal: mixed meshes beyond affine cells (general hexahedra, prisms, pyramids)

Written 2026-11-26. Proposal only (research size): no statement is written or frozen until the user approves it.
Paper input `Handbook/paper1/paper1.tex`, sha256 `5ec5f9db…`. Numerics: `evidence/JST1/P7-hexsplit.py` (output
`P7-hexsplit.log`, numpy, unit cube numbering `x + 2y + 4z`).

## 0. Finding that shapes the batch (new paper gap G8)

The proof of `lem:avg` says "Each split is a conforming triangulation of C". On a general hexahedron this is false,
even when the cell is valid as a trilinear cell (positive Jacobian everywhere):

- Twisted cube: the top face turned by θ about the vertical axis. Its trilinear Jacobian is
  `det J = 1 - 2w(1-w)(1 - cos θ) ≥ (1 + cos θ)/2 > 0`. For `cos θ = 3/5`, `sin θ = 4/5` (all vertices rational), 8 of
  the 96 distinct pulling sub-tetrahedra are inverted (from θ ≈ 45° on), and the one-cell mesh averaged over the 64
  pulling splits is not facet balanced: 24 of its 32 interior triangles carry a nonzero area-vector sum. So the
  closure `Σ_k n_ik = -β_i` of `lem:avg` fails on such cells.
- Random cells (unit cube, vertices moved by up to 30 % of the edge, positive Jacobian on a grid): 21 % have an
  inverted pulling sub-tetrahedron, 1 % an inverted Kuhn (neighbour-fan) sub-tetrahedron. On the twisted cube the
  four Kuhn splits stay valid and balanced up to θ = 85°.

Today the Lean results (P3-11.7, P3-11.8) assume affine cells (`Mesh.Affine`: cell = A·ref + b), where the issue
cannot occur. The scheme itself only sees the vertex positions and the splits, never a trilinear map.

## 1. Item 22: statement sketches

New definitions (bridge only; frozen files unchanged): vertex positions of a cell from the mesh (`pos ∘ glob`), with
no `A, b`; `SplitOriented`: every sub-tetrahedron of every pulling split is nondegenerate, and all have the same
orientation relative to the reference cell (one global sign per cell); `ConformT`: `Mesh.Conform` with the centroid
test replaced by a tetrahedron test (at a shared face triangle, the sub-tetrahedra of the two cells lie on opposite
sides of it).

- **P7-22.1 (cell level, extends P3-11.7 clauses 1-2).** For any vertex positions of a reference cell with
  `SplitOriented`: in every pulling split, two sub-tetrahedra that share an interior triangle lie on opposite sides
  of it. (Proof idea: the side of the opposite vertex is the tetrahedron's determinant times a sign that depends only
  on the vertex order, so the reference signs transfer.)
- **P7-22.2 (mesh level, extends P3-11.8).** A mesh of hexahedra, prisms and pyramids with free vertices, `SplitOriented`
  and `ConformT`, averaged over the pulling splits, assembles to a valid weighted mesh that is facet balanced (so
  P3-11.1 and P3-14 apply). Plus: `Affine ∧ Conform → SplitOriented ∧ ConformT`, so P3-11.8 is a special case.
- **P7-22.3 (necessity, G8).** The twisted cube with `cos θ = 3/5`: its trilinear Jacobian is positive on `[0,1]³`;
  some pulling sub-tetrahedron is inverted (so `SplitOriented` fails); and the one-cell mesh is not facet balanced.
- **P7-22.4 (optional).** The same for the Kuhn (neighbour-fan) family with an explicit rational cell (to be found
  by search; random cells show it exists).

## 2. Decisions (my choice and reason; to confirm)

- **D1 — geometry.** Free vertex positions, not a trilinear map. Reason: the scheme only uses vertices and splits;
  the trilinear map appears only in 22.3 as the usual cell-validity test.
- **D2 — validity hypothesis.** `SplitOriented` (finite and checkable per cell: 96 determinant signs for a hexahedron;
  a mesh code can test it). Not "positive trilinear Jacobian", because 22.3 shows that is not enough.
- **D3 — conformity.** A tetrahedron-level side test at shared faces. The centroid test of `Mesh.Conform` is only
  right for convex cells.
- **D4 — counterexample cell.** Twisted cube with the rational rotation (3/5, 4/5): the Jacobian has a closed form and
  every determinant is a rational number (`norm_num`). Fallback if the facet-balance sum is too heavy for Lean: state
  that one split has two sub-tetrahedra on the same side of an interior triangle (the direct cause).
- **D5 — scope.** Pulling family (the paper's `lem:avg`) for 22.1-22.3; the Kuhn family only as 22.4.

Size: L (22.1 is combinatorics over the reference lists plus a sign lemma; 22.2 reuses the P3-11.8 proof with the new
hypotheses; 22.3 is a finite rational computation, the facet-balance part may be heavy).

## 3. For the paper session (G8)

`lem:avg` needs a hypothesis on the cells: every sub-tetrahedron of every split used must be positively oriented
(no inverted sub-tetrahedron). Positive trilinear Jacobian is not enough for the pulling splits (twisted cube,
θ > 45°). Suggested wording: "We assume that every sub-tetrahedron of the splits is positively oriented; for the
pulling splits this excludes strongly twisted hexahedra (e.g. a face turned by more than 45°)." Alternatively restrict
to the neighbour-fan family, which is more robust but still not valid on every trilinear-valid hexahedron.
