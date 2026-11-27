# CFD_Lean theorem catalog (MC-C)

595 promised theorems, grouped by layer.

## Rules

Each entry of `theorems.json` is one promised theorem: the 15 accepted M1 theorems (M1 has no result map; its
accepted list is the `#print axioms` list of the hash-pinned `Integrity.lean`, with IDs `M1-1`..`M1-6` for the
targets of `specifications/M1.md` and `M1-aux` for the finite-sum lemmas), every declaration bound in
`specifications/M2-results.json` .. `M5-results.json`, the FV1D, FVP, FVA, FVN and FVNA result maps, every theorem of `specifications/MC-N-results.json`, and the
121 paper-1 proofs bound in `specifications/JST1/P1-results.json` .. `P8-results.json` (IDs `P1-x.y` .. `P8-x.y`).

**Status.** `accepted`: M1-M4, independently accepted (`reviews/*/Acceptance.md`). `pending`: M5, implemented,
independent review pending. FV1D is independently accepted (`reviews/FV1D/Acceptance.md`). FVN (FV1D on a
non-uniform periodic 1D mesh, `specifications/FV1D-nonuniform-results.json`) is `pending`: implemented, independent
review pending. FVNA is independently accepted (`reviews/FVNA/Acceptance.md`). `candidate`: MC-N, moved from JST_Paper_Lean on branch `mc-n`, not yet merged to `main`;
JST1, the paper-1 statements folded from JST_Paper_Lean by MR-2 and the P4-P8 statements written here (self-checked,
AI-reviewed, not independently accepted). The 37 JST1 proofs whose statement is an MC-N theorem delegate to it and carry its layer, tags and summary.

**Layer** (by the mathematical object a statement is about, not by milestone or module):

| Layer | Content |
|---|---|
| Foundations | Generic algebra and analysis: sums of squares, dot products, state coordinates, unit normals, log mean. |
| Geometry | Simplices and meshes: P1 simplex calculus, facet vectors, median-dual flags, interfaces, patches, volumes, boundary records, used nodes, facet/side balance, pulling splits of mixed cells. |
| Discrete operators | Mesh operators independent of the flux function: edge incidence and assembly, P1/SBP operators (c, B, beta, defect), Galerkin and finite-volume residual identities, edge dissipation tensors. |
| Entropy framework | Entropy production and conservation identities of pair fluxes and boundary closures. |
| Physics models | Ideal-gas Euler states, admissibility, entropy variables, physical flux and Jacobian, Roe averages, linearization and eigenstructure; the Navier-Stokes viscous matrix, wall conditions and the SST model. |
| Schemes | Numerical fluxes and their residuals: Roe flux, Roe edge/boundary transfers, boundary kinds, closures, residual balances, constant-state and free-stream consistency, JST dissipation coefficients, viscous and wall element terms, entropy bounds of the complete scheme. |
| Time | The explicit Euler update, amounts, conservation balances and step controls. |
| Execution | Executable array kernels and their refinement to the mathematical schemes (Burgers E0, E0b, E0c). |

**Method tags** (`FEM`, `FVM`, both, or `method-free`):

- `FEM`: statements about Galerkin / P1-basis / SBP-operator objects (Galerkin residual, `c_ik`, boundary matrix `B`,
  `beta_i`, closed vertices of the P1 operator). Tagged `FEM` and `FVM` when the statement also involves the
  finite-volume side: an FV <-> Galerkin equivalence, dual edge normals `n_ik`, or median-dual facets.
- `FVM`: median-dual geometry (flags, interfaces, patches, dual volumes, boundary records), interface/edge fluxes
  and edge dissipation, assembly and incidence, boundary transfers and closures, residual balances, and the time
  update on dual volumes.
- `method-free`: pure algebra/analysis of states, fluxes, the Roe matrix, the log mean, single-simplex calculus,
  primal-mesh combinatorics and facet/side balance, entropy-production calculus, and the pointwise Euler step.
- Entropy statements about one pair of states (a pair flux, its production) are `method-free`; sums over the nodes or
  pairs of a mesh, or semi-discrete rates over dual volumes `V_i`, are `FVM`.

**Burgers** (milestones `B0` .. `B4`, `B3b`, `E0`, `E0b`, `E0c`, status `accepted`: implementation accepted, see `reviews/Burgers-Implementation/Review.md`). The declarations
bound in `specifications/Burgers-B0-results.json` .. `Burgers-B4-results.json`, `Burgers-B3b-results.json`, `Burgers-E0-results.json`, `Burgers-E0b-results.json` and `Burgers-E0c-results.json`: the scalar two-point-flux finite-volume
core on a periodic grid, the incremental-form stability lemmas, the convexity of bounded states and of the total
variation, the MUSCL reconstruction with a limiter certificate (Discrete operators), the flux certificates and the
Burgers Rusanov flux (Schemes), the Forward Euler step, its stability under a CFL hypothesis, the generic SSP
Runge-Kutta composition and the multi-step results (Time), the entropy certificates of a two-point flux and the
semidiscrete entropy inequalities (Entropy framework), the refinement of the executable array kernel (Execution). `FVM` marks the periodic finite-volume statements; the
generic time-stepping statements are `method-free`.

**Source.** The contract or result map and the result ID (with stage, or the JST statement for MC-N and JST1).

Generated by `python3 scripts/catalog.py` from `theorems.json`; `scripts/verify.py` checks coverage, tag values and
that this file equals the generated text. Do not edit by hand.

## Counts

| Layer | Theorems | FEM | FVM | FEM + FVM | method-free |
|---|---:|---:|---:|---:|---:|
| Foundations | 12 | 0 | 0 | 0 | 12 |
| Geometry | 75 | 0 | 43 | 4 | 28 |
| Discrete operators | 94 | 10 | 65 | 19 | 0 |
| Entropy framework | 32 | 0 | 26 | 0 | 6 |
| Physics models | 93 | 0 | 0 | 0 | 93 |
| Schemes | 105 | 7 | 80 | 7 | 11 |
| Time | 105 | 0 | 85 | 0 | 20 |
| Execution | 79 | 0 | 78 | 0 | 1 |
| **Total** | 595 | 17 | 377 | 30 | 171 |

| Method tag | Theorems carrying it |
|---|---:|
| FEM | 47 |
| FVM | 407 |
| method-free | 171 |

| Milestone | Status | Theorems |
|---|---|---:|
| M1 | accepted | 15 |
| M2 | accepted | 66 |
| M3 | accepted | 51 |
| M4 | accepted | 39 |
| M5 | pending | 43 |
| MC-N | candidate | 37 |
| B0 | accepted | 12 |
| B1 | accepted | 9 |
| B2 | accepted | 23 |
| B3 | accepted | 24 |
| B4 | accepted | 14 |
| E0 | accepted | 20 |
| E0b | accepted | 14 |
| B3b | accepted | 40 |
| E0c | accepted | 19 |
| JST1 | candidate | 121 |
| FV1D | accepted | 4 |
| FVP | accepted | 1 |
| FVA | accepted | 2 |
| FVN | pending | 17 |
| FVNA | accepted | 20 |
| E1 | pending | 4 |

## Foundations (12)

| Theorem | ID | Methods | Status | Summary |
|---|---|---|---|---|
| `CFDLean.squareSum_mul` | M1-aux | method-free | accepted | Scaling a vector by a multiplies its sum of squares by a². |
| `CFDLean.squareSum_div` | M1-aux | method-free | accepted | Dividing a vector by a divides its sum of squares by a². |
| `CFDLean.dot_add` | M1-6 | method-free | accepted | The dot product is additive in its second argument. |
| `CFDLean.dot_mul` | M1-6 | method-free | accepted | The dot product is homogeneous in its second argument. |
| `CFDLean.Coordinates.decode_encode` | M2-J | method-free | accepted | Decoding the five-coordinate encoding of a 3D conservative state returns the state. |
| `CFDLean.Coordinates.encode_decode` | M2-J | method-free | accepted | Encoding a decoded five-coordinate vector returns the vector. |
| `CFDLean.Coordinates.unitNormal_dot_self` | M2-J | method-free | accepted | The unit normal of a nonzero area vector has unit length. |
| `CFDLean.Num.logMean_properties` | MC-N.P1-2.4 | method-free | candidate | The logarithmic mean of two positive numbers is symmetric, positive, equals a at a = b, and satisfies b − a = L(a,b)(log b − log a). |
| `CFDLean.JST1.Proofs.p1_2_4` | P1-2.4 | method-free | candidate | The logarithmic mean of two positive numbers is symmetric, positive, equals a at a = b, and satisfies b − a = L(a,b)(log b − log a). |
| `CFDLean.JST1.Proofs.p3_12_3` | P3-12.3 | method-free | candidate | A weighted sum of nonnegative forms with weight at least 1/16 on one element is at least 1/16 of that element's form. |
| `CFDLean.JST1.Proofs.p4_16_2` | P4-16.2 | method-free | candidate | A symmetric, consistent two-point flux that is C² near the diagonal differs from the mean flux by O(\|u_k − u_i\|²). |
| `CFDLean.JST1.Proofs.p5_19_1` | P5-19.1 | method-free | candidate | The logarithmic mean is Cⁿ for every n on (0,∞)², across the diagonal a = b (L(a,b) = a·E(ln b − ln a) with E(t) = (eᵗ−1)/t analytic). |

## Geometry (75)

| Theorem | ID | Methods | Status | Summary |
|---|---|---|---|---|
| `CFDLean.MedianDual.faceVector_sum` | M3-G | method-free | accepted | The four face area vectors of a tetrahedron sum to zero. |
| `CFDLean.MedianDual.flagBoundary_sum` | M3-G | FVM | accepted | The boundary area vectors of each median-dual flag tetrahedron sum to zero. |
| `CFDLean.MedianDual.outwardTriangle_dot` | M3-G | FVM | accepted | The outward dual triangle of a flag dotted with its edge vector is one 24th of six times the tetrahedron volume. |
| `CFDLean.MedianDual.localInterface_reverse` | M3-G | FVM | accepted | Local median-dual interface vectors are antisymmetric in their two nodes. |
| `CFDLean.MedianDual.localPatch_eq` | M3-G | FVM | accepted | A local boundary patch is one third of the face vector, or zero at the vertex opposite the face. |
| `CFDLean.MedianDual.sum_internal_one` | M3-G | FVM | accepted | The first family of internal flag faces cancels when summed over the flags of a vertex. |
| `CFDLean.MedianDual.sum_internal_two` | M3-G | FVM | accepted | The second family of internal flag faces cancels when summed over the flags of a vertex. |
| `CFDLean.MedianDual.flag_boundaries_identify` | M3-G | FVM | accepted | The flag boundary vectors of a vertex sum to its local hull vector. |
| `CFDLean.MedianDual.localHull_identification` | M3-G | FVM | accepted | The local hull vector of a vertex is the sum of its interface vectors and boundary patches. |
| `CFDLean.MedianDual.local_closure` | M3-G | FVM | accepted | In one tetrahedron the interface vectors and boundary patches of each vertex sum to zero. |
| `CFDLean.MedianDual.MeshData.mem_faceNodes` | M3-G | method-free | accepted | A node lies on face j of a cell iff it is a cell vertex other than vertex j. |
| `CFDLean.MedianDual.MeshData.face_membership` | M3-G | method-free | accepted | A three-node set lies in a cell iff it is one of the cell's faces. |
| `CFDLean.MedianDual.MeshData.faceArea_cancel` | M3-G | method-free | accepted | On a conforming mesh two distinct occurrences of the same primal face have opposite area vectors. |
| `CFDLean.MedianDual.MeshData.assembledArea_reverse` | M3-G | FVM | accepted | Assembled median-dual edge area vectors are antisymmetric. |
| `CFDLean.MedianDual.MeshData.assembledArea_row` | M3-G | FVM | accepted | The assembled areas at a node sum to its local interface vectors summed over all cells. |
| `CFDLean.MedianDual.MeshData.edge_incidence_sum` | M3-G | FVM | accepted | The incidence-signed edge areas at a node equal the row sum of assembled areas. |
| `CFDLean.MedianDual.MeshData.ownedPatch_local` | M3-G | FVM | accepted | The patch area a node owns on a face occurrence is the corresponding local patch. |
| `CFDLean.MedianDual.MeshData.interior_cancel` | M3-G | FVM | accepted | On a conforming mesh the patches on interior faces cancel at every node. |
| `CFDLean.MedianDual.MeshData.boundaryKey_injective` | M3-G | FVM | accepted | A boundary record is determined by its face and owner key. |
| `CFDLean.MedianDual.MeshData.boundaryKey_range` | M3-G | FVM | accepted | Boundary keys are exactly the pairs of a face used once and a node on that face. |
| `CFDLean.MedianDual.MeshData.all_patches_boundary` | M3-G | FVM | accepted | On a conforming mesh all patches at a node sum to the areas of its boundary records. |
| `CFDLean.MedianDual.MeshData.metric_closed` | M3-G | FVM | accepted | On a conforming mesh the median dual of every node is metrically closed (zero metric defect). |
| `CFDLean.MedianDual.flag_card` | M3-V | FVM | accepted | A tetrahedron has 24 median-dual flags. |
| `CFDLean.MedianDual.vertexFlags_card` | M3-V | FVM | accepted | Each tetrahedron vertex has 6 median-dual flags. |
| `CFDLean.MedianDual.flag_determinant` | M3-V | FVM | accepted | Each flag's signed six-volume is its frame sign times one 24th of the tetrahedron's. |
| `CFDLean.MedianDual.flag_volume` | M3-V | FVM | accepted | Each flag's volume is one 24th of the tetrahedron's volume. |
| `CFDLean.MedianDual.localDualVolume_eq` | M3-V | FVM | accepted | The local dual volume of a vertex in a tetrahedron is a quarter of its volume. |
| `CFDLean.MedianDual.MeshData.dualVolume_formula` | M3-V | FVM | accepted | A node's dual volume is the sum of Vol(T)/4 over its incident cells. |
| `CFDLean.MedianDual.MeshData.dualVolume_pos` | M3-V | FVM | accepted | Used nodes have positive dual volume. |
| `CFDLean.MedianDual.MeshData.dualVolume_unused` | M3-V | FVM | accepted | Unused nodes have zero dual volume. |
| `CFDLean.MedianDual.MeshData.volume_partition` | M3-V | FVM | accepted | On a conforming mesh the dual volumes sum to the total cell volume. |
| `CFDLean.Boundary.boundary_record_unique` | M4-B | FVM | accepted | A boundary record is determined by its primal face and owner node. |
| `CFDLean.Boundary.boundary_record_range` | M4-B | FVM | accepted | Boundary records exist exactly for the faces used once and the nodes on them. |
| `CFDLean.Time.mesh_used_volume_pos` | M5-V | FVM | pending | Used nodes have positive dual volume. |
| `CFDLean.Time.tail_used` | M5-V | FVM | pending | The tail of every edge is a used node. |
| `CFDLean.Time.head_used` | M5-V | FVM | pending | The head of every edge is a used node. |
| `CFDLean.Time.owner_used` | M5-V | FVM | pending | The owner of every boundary record is a used node. |
| `CFDLean.Num.Simplex.calculus` | MC-N.P1-5.1 | method-free | candidate | On a nondegenerate simplex the P1 gradients sum to zero, are dual to the edges, reproduce the identity, and the facet vectors sum to zero. |
| `CFDLean.Num.Simplex.facet_cross3` | MC-N.P3-11.2 | method-free | candidate | A tetrahedron facet vector is half the cross product of two facet edges oriented away from the opposite vertex; neighbours across a triangle have opposite facet vectors. |
| `CFDLean.Num.Simplex.facet_perp2` | MC-N.P3-11.2b | method-free | candidate | A triangle facet vector is the rotated facet edge pointing away from the opposite vertex. |
| `CFDLean.Num.pathSimplex_nonobtuse` | MC-N.P3-12.5 | method-free | candidate | Every Kuhn tetrahedron of a brick is nondegenerate with pairwise nonpositive gradient products (no obtuse dihedral angle). |
| `CFDLean.Num.WMesh.dissGeom_edge` | MC-N.P1-5.2 | FVM | candidate | Dual normals satisfy n·e = 2μ > 0 on edges, and the edge projection ν is a positive multiple of e with \|ν\| = n·e/\|e\|. |
| `CFDLean.Num.WMesh.dissGeom_outer` | MC-N.P1-5.3 | FEM + FVM | candidate | The Galerkin coefficients give Σ c⊗e = V·I, dual normals give Σ n⊗e = 2V·I at closed vertices, and the dual volumes sum to \|Ω\|. |
| `CFDLean.Num.WMesh.dissGeom_calibration` | MC-N.P1-5.4 | FVM | candidate | At closed vertices the edge-projected tensor G(ν) has trace 2dV and G(n) has trace at least 2dV, with equality iff every normal is a nonnegative multiple of its edge. |
| `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced` | MC-N.P3-11.4 | method-free | candidate | On a mesh of nondegenerate tetrahedra side balance implies facet balance. |
| `CFDLean.Num.WMesh.facetBalanced_of_sideBalanced2` | MC-N.P3-11.4b | method-free | candidate | On a mesh of nondegenerate triangles side balance implies facet balance. |
| `CFDLean.Num.dualFacets_grad` | MC-N.P1-5.6 | FEM + FVM | candidate | The median-dual facets of a tetrahedron (and of a triangle) are (\|T\|/(d+1))(g_k − g_i) in terms of P1 gradients. |
| `CFDLean.JST1.Proofs.p1_5_1` | P1-5.1 | method-free | candidate | On a nondegenerate simplex the P1 gradients sum to zero, are dual to the edges, reproduce the identity, and the facet vectors sum to zero. |
| `CFDLean.JST1.Proofs.p1_5_2` | P1-5.2 | FVM | candidate | Dual normals satisfy n·e = 2μ > 0 on edges, and the edge projection ν is a positive multiple of e with \|ν\| = n·e/\|e\|. |
| `CFDLean.JST1.Proofs.p1_5_3` | P1-5.3 | FEM + FVM | candidate | The Galerkin coefficients give Σ c⊗e = V·I, dual normals give Σ n⊗e = 2V·I at closed vertices, and the dual volumes sum to \|Ω\|. |
| `CFDLean.JST1.Proofs.p1_5_4` | P1-5.4 | FVM | candidate | At closed vertices the edge-projected tensor G(ν) has trace 2dV and G(n) has trace at least 2dV, with equality iff every normal is a nonnegative multiple of its edge. |
| `CFDLean.JST1.Proofs.p1_5_4b` | P1-5.4b | FVM | candidate | On the Cartesian model with box-dual vectors the edge tensors satisfy G(ν) = G(n) = 2V I. |
| `CFDLean.JST1.Proofs.p1_5_6` | P1-5.6 | FEM + FVM | candidate | The median-dual facets of a tetrahedron (and of a triangle) are (\|T\|/(d+1))(g_k − g_i) in terms of P1 gradients. |
| `CFDLean.JST1.Proofs.p3_11_2` | P3-11.2 | method-free | candidate | A tetrahedron facet vector is half the cross product of two facet edges oriented away from the opposite vertex; neighbours across a triangle have opposite facet vectors. |
| `CFDLean.JST1.Proofs.p3_11_3` | P3-11.3 | method-free | candidate | The pulling splits of hexahedron, prism, pyramid and quadrilateral use both diagonals of each quadrilateral face equally often, one per split. |
| `CFDLean.JST1.Proofs.p3_12_1` | P3-12.1 | method-free | candidate | Half of the 64 hexahedron pulling splits contain a sliver, and each of the 8 slivers lies in 4 splits (weight 1/16). |
| `CFDLean.JST1.Proofs.p3_12_2` | P3-12.2 | method-free | candidate | As the brick thickness tends to zero, two dihedral angles of the sliver tend to 180°. |
| `CFDLean.JST1.Proofs.p3_12_4` | P3-12.4 | method-free | candidate | The neighbour-fan splits of the hexahedron form 4 Kuhn triangulations, face balanced and symmetric; on prisms and pyramids all pulling splits. |
| `CFDLean.JST1.Proofs.p3_12_5` | P3-12.5 | method-free | candidate | Every Kuhn tetrahedron of a brick is nondegenerate with pairwise nonpositive gradient products (no obtuse dihedral angle). |
| `CFDLean.JST1.Proofs.p3_11_2b` | P3-11.2b | method-free | candidate | A triangle facet vector is the rotated facet edge pointing away from the opposite vertex. |
| `CFDLean.JST1.Proofs.p3_11_4` | P3-11.4 | method-free | candidate | On a mesh of nondegenerate tetrahedra side balance implies facet balance. |
| `CFDLean.JST1.Proofs.p3_11_4b` | P3-11.4b | method-free | candidate | On a mesh of nondegenerate triangles side balance implies facet balance. |
| `CFDLean.JST1.Proofs.p3_11_5` | P3-11.5 | method-free | candidate | Pulling splits are pseudomanifolds: an interior triangle bounds two sub-tetrahedra, a triangle on the cell boundary one. |
| `CFDLean.JST1.Proofs.p3_11_6` | P3-11.6 | method-free | candidate | With equal split weights each triangle of a quadrilateral cell face has total weight 1/2 and each triangular face weight 1. |
| `CFDLean.JST1.Proofs.p3_11_7` | P3-11.7 | method-free | candidate | In affine cells the pulling-split tetrahedra are nondegenerate, lie on opposite sides of shared interior triangles, and boundary ones lie on the centroid side. |
| `CFDLean.JST1.Proofs.p3_11_8` | P3-11.8 | method-free | candidate | A conforming mesh of affine hexahedra, prisms and pyramids averaged over pulling splits is a valid facet-balanced weighted tetrahedral mesh. |
| `CFDLean.JST1.Proofs.p4_16_4` | P4-16.4 | FVM | candidate | On the face vector the dissipation sum is at least Σ c̄ (n·e) sec ϑ, which is unbounded at fixed \|Ω\| on stretched triangles. |
| `CFDLean.JST1.Proofs.p6_21_1` | P6-21.1 | method-free | candidate | The closed simplex (convex hull of the vertices) is where all barycentric coordinates are ≥ 0, and its Lebesgue measure is \|det(x_β − x_0)\|/d!. |
| `CFDLean.JST1.Proofs.p6_21_2` | P6-21.2 | method-free | candidate | Each barycentric coordinate of a nondegenerate simplex is integrable on it and ∫_T φ_b = \|T\|/(d+1) = m_T. |
| `CFDLean.JST1.Proofs.p7_22_1` | P7-22.1 | method-free | candidate | In a cell with free vertex positions whose pulling sub-tetrahedra all keep one orientation, sub-tetrahedra sharing an interior triangle lie on opposite sides, and those at a cell-face triangle on one side. |
| `CFDLean.JST1.Proofs.p7_22_2` | P7-22.2 | FVM | candidate | A mesh of general hexahedra, prisms and pyramids, split-oriented and conforming at the sub-tetrahedron level, averaged over its pulling splits, is valid and facet balanced. |
| `CFDLean.JST1.Proofs.p7_22_3` | P7-22.3 | FVM | candidate | Affine cells are split-oriented and centroid conformity implies sub-tetrahedron conformity, so the affine result P3-11.8 is a special case of P7-22.2. |
| `CFDLean.JST1.Proofs.p7_22_4` | P7-22.4 | FVM | candidate | A twisted cube (top face turned, cos θ = 3/5) is a valid trilinear hexahedron but has inverted pulling sub-tetrahedra; its one-cell mesh is not facet balanced and the boundary formula of β fails. |
| `CFDLean.JST1.Proofs.p8_23_1` | P8-23.1 | method-free | candidate | A valid trilinear hexahedron with its top face turned by about 106 degrees has a neighbour-fan (Kuhn) split that is not a triangulation of the cell. |
| `CFDLean.JST1.Proofs.p8_23_2` | P8-23.2 | FVM | candidate | A conforming 8-cell mesh of valid hexahedra has an interior vertex (13) whose averaged vertex normals sum to (0, 0, 7/30), not zero. |

## Discrete operators (94)

| Theorem | ID | Methods | Status | Summary |
|---|---|---|---|---|
| `CFDLean.Assembly.incidence_tail` | M3-I | FVM | accepted | Edge incidence is +1 at the tail node. |
| `CFDLean.Assembly.incidence_head` | M3-I | FVM | accepted | Edge incidence is −1 at the head node. |
| `CFDLean.Assembly.incidence_other` | M3-I | FVM | accepted | Edge incidence is 0 at a node that is neither tail nor head. |
| `CFDLean.Assembly.incidence_eq_one` | M3-I | FVM | accepted | Edge incidence is +1 exactly at the tail node. |
| `CFDLean.Assembly.incidence_eq_neg_one` | M3-I | FVM | accepted | Edge incidence is −1 exactly at the head node. |
| `CFDLean.Assembly.incidence_sum` | M3-I | FVM | accepted | The incidences of an edge sum to zero over all nodes. |
| `CFDLean.Assembly.incidence_smul` | M3-I | FVM | accepted | Incidence times a vector is the vector at the tail minus the vector at the head. |
| `CFDLean.Assembly.residual_outgoing` | M3-I | FVM | accepted | The assembled residual is outgoing tail transfers minus incoming head transfers plus owned boundary transfers. |
| `CFDLean.Assembly.global_balance` | M3-R | FVM | accepted | For arbitrary edge and boundary transfers the nodal residuals sum to the total boundary transfer. |
| `CFDLean.Assembly.residual_reverse` | M3-O | FVM | accepted | Reversing a set of edges and negating their transfers leaves every assembled residual unchanged. |
| `CFDLean.Assembly.residual_reindex` | M3-O | FVM | accepted | The assembled residual commutes with relabeling of nodes, edges and boundary pieces. |
| `CFDLean.Time.weighted_residual` | M5-L | FVM | pending | Node-weighted residuals sum to step differences across edges times edge transfers plus owner-weighted boundary transfers. |
| `CFDLean.Num.WMesh.nW_row_sum` | MC-N.P1-2.3 | FEM + FVM | candidate | For any dual of the P1 operator the edge normals at a node sum to −β_i, and β_i = 0 at a closed vertex. |
| `CFDLean.Num.WMesh.sbp_defect` | MC-N.P2-6.1 | FEM | candidate | For any dual the P1 operator satisfies c + cᵀ = B + 2E with E symmetric with zero row sums, and c has zero row sums and column sums β. |
| `CFDLean.Num.Simplex.median_defect_iff` | MC-N.P2-6.2 | FEM + FVM | candidate | On a nondegenerate simplex all off-diagonal SBP defect terms vanish iff the dual weights are the median weights. |
| `CFDLean.Num.quadratic_edge_expansion` | MC-N.P2-7.1 | FVM | candidate | For a quadratic field the weighted edge-difference sum is its first-order part plus V times the dissipation tensor contracted with the Hessian. |
| `CFDLean.Num.dissTensor_loewner` | MC-N.P2-7.2 | FVM | candidate | The edge dissipation tensor with full normals dominates the edge-projected one in the Loewner order, with equality iff the normals are parallel to the edges. |
| `CFDLean.Num.WMesh.dissTensor_trace` | MC-N.P2-7.3 | FVM | candidate | Under uniform edge scaling the dissipation tensor is s·G/(4V), its projected trace is ds/2, and the trace is bounded by (d/2)σ_max h. |
| `CFDLean.Num.WMesh.closed_of_facetPaired` | MC-N.P1-5.0a | FEM | candidate | A facet pairing at a vertex makes it a closed vertex of the P1 operator (zero boundary-matrix row). |
| `CFDLean.Num.WMesh.conforming_boundary` | MC-N.P2-6.3 | FEM | candidate | On a conforming mesh β and the boundary matrix B are sums over boundary facets, and a vertex on no boundary facet is closed. |
| `CFDLean.Num.WMesh.facetBalanced_boundary` | MC-N.P3-11.1 | FEM | candidate | Conforming meshes are facet balanced, and on facet-balanced meshes β and B are boundary-facet sums with interior vertices closed. |
| `CFDLean.Num.edgeForm_boundary_split` | MC-N.P2-6.4 | FEM + FVM | candidate | For row sums 0 and column sums β the edge form plus ½(B F + diag β F) equals the Galerkin form c F. |
| `CFDLean.Num.WMesh.faceRule_beta_B` | MC-N.P2-8.4 | FEM + FVM | candidate | A boundary face quadrature rule with the stated moments reproduces β and the boundary matrix B on a conforming mesh. |
| `CFDLean.Num.WMesh.galerkin_identity` | MC-N.P1-4.1 | FEM | candidate | The w-weighted sum of Galerkin residuals is minus the cell-weighted Frobenius product of the P1 gradient of w and the element fluxes. |
| `CFDLean.Num.WMesh.fvRes_eq_galerkinRes` | MC-N.P1-5.5 | FEM + FVM | candidate | With dual facet vectors m_T(g_k − g_i) the finite-volume residual of element fluxes equals the Galerkin residual. |
| `CFDLean.Num.WMesh.closed_mean_galerkin` | MC-N.P2-6.7 | FEM + FVM | candidate | At a closed vertex the mean edge flux through the dual normals equals the Galerkin form Σ_k c_ik F_k. |
| `CFDLean.Num.ofMeshData_closed` | MC-N.P1-5.0b | FEM + FVM | candidate | In a conforming tetrahedral median-dual mesh a vertex on no boundary face is closed for the induced P1 operator. |
| `CFDLean.Num.ofMeshData_fv_galerkin` | MC-N.P1-5.7 | FEM + FVM | candidate | On a median-dual tetrahedral mesh the finite-volume residual over the dual facets equals the Galerkin residual. |
| `CFDLean.Scalar.FiniteVolume.fluxDifference_sum_zero` | B0-C | FVM | accepted | On a finite periodic grid the interface flux differences of any two-point flux sum to zero. |
| `CFDLean.Scalar.FiniteVolume.rhs_sum_zero` | B0-C | FVM | accepted | For dx ≠ 0 the periodic first-order finite-volume right-hand side of any two-point flux sums to zero. |
| `CFDLean.Scalar.FiniteVolume.incrementalUpdate_totalVariation_le` | B1-H | FVM | accepted | Harten lemma: an incremental-form update with C, D ≥ 0 and C + D ≤ 1 at every interface does not increase the periodic total variation. |
| `CFDLean.Scalar.FiniteVolume.incrementalUpdate_bounds` | B1-X | FVM | accepted | An incremental-form update with C_i, D_{i-1} ≥ 0 and C_i + D_{i-1} ≤ 1 keeps every lower and upper bound of the old state at cell i. |
| `CFDLean.Scalar.FiniteVolume.boundedStates_convex` | B2-B | FVM | accepted | The set of cell functions with m ≤ u_j ≤ M in every cell is convex. |
| `CFDLean.Scalar.FiniteVolume.totalVariation_convexOn` | B2-B | FVM | accepted | The periodic total variation is a convex functional on every convex set of states. |
| `CFDLean.Scalar.FiniteVolume.minmod_minmodBounded` | B3-L | FVM | accepted | The minmod limiter has the sign of both differences and is not larger than either in absolute value. |
| `CFDLean.Scalar.FiniteVolume.zero_minmodBounded` | B3-L | FVM | accepted | The zero limiter (first-order reconstruction) satisfies the limiter certificate. |
| `CFDLean.Scalar.FiniteVolume.musclRhs_zero` | B3-R | FVM | accepted | With the zero limiter the MUSCL right-hand side is the first-order flux-difference right-hand side. |
| `CFDLean.Scalar.FiniteVolume.musclRhs_sum_zero` | B3-R | FVM | accepted | The periodic MUSCL right-hand side sums to zero for every two-point flux and every limiter. |
| `CFDLean.Scalar.FiniteVolume.musclRhs_constant` | B3-R | FVM | accepted | The MUSCL right-hand side is zero on a constant state, for every flux and every limiter. |
| `CFDLean.Scalar.FiniteVolume.leftState_mem` | B3-R | FVM | accepted | With a limiter in the minmod region the reconstructed left state of an interface keeps the bounds m ≤ u ≤ M. |
| `CFDLean.Scalar.FiniteVolume.rightState_mem` | B3-R | FVM | accepted | With a limiter in the minmod region the reconstructed right state of an interface keeps the bounds m ≤ u ≤ M. |
| `CFDLean.Scalar.FiniteVolume.muscl_incremental` | B3-I | FVM | accepted | For a monotone flux that is Lipschitz on bounded states and a limiter in the minmod region, the MUSCL Forward Euler step is an incremental update with 0 ≤ C ≤ (dt/dx)(3/2)KR and 0 ≤ D ≤ (dt/dx)(3/2)KL. |
| `CFDLean.JST1.Proofs.p1_2_3` | P1-2.3 | FEM + FVM | candidate | For any dual of the P1 operator the edge normals at a node sum to −β_i, and β_i = 0 at a closed vertex. |
| `CFDLean.JST1.Proofs.p1_4_1` | P1-4.1 | FEM | candidate | The w-weighted sum of Galerkin residuals is minus the cell-weighted Frobenius product of the P1 gradient of w and the element fluxes. |
| `CFDLean.JST1.Proofs.p1_5_0a` | P1-5.0a | FEM | candidate | A facet pairing at a vertex makes it a closed vertex of the P1 operator (zero boundary-matrix row). |
| `CFDLean.JST1.Proofs.p1_5_0b` | P1-5.0b | FEM + FVM | candidate | In a conforming tetrahedral median-dual mesh a vertex on no boundary face is closed for the induced P1 operator. |
| `CFDLean.JST1.Proofs.p1_5_5` | P1-5.5 | FEM + FVM | candidate | With dual facet vectors m_T(g_k − g_i) the finite-volume residual of element fluxes equals the Galerkin residual. |
| `CFDLean.JST1.Proofs.p1_5_7` | P1-5.7 | FEM + FVM | candidate | On a median-dual tetrahedral mesh the finite-volume residual over the dual facets equals the Galerkin residual. |
| `CFDLean.JST1.Proofs.p1_5_8` | P1-5.8 | FEM + FVM | candidate | On a valid triangle mesh the finite-volume residual over the median-dual segments equals the Galerkin residual. |
| `CFDLean.JST1.Proofs.p2_6_1` | P2-6.1 | FEM | candidate | For any dual the P1 operator satisfies c + cᵀ = B + 2E with E symmetric with zero row sums, and c has zero row sums and column sums β. |
| `CFDLean.JST1.Proofs.p2_6_2` | P2-6.2 | FEM + FVM | candidate | On a nondegenerate simplex all off-diagonal SBP defect terms vanish iff the dual weights are the median weights. |
| `CFDLean.JST1.Proofs.p2_6_3` | P2-6.3 | FEM | candidate | On a conforming mesh β and the boundary matrix B are sums over boundary facets, and a vertex on no boundary facet is closed. |
| `CFDLean.JST1.Proofs.p2_6_4` | P2-6.4 | FEM + FVM | candidate | For row sums 0 and column sums β the edge form plus ½(B F + diag β F) equals the Galerkin form c F. |
| `CFDLean.JST1.Proofs.p2_6_7` | P2-6.7 | FEM + FVM | candidate | At a closed vertex the mean edge flux through the dual normals equals the Galerkin form Σ_k c_ik F_k. |
| `CFDLean.JST1.Proofs.p2_7_1` | P2-7.1 | FVM | candidate | For a quadratic field the weighted edge-difference sum is its first-order part plus V times the dissipation tensor contracted with the Hessian. |
| `CFDLean.JST1.Proofs.p2_7_2` | P2-7.2 | FVM | candidate | The edge dissipation tensor with full normals dominates the edge-projected one in the Loewner order, with equality iff the normals are parallel to the edges. |
| `CFDLean.JST1.Proofs.p2_7_3` | P2-7.3 | FVM | candidate | Under uniform edge scaling the dissipation tensor is s·G/(4V), its projected trace is ds/2, and the trace is bounded by (d/2)σ_max h. |
| `CFDLean.JST1.Proofs.p2_7_4` | P2-7.4 | FVM | candidate | The edge dissipation coefficients satisfy Σ λ̂_ik \|e_ik\| ≤ d σ_max \|Ω\| (ordered pairs). |
| `CFDLean.JST1.Proofs.p2_8_4` | P2-8.4 | FEM + FVM | candidate | A boundary face quadrature rule with the stated moments reproduces β and the boundary matrix B on a conforming mesh. |
| `CFDLean.JST1.Proofs.p3_11_1` | P3-11.1 | FEM | candidate | Conforming meshes are facet balanced, and on facet-balanced meshes β and B are boundary-facet sums with interior vertices closed. |
| `CFDLean.JST1.Proofs.p4_15_6` | P4-15.6 | FVM | candidate | Linear model of the fourth-difference operator with the wall-crossing edges cut: every complex eigenvalue is real and non-negative. |
| `CFDLean.JST1.Proofs.p4_16_1` | P4-16.1 | FEM + FVM | candidate | The P1 interpolant of nodal fluxes takes the nodal values, has derivative Σ_b g_b F_b, reproduces affine fluxes, and its divergence gives the mean flux at a closed vertex. |
| `CFDLean.JST1.Proofs.p6_21_3` | P6-21.3 | FEM + FVM | candidate | At a closed vertex the mean flux equals Σ_T ω_T ∫_T φ_i ∇·F_h with F_h the P1 interpolant (the Galerkin form, with a real integral). |
| `CFDLean.Scalar.FiniteVolume.limitedSlope_noLimiter` | B3b-U | FVM | accepted | With the factor 1 (no limiter) the limited slope is the unlimited central slope (a + b)/2. |
| `CFDLean.Scalar.FiniteVolume.minmodBounded_iff_slopeBounded_one` | B3b-C | FVM | accepted | The minmod-region certificate of B3 is the θ-bounded certificate with θ = 1. |
| `CFDLean.Scalar.FiniteVolume.SlopeBounded.mono` | B3b-C | FVM | accepted | A θ-bounded slope function is θ'-bounded for every θ' ≥ θ. |
| `CFDLean.Scalar.FiniteVolume.SlopeBounded.nonneg` | B3b-C | FVM | accepted | A θ-bounded slope function exists only for θ ≥ 0. |
| `CFDLean.Scalar.FiniteVolume.not_slopeBounded_centralSlope` | B3b-C | FVM | accepted | The unlimited central slope is not θ-bounded for any θ. |
| `CFDLean.Scalar.FiniteVolume.limitedSlope_minmodFactor` | B3b-L | FVM | accepted | The minmod factor times the central slope is the classical minmod limited slope. |
| `CFDLean.Scalar.FiniteVolume.limitedSlope_mcFactor` | B3b-L | FVM | accepted | The MC factor times the central slope is the classical MC limited slope. |
| `CFDLean.Scalar.FiniteVolume.limitedSlope_superbeeFactor` | B3b-L | FVM | accepted | The superbee factor times the central slope is the classical superbee limited slope. |
| `CFDLean.Scalar.FiniteVolume.limitedSlope_vanLeerFactor` | B3b-L | FVM | accepted | The van Leer factor times the central slope is the classical van Leer limited slope. |
| `CFDLean.Scalar.FiniteVolume.limitedSlope_vanAlbadaFactor` | B3b-L | FVM | accepted | The van Albada factor times the central slope is the classical van Albada limited slope. |
| `CFDLean.Scalar.FiniteVolume.minmodFactor_mem` | B3b-L | FVM | accepted | The minmod limiter factor is between 0 and 1. |
| `CFDLean.Scalar.FiniteVolume.mcFactor_mem` | B3b-L | FVM | accepted | The MC limiter factor is between 0 and 1. |
| `CFDLean.Scalar.FiniteVolume.superbeeFactor_mem` | B3b-L | FVM | accepted | The superbee limiter factor is between 0 and 4/3. |
| `CFDLean.Scalar.FiniteVolume.vanLeerFactor_mem` | B3b-L | FVM | accepted | The van Leer limiter factor is between 0 and 1. |
| `CFDLean.Scalar.FiniteVolume.vanAlbadaFactor_mem` | B3b-L | FVM | accepted | The van Albada limiter factor is between 0 and 1. |
| `CFDLean.Scalar.FiniteVolume.minmodFactor_comm` | B3b-L | FVM | accepted | The minmod limiter factor is symmetric in the two differences. |
| `CFDLean.Scalar.FiniteVolume.mcFactor_comm` | B3b-L | FVM | accepted | The MC limiter factor is symmetric in the two differences. |
| `CFDLean.Scalar.FiniteVolume.superbeeFactor_comm` | B3b-L | FVM | accepted | The superbee limiter factor is symmetric in the two differences. |
| `CFDLean.Scalar.FiniteVolume.vanLeerFactor_comm` | B3b-L | FVM | accepted | The van Leer limiter factor is symmetric in the two differences. |
| `CFDLean.Scalar.FiniteVolume.vanAlbadaFactor_comm` | B3b-L | FVM | accepted | The van Albada limiter factor is symmetric in the two differences. |
| `CFDLean.Scalar.FiniteVolume.slopeBounded_minmodFactor` | B3b-L | FVM | accepted | The minmod limited slope is θ-bounded with θ = 1. |
| `CFDLean.Scalar.FiniteVolume.slopeBounded_mcFactor` | B3b-L | FVM | accepted | The MC limited slope is θ-bounded with θ = 2. |
| `CFDLean.Scalar.FiniteVolume.slopeBounded_superbeeFactor` | B3b-L | FVM | accepted | The superbee limited slope is θ-bounded with θ = 2. |
| `CFDLean.Scalar.FiniteVolume.slopeBounded_vanLeerFactor` | B3b-L | FVM | accepted | The van Leer limited slope is θ-bounded with θ = 2. |
| `CFDLean.Scalar.FiniteVolume.slopeBounded_vanAlbadaFactor` | B3b-L | FVM | accepted | The van Albada limited slope is θ-bounded with θ = 5/4. |
| `CFDLean.Scalar.FiniteVolume.muscl_incremental_bounded` | B3b-I | FVM | accepted | For a θ-bounded slope with θ ≤ 2 and a monotone flux that is Lipschitz on bounded states, the MUSCL Forward Euler step is an incremental update with 0 ≤ C ≤ (dt/dx)(1 + θ/2)KR and 0 ≤ D ≤ (dt/dx)(1 + θ/2)KL. |
| `CFDLean.FV1D.Nonuniform.leftState_affine` | FVN-A | FVM | pending | Local affine reconstruction exactness: if both differences next to cell i are the centroid distance times β and lim d d = d, the left state at face i is U i + (w i/2) β. |
| `CFDLean.FV1D.Nonuniform.rightState_prev_affine` | FVN-A | FVM | pending | Local affine reconstruction exactness: under the same hypotheses the right state at face prev i is U i − (w i/2) β. |
| `CFDLean.FV1D.Nonuniform.leftState_mem` | FVN-R | FVM | pending | For a θ-bounded slope and mesh ratio θ the rescaled MUSCL left state of every face keeps the bounds m ≤ u ≤ M. |
| `CFDLean.FV1D.Nonuniform.rightState_mem` | FVN-R | FVM | pending | For a θ-bounded slope and mesh ratio θ the rescaled MUSCL right state of every face keeps the bounds m ≤ u ≤ M. |
| `CFDLean.Burgers.Nonuniform.meshRatio_needed` | FVN-R | FVM | pending | Exact example on widths (1, 3, 1, 1): the mesh ratio holds for θ = 5/4, fails for θ = 2, and the van Leer, MC, superbee and unlimited left states leave [0, 6/5]. |

## Entropy framework (32)

| Theorem | ID | Methods | Status | Summary |
|---|---|---|---|---|
| `CFDLean.Num.antisymmetric_pairFlux` | MC-N.P1-2.1 | FVM | candidate | Antisymmetric pair fluxes are globally conservative, and their entropy production is half the sum of entropy-variable jumps times the fluxes. |
| `CFDLean.Num.entropyConservative_production` | MC-N.P1-2.2 | FVM | candidate | An entropy-conservative central pair flux produces only the boundary term Σ ψ_i·β_i. |
| `CFDLean.Num.WMesh.standardClosure_entropy` | MC-N.P2-6.5 | FVM | candidate | The standard boundary closure on a conforming mesh produces the lumped facet entropy flux plus a per-facet jump defect. |
| `CFDLean.Num.quadratureClosure_entropy` | MC-N.P2-8.1 | FVM | candidate | The quadrature boundary closure has an exact boundary entropy identity and conserves Σ_i b_i = Σ_q F*_q. |
| `CFDLean.Num.pair_production_integral` | MC-N.P3-13.1 | method-free | candidate | The pair entropy production is exactly the path integral of the derivative along the straight segment in entropy variables, with no remainder. |
| `CFDLean.JST1.Proofs.p1_1_5` | P1-1.5 | method-free | candidate | The second-difference flux λε2(ũ_i − ũ_k) produces at most −λ_γ ε2 λ [w]·[u] ≤ 0. |
| `CFDLean.JST1.Proofs.p1_2_1` | P1-2.1 | FVM | candidate | Antisymmetric pair fluxes are globally conservative, and their entropy production is half the sum of entropy-variable jumps times the fluxes. |
| `CFDLean.JST1.Proofs.p1_2_2` | P1-2.2 | FVM | candidate | An entropy-conservative central pair flux produces only the boundary term Σ ψ_i·β_i. |
| `CFDLean.JST1.Proofs.p2_6_5` | P2-6.5 | FVM | candidate | The standard boundary closure on a conforming mesh produces the lumped facet entropy flux plus a per-facet jump defect. |
| `CFDLean.JST1.Proofs.p2_6_6` | P2-6.6 | FVM | candidate | At a slip wall with the pressure flux the boundary closure defect [w]·[F*] takes both signs on admissible states. |
| `CFDLean.JST1.Proofs.p2_8_1` | P2-8.1 | FVM | candidate | The quadrature boundary closure has an exact boundary entropy identity and conserves Σ_i b_i = Σ_q F*_q. |
| `CFDLean.JST1.Proofs.p2_8_5` | P2-8.5 | FVM | candidate | At a slip wall with the pressure flux the boundary point term ψ̃·N − w̃·F* vanishes for every admissible state. |
| `CFDLean.JST1.Proofs.p2_8_6` | P2-8.6 | FVM | candidate | An entropy-stable far-field flux bounds the point term by the ghost entropy flux; Ismail-Roe with Rusanov dissipation λ ≥ 0 is such a flux. |
| `CFDLean.JST1.Proofs.p2_10_2` | P2-10.2 | FVM | candidate | v^η is the gradient of η0, v^η·R = w(û)·(R_ρ, R_m, R_E − R_k), and the exact semi-discrete entropy rate follows. |
| `CFDLean.JST1.Proofs.p3_13_1` | P3-13.1 | method-free | candidate | The pair entropy production is exactly the path integral of the derivative along the straight segment in entropy variables, with no remainder. |
| `CFDLean.JST1.Proofs.p3_13_2` | P3-13.2 | method-free | candidate | For Euler with \|v·E\| < c\|E\| the pair term production takes both signs for arbitrarily small admissible jumps. |
| `CFDLean.JST1.Proofs.p3_14_2` | P3-14.2 | FVM | candidate | With slip and no-slip wall points and entropy-stable far-field points the boundary term B is at most the sum of ghost entropy fluxes. |
| `CFDLean.Scalar.EntropyConservative.entropyStable` | B4-C | method-free | accepted | An entropy-conservative two-point flux is entropy stable. |
| `CFDLean.Scalar.FiniteVolume.entropyFlux_constant` | B4-Q | FVM | accepted | On equal states the numerical entropy flux of a consistent flux is v f − ψ. |
| `CFDLean.Scalar.FiniteVolume.cell_entropy_identity` | B4-I | FVM | accepted | Cell entropy identity: v_i L_i + (Q_i − Q_{i−1})/dx is the sum of the two interface entropy defects over 2 dx. |
| `CFDLean.Scalar.FiniteVolume.cell_entropy_inequality` | B4-I | FVM | accepted | For an entropy-stable flux and dx > 0: v_i L_i ≤ −(Q_i − Q_{i−1})/dx in every cell. |
| `CFDLean.Scalar.FiniteVolume.cell_entropy_equality` | B4-I | FVM | accepted | For an entropy-conservative flux: v_i L_i = −(Q_i − Q_{i−1})/dx in every cell. |
| `CFDLean.Scalar.FiniteVolume.entropy_production_nonpos` | B4-G | FVM | accepted | For an entropy-stable flux and dx > 0 the total entropy production Σ v_i L_i on a periodic grid is nonpositive. |
| `CFDLean.Scalar.FiniteVolume.entropy_production_zero` | B4-G | FVM | accepted | For an entropy-conservative flux the total entropy production on a periodic grid is zero. |
| `CFDLean.Burgers.entropyPotential_eq` | B4-B | method-free | accepted | For Burgers and the square entropy the potential u³/6 is v f − q with v = u, f = u²/2, q = u³/3. |
| `CFDLean.Burgers.EntropyConservativeFlux.consistent` | B4-B | FVM | accepted | The flux (a² + ab + b²)/6 is consistent with the Burgers flux. |
| `CFDLean.Burgers.EntropyConservativeFlux.entropyConservative` | B4-B | FVM | accepted | The flux (a² + ab + b²)/6 is entropy conservative for the square entropy of Burgers. |
| `CFDLean.Burgers.Rusanov.eval_eq_entropyConservative_sub` | B4-B | FVM | accepted | The Burgers Rusanov flux is the entropy-conservative flux minus (α/2 − (b − a)/12)(b − a). |
| `CFDLean.Burgers.Rusanov.entropyStable` | B4-B | FVM | accepted | The Burgers Rusanov flux is entropy stable for the square entropy. |
| `CFDLean.Burgers.Rusanov.cell_entropy_inequality` | B4-S | FVM | accepted | Cell entropy inequality of the Burgers Rusanov operator for the square entropy, dx > 0. |
| `CFDLean.Burgers.Rusanov.energy_production_nonpos` | B4-S | FVM | accepted | The Burgers Rusanov operator does not produce energy: Σ u_i L_i(u) ≤ 0 for dx > 0. |
| `CFDLean.JST1.Proofs.p4_15_5` | P4-15.5 | FVM | candidate | Linear wall-normal profile on a geometric mesh: L_k − L_s = (r−1)(ũ_k − ũ_s), and the fourth-difference wall flux produces ε4(r−1)λ[w]·[ũ] ≥ 0. |

## Physics models (93)

| Theorem | ID | Methods | Status | Summary |
|---|---|---|---|---|
| `CFDLean.pressure_toConservative` | M1-1 | method-free | accepted | For γ ≠ 1 and ρ ≠ 0 the pressure of a converted primitive state is its prescribed pressure. |
| `CFDLean.primitive_roundTrip` | M1-1 | method-free | accepted | For γ ≠ 1 and ρ ≠ 0 converting a primitive state to conservative and back returns it. |
| `CFDLean.conservative_roundTrip` | M1-2 | method-free | accepted | For γ ≠ 1 and ρ ≠ 0 converting a conservative state to primitive and back returns it. |
| `CFDLean.primitive_admissible_toConservative` | M1-3 | method-free | accepted | For γ > 1 an admissible primitive state converts to an admissible conservative state. |
| `CFDLean.conservative_admissible_toPrimitive` | M1-3 | method-free | accepted | An admissible conservative state converts to an admissible primitive state. |
| `CFDLean.admissible_iff_internalEnergy_pos` | M1-4 | method-free | accepted | For γ > 1 a conservative state is admissible iff ρ > 0 and its energy exceeds the kinetic energy Q(m)/(2ρ). |
| `CFDLean.admissible_exists` | M1-5 | method-free | accepted | For γ > 1 the admissible conservative domain is nonempty in every dimension. |
| `CFDLean.physicalFlux_add` | M1-6 | method-free | accepted | The physical Euler flux is additive in the oriented area vector. |
| `CFDLean.physicalFlux_mul` | M1-6 | method-free | accepted | The physical Euler flux scales linearly with the oriented area vector. |
| `CFDLean.physicalFlux_reverse` | M1-6 | method-free | accepted | Reversing the oriented area vector negates the physical Euler flux. |
| `CFDLean.physicalFlux_zero` | M1-6 | method-free | accepted | The physical Euler flux through a zero area vector is zero. |
| `CFDLean.PhysicalJacobian.hasFDerivAt_coordinateFlux` | M2-J | method-free | accepted | For nonzero density the explicit physical Jacobian is the Fréchet derivative of the fixed-normal Euler flux in state coordinates. |
| `CFDLean.PhysicalJacobian.isOpen_admissible` | M2-J | method-free | accepted | The admissible set is open in state coordinates. |
| `CFDLean.PhysicalJacobian.hasFDerivAt_integratedFlux` | M2-J | method-free | accepted | For nonzero density and area the derivative of the area-integrated flux is the area times the Jacobian at the unit normal. |
| `CFDLean.PhysicalJacobian.jacobian_action` | M2-J | method-free | accepted | The physical Jacobian applied to a perturbation is given by the explicit formula in velocity, normal speed, pressure perturbation and total enthalpy. |
| `CFDLean.PhysicalJacobian.hasFDerivAt_zeroArea` | M2-J | method-free | accepted | The flux through a zero area vector has zero derivative at every state. |
| `CFDLean.Roe.root_pos` | M2-A | method-free | accepted | The square-root density used by the Roe average is positive for positive density. |
| `CFDLean.Roe.root_sum_pos` | M2-A | method-free | accepted | The sum of the two square-root densities is positive for positive densities. |
| `CFDLean.Roe.weight_pos` | M2-A | method-free | accepted | Each Roe averaging weight is positive for positive densities. |
| `CFDLean.Roe.weight_lt_one` | M2-A | method-free | accepted | Each Roe averaging weight is smaller than one for positive densities. |
| `CFDLean.Roe.weight_sum` | M2-A | method-free | accepted | The two Roe averaging weights sum to one. |
| `CFDLean.Roe.averages_swap` | M2-A | method-free | accepted | The Roe-averaged velocity, enthalpy and sound-speed square are symmetric in the two states. |
| `CFDLean.Roe.variance_identity` | M2-A | method-free | accepted | The averaged sound-speed square is the weighted mean of the endpoint sound-speed squares plus a velocity-jump variance term. |
| `CFDLean.Roe.soundSquare_pos` | M2-A | method-free | accepted | For γ > 1 and admissible states the averaged sound-speed square is positive. |
| `CFDLean.Roe.soundSpeed_pos` | M2-A | method-free | accepted | For γ > 1 and admissible states the averaged sound speed is positive. |
| `CFDLean.Roe.soundSpeed_sq` | M2-A | method-free | accepted | For γ > 1 and admissible states the averaged sound speed squares to the averaged sound-speed square. |
| `CFDLean.Roe.parameter_state` | M2-R | method-free | accepted | The state recovered from Roe's parameter vector is the original state. |
| `CFDLean.Roe.parameter_flux` | M2-R | method-free | accepted | The flux recovered from Roe's parameter vector is the physical coordinate flux. |
| `CFDLean.Roe.hasFDerivAt_parameterState` | M2-R | method-free | accepted | B is the Fréchet derivative of the parameter-to-state map. |
| `CFDLean.Roe.hasFDerivAt_parameterFlux` | M2-R | method-free | accepted | C is the Fréchet derivative of the parameter-to-flux map. |
| `CFDLean.Roe.state_midpoint_jump` | M2-R | method-free | accepted | The state jump is B at the parameter midpoint applied to the parameter jump. |
| `CFDLean.Roe.flux_midpoint_jump` | M2-R | method-free | accepted | The flux jump is C at the parameter midpoint applied to the parameter jump. |
| `CFDLean.Roe.midpoint_pos` | M2-R | method-free | accepted | The parameter midpoint of two positive-density states has positive first component. |
| `CFDLean.Roe.B_bijective` | M2-R | method-free | accepted | B is bijective for γ ≠ 0 and nonzero first parameter component. |
| `CFDLean.Roe.inverseB_B` | M2-R | method-free | accepted | The explicit inverse of B is a left inverse. |
| `CFDLean.Roe.B_inverseB` | M2-R | method-free | accepted | The explicit inverse of B is a right inverse. |
| `CFDLean.Roe.operator_B` | M2-R | method-free | accepted | The Roe operator at the parameter velocity and enthalpy composed with B equals C. |
| `CFDLean.Roe.roeMatrix_B` | M2-R | method-free | accepted | The Roe matrix composed with B at the parameter midpoint equals C at the midpoint. |
| `CFDLean.Roe.roeMatrix_CB_inverse` | M2-R | method-free | accepted | For admissible states the Roe matrix is C composed with the inverse of B at the parameter midpoint. |
| `CFDLean.Roe.secant_identity` | M2-R | method-free | accepted | For admissible states the Roe matrix maps the state jump to the flux jump (Roe property U). |
| `CFDLean.Roe.integrated_secant` | M2-R | method-free | accepted | For admissible states and nonzero area the area-scaled Roe matrix at the unit normal maps the state jump to the integrated flux jump. |
| `CFDLean.Roe.roeMatrix_continuousOn` | M2-L | method-free | accepted | The Roe matrix is jointly continuous on pairs of admissible states. |
| `CFDLean.Roe.roeMatrix_diagonal` | M2-L | method-free | accepted | At two equal positive-density states the Roe matrix is the physical Jacobian. |
| `CFDLean.Roe.hasFDerivAt_diagonal` | M2-L | method-free | accepted | At an admissible state the equal-state Roe matrix is the derivative of the physical flux. |
| `CFDLean.Roe.roeMatrix_equal_state_limit` | M2-L | method-free | accepted | The Roe matrix tends to the physical Jacobian as both states tend to the same admissible state. |
| `CFDLean.Roe.Spectral.sound_parameters` | M2-E | method-free | accepted | For admissible states the averaged sound speed is positive and its square is (γ−1)(H̄ − Q(ū)/2). |
| `CFDLean.Roe.Spectral.roe_cubic` | M2-E | method-free | accepted | The shifted Roe matrix satisfies the cubic identity (Ã − q̄)³ = c̄²(Ã − q̄) for a unit normal. |
| `CFDLean.Roe.Spectral.roe_eigenvectors` | M2-E | method-free | accepted | The acoustic, contact and shear vectors are eigenvectors of the Roe matrix with speeds q̄ ∓ c̄ and q̄. |
| `CFDLean.Roe.Spectral.roe_projector_algebra` | M2-E | method-free | accepted | The three Roe spectral projectors are idempotent and have zero mutual products. |
| `CFDLean.Roe.Spectral.roe_projector_sum` | M2-E | method-free | accepted | The three Roe spectral projectors sum to the identity. |
| `CFDLean.Roe.Spectral.roe_projector_ranges` | M2-E | method-free | accepted | Each Roe projector's range is the eigenspace of its wave speed. |
| `CFDLean.Roe.Spectral.roe_dimensions` | M2-E | method-free | accepted | The Roe eigenspaces have dimensions 1, 3 and 1. |
| `CFDLean.Roe.Spectral.roe_projector_ranks` | M2-E | method-free | accepted | The Roe projectors have ranks 1, 3 and 1. |
| `CFDLean.Roe.Spectral.roe_complete_basis` | M2-E | method-free | accepted | The Roe matrix has a complete basis of five eigenvectors. |
| `CFDLean.Roe.Spectral.roe_spectral_decomposition` | M2-E | method-free | accepted | The Roe matrix is the speed-weighted sum of its three spectral projectors. |
| `CFDLean.Roe.Spectral.roe_convective_tangent_span` | M2-E | method-free | accepted | The contact vector and the shear vectors of any tangent basis span the convective eigenspace. |
| `CFDLean.Roe.Spectral.tangent_dimension` | M2-E | method-free | accepted | The plane tangent to a unit normal has dimension 2. |
| `CFDLean.Roe.Spectral.exists_tangent_basis` | M2-E | method-free | accepted | The plane tangent to a unit normal has a basis. |
| `CFDLean.Roe.Spectral.roe_absolute_basis` | M2-D | method-free | accepted | The Roe dissipation operator equals R diag(\|speeds\|) R⁻¹ for every complete eigenbasis R. |
| `CFDLean.Roe.Spectral.roe_absolute_eigen` | M2-D | method-free | accepted | Every eigenvector of the Roe matrix with eigenvalue μ is an eigenvector of the dissipation operator with eigenvalue \|μ\|. |
| `CFDLean.Roe.Spectral.roe_matrix_reverse` | M2-O | method-free | accepted | Reversing the normal negates the Roe matrix. |
| `CFDLean.Roe.Spectral.roe_shift_reverse` | M2-O | method-free | accepted | Reversing the normal negates the shifted Roe matrix. |
| `CFDLean.Roe.Spectral.roe_projector_reverse` | M2-O | method-free | accepted | Reversing the normal exchanges the two acoustic projectors. |
| `CFDLean.Roe.Spectral.roe_speed_reverse` | M2-O | method-free | accepted | Reversing the normal negates the Roe wave speeds and reverses their order. |
| `CFDLean.Roe.Spectral.roe_absolute_reverse` | M2-O | method-free | accepted | The Roe dissipation operator is invariant under normal reversal. |
| `CFDLean.Roe.Spectral.roe_swap` | M2-O | method-free | accepted | The shifted Roe matrix, projectors and dissipation are symmetric in the two states. |
| `CFDLean.Boundary.wall_pressure_pos` | M4-W | method-free | accepted | An admissible state has positive pressure. |
| `CFDLean.JST1.Proofs.p1_1_0` | P1-1.0 | method-free | candidate | At admissible Euler states the entropy variables w are the derivative of the entropy U = −ρs/(γ−1). |
| `CFDLean.JST1.Proofs.p1_1_1` | P1-1.1 | method-free | candidate | Pointwise bounds of the 2×2 thermodynamic pencil of the ideal gas, with their equality cases. |
| `CFDLean.JST1.Proofs.p1_1_2` | P1-1.2 | method-free | candidate | For admissible states λ_γ[w]·[u] ≤ [w]·[ũ] ≤ Λ_γ[w]·[u], with ũ the enthalpy state (energy replaced by ρH). |
| `CFDLean.JST1.Proofs.p1_1_3` | P1-1.3 | method-free | candidate | [w]·[u] ≥ 0 for admissible Euler states (convexity of the entropy). |
| `CFDLean.JST1.Proofs.p1_1_4` | P1-1.4 | method-free | candidate | 3/4 < λ_γ < 1 < Λ_γ; λ_γ is strictly decreasing in γ > 1, tends to 1 as γ → 1⁺ and to 3/4 as γ → ∞, and 0.8258 < λ_1.4 < 0.8259. |
| `CFDLean.JST1.Proofs.p1_1_6` | P1-1.6 | method-free | candidate | λ_γ and Λ_γ are the best constants for two states: no larger lower and no smaller upper constant holds. |
| `CFDLean.JST1.Proofs.p1_2_0` | P1-2.0 | method-free | candidate | For the Euler equations the entropy flux potential ψ = w·F − Q equals ρv. |
| `CFDLean.JST1.Proofs.p1_4_0` | P1-4.0 | method-free | candidate | The momentum and energy entropy variables are v/(RT) and −1/(RT), and the viscous flux of their gradient is the Navier-Stokes flux. |
| `CFDLean.JST1.Proofs.p1_4_2` | P1-4.2 | method-free | candidate | The viscous matrix K(w̄) is positive semidefinite and linear (d ≤ 3, Stokes hypothesis, μ, κ ≥ 0, R > 0, w̄_E < 0). |
| `CFDLean.JST1.Proofs.p1_4_3b` | P1-4.3b | method-free | candidate | Admissible Euler states have negative energy entropy variable w_E < 0. |
| `CFDLean.JST1.Proofs.p1_4_4` | P1-4.4 | method-free | candidate | The viscous matrix is symmetric: G : K H = H : K G. |
| `CFDLean.JST1.Proofs.p2_8_0` | P2-8.0 | method-free | candidate | Every w with w_E < 0 is the entropy-variable image of exactly one admissible Euler state (entropy projection). |
| `CFDLean.JST1.Proofs.p2_9_3` | P2-9.3 | method-free | candidate | The Navier-Stokes K(w̄) with μ > 0 and the momentum projector satisfy the sharpness hypotheses for every nonzero normal. |
| `CFDLean.JST1.Proofs.p2_9_4` | P2-9.4 | method-free | candidate | No-slip and isothermal conditions are linear and constant in entropy variables: v = 0 ⟺ w_m = 0, T = T_w ⟺ w_E = −1/(R T_w). |
| `CFDLean.JST1.Proofs.p2_10_1` | P2-10.1 | method-free | candidate | The SST map T has kernel span{e_E + e_k, e_ω}, and the entropy η0 is constant along it. |
| `CFDLean.JST1.Proofs.p2_10_3` | P2-10.3 | method-free | candidate | The SST admissible set is convex, η0 is convex on it, and its gradient is monotone with equality iff T U_1 = T U_2. |
| `CFDLean.JST1.Proofs.p2_10_4` | P2-10.4 | method-free | candidate | Pointwise SST entropy production: the Π formula, Q ≥ 0, Π ≤ 0 if P_k ≤ μ_t Q, and the remainder bound. |
| `CFDLean.JST1.Proofs.p2_10_6` | P2-10.6 | method-free | candidate | The production limiter P_k = max(0, min(P*, c_l ε)) with ε, P* ≥ 0 satisfies (M4): P_k − ε ≤ P*. |
| `CFDLean.JST1.Proofs.p2_8_0b` | P2-8.0b | method-free | candidate | Convex combinations of entropy variables with w_E < 0 keep w_E < 0, so the projected boundary state exists. |
| `CFDLean.JST1.Proofs.p4_17_1` | P4-17.1 | method-free | candidate | Continuous SST entropy balance: ∂_t η0 + ∇·(v η0 + G) = Π for smooth solutions, with G = −v^η·F^v = θκ∇T (− θD_k∇k). |
| `CFDLean.JST1.Proofs.p4_18_1` | P4-18.1 | method-free | candidate | The Euler entropy −ρs/(γ−1) has a positive definite Hessian at admissible states. |
| `CFDLean.JST1.Proofs.p4_18_2` | P4-18.2 | method-free | candidate | The SST coupled entropy η0 has a positive semidefinite Hessian with null space span{e_E + e_k, e_ω}. |
| `CFDLean.JST1.Proofs.p5_20_1` | P5-20.1 | method-free | candidate | The paper's Euler state and M1's conservative state correspond one to one (toState, ofState inverse; density, momentum, energy agree). |
| `CFDLean.JST1.Proofs.p5_20_2` | P5-20.2 | method-free | candidate | The paper's pressure, admissibility, velocity and primitive-to-conservative map equal M1's. |
| `CFDLean.JST1.Proofs.p5_20_3` | P5-20.3 | method-free | candidate | The paper's Euler flux on a vector y equals M1's integrated physical flux on the area vector y, for every state. |
| `CFDLean.JST1.Proofs.p5_20_4` | P5-20.4 | method-free | candidate | The paper's entropy −ρs/(γ−1) and its entropy variables written in M1's primitive variables (ρ, v, p). |

## Schemes (105)

| Theorem | ID | Methods | Status | Summary |
|---|---|---|---|---|
| `CFDLean.Roe.numericalFlux_consistency` | M2-F1 | method-free | accepted | The Roe numerical flux of two equal states is the physical flux. |
| `CFDLean.Roe.numericalFlux_reverse` | M2-F2 | method-free | accepted | Swapping the states and reversing the area vector negates the Roe numerical flux. |
| `CFDLean.Roe.numericalFlux_zero` | M2-F3 | method-free | accepted | The Roe numerical flux through a zero area vector is zero. |
| `CFDLean.Roe.numericalFlux_scale` | M2-F3 | method-free | accepted | The Roe numerical flux scales linearly with nonnegative multiples of the area vector. |
| `CFDLean.Roe.numericalFlux_upwind_left` | M2-F4 | method-free | accepted | If the Roe normal speed is at least the averaged sound speed, the Roe flux is the left physical flux (sonic case included). |
| `CFDLean.Roe.numericalFlux_upwind_right` | M2-F4 | method-free | accepted | If the Roe normal speed is at most minus the averaged sound speed, the Roe flux is the right physical flux (sonic case included). |
| `CFDLean.Roe.witness_intermediate_coordinates` | M2-C | method-free | accepted | The Roe intermediate state of the receding-state witness has the stated exact coordinates. |
| `CFDLean.Roe.positivity_counterexample` | M2-C | method-free | accepted | Two admissible states with positive averaged sound-speed square have a Roe intermediate state with negative density. |
| `CFDLean.Assembly.roe_global_balance` | M3-R | FVM | accepted | With Roe edge transfers the nodal residuals sum to the total boundary transfer. |
| `CFDLean.Assembly.outwardTransfer_eq` | M3-O | FVM | accepted | The outward Roe transfer of an edge at a node is the incidence times the edge Roe transfer. |
| `CFDLean.Assembly.roe_residual_reverse` | M3-O | FVM | accepted | Reversing a set of edges, with swapped endpoints and reversed area vectors, leaves every Roe residual unchanged. |
| `CFDLean.Assembly.roe_residual_reindex` | M3-O | FVM | accepted | The Roe residual commutes with relabeling of nodes, edges and boundary pieces with transported data. |
| `CFDLean.Assembly.roeTransfer_zero` | M3-O | FVM | accepted | An edge with zero area vector has zero Roe transfer. |
| `CFDLean.MedianDual.MeshData.roe_boundary_balance` | M3-G | FVM | accepted | On a concrete median-dual mesh the Roe residuals sum to the total boundary transfer. |
| `CFDLean.Assembly.constant_state_residual` | M3-C | FVM | accepted | For a common state with physical boundary transfers the residual is the physical flux through the metric defect. |
| `CFDLean.Assembly.constant_state_closed` | M3-C | FVM | accepted | A common state with physical boundary transfers has zero residual at every node with zero metric defect. |
| `CFDLean.MedianDual.MeshData.constant_state` | M3-C | FVM | accepted | On a conforming median-dual mesh a common state with physical boundary transfers has zero residual. |
| `CFDLean.Boundary.patchKind_coherent` | M4-B | FVM | accepted | The boundary kind is the same on all records of one primal face. |
| `CFDLean.Boundary.patchExterior_coherent` | M4-B | FVM | accepted | The prescribed exterior state is the same on all records of one primal face. |
| `CFDLean.Boundary.patchTransfer_wall` | M4-B | FVM | accepted | On a slip-wall record the patch transfer is the wall transfer at the owner state. |
| `CFDLean.Boundary.patchTransfer_symmetry` | M4-B | FVM | accepted | On an inviscid symmetry record the patch transfer is the wall transfer at the owner state. |
| `CFDLean.Boundary.patchTransfer_prescribed` | M4-B | FVM | accepted | On a prescribed-exterior record the patch transfer is the Roe transfer between owner and exterior states. |
| `CFDLean.Boundary.wall_mass` | M4-W | FVM | accepted | The wall transfer has zero mass component. |
| `CFDLean.Boundary.wall_energy` | M4-W | FVM | accepted | The wall transfer has zero energy component. |
| `CFDLean.Boundary.wall_momentum` | M4-W | FVM | accepted | The wall transfer's momentum is the owner pressure times the area vector. |
| `CFDLean.Boundary.wall_zero` | M4-W | FVM | accepted | The wall transfer through a zero area vector is zero. |
| `CFDLean.Boundary.wall_add` | M4-W | FVM | accepted | The wall transfer is additive in the area vector. |
| `CFDLean.Boundary.wall_smul` | M4-W | FVM | accepted | The wall transfer is homogeneous in the area vector. |
| `CFDLean.Boundary.wall_reverse` | M4-W | FVM | accepted | Reversing the area vector negates the wall transfer. |
| `CFDLean.Boundary.wall_eq_physical_iff` | M4-W | FVM | accepted | The wall transfer equals the physical flux iff the normal momentum is zero. |
| `CFDLean.Boundary.wall_eq_physical_iff_normalVelocity` | M4-W | FVM | accepted | For positive density and nonzero area the wall transfer equals the physical flux iff the normal velocity is zero. |
| `CFDLean.Boundary.prescribed_consistency` | M4-P | FVM | accepted | The prescribed-exterior Roe transfer with exterior state equal to the owner state is the physical flux. |
| `CFDLean.Boundary.prescribed_zero` | M4-P | FVM | accepted | The prescribed-exterior transfer through a zero area vector is zero. |
| `CFDLean.Boundary.prescribed_scale` | M4-P | FVM | accepted | The prescribed-exterior transfer scales with nonnegative multiples of the area vector. |
| `CFDLean.Boundary.prescribed_reverse` | M4-P | FVM | accepted | Swapping owner and exterior states and reversing the area negates the prescribed-exterior transfer. |
| `CFDLean.Boundary.prescribed_upwind_owner` | M4-P | FVM | accepted | If the Roe normal speed is at least the sound speed the prescribed-exterior transfer is the owner's physical flux. |
| `CFDLean.Boundary.prescribed_upwind_exterior` | M4-P | FVM | accepted | If the Roe normal speed is at most minus the sound speed the prescribed-exterior transfer is the exterior physical flux. |
| `CFDLean.Boundary.stationary_global_balance` | M4-R | FVM | accepted | With the selected boundary transfers the nodal residuals sum to the total boundary transfer. |
| `CFDLean.Boundary.stationary_mixed_balance` | M4-R | FVM | accepted | The total residual splits into prescribed-exterior Roe transfers and wall/symmetry transfers. |
| `CFDLean.Boundary.stationary_mass_balance` | M4-R | FVM | accepted | The total mass residual is the mass transfer through prescribed-exterior faces only. |
| `CFDLean.Boundary.stationary_energy_balance` | M4-R | FVM | accepted | The total energy residual is the energy transfer through prescribed-exterior faces only. |
| `CFDLean.Boundary.stationary_momentum_balance` | M4-R | FVM | accepted | The total momentum residual is the prescribed-exterior momentum transfer plus the wall/symmetry pressure forces. |
| `CFDLean.Boundary.meshResidual_eq` | M4-R | FVM | accepted | The concrete mesh residual is the M3 Roe residual with the selected patch transfers. |
| `CFDLean.Boundary.mesh_global_balance` | M4-R | FVM | accepted | On a concrete mesh the nodal residuals sum to the total patch transfer. |
| `CFDLean.Boundary.constructed_transfer_reindex` | M4-O | FVM | accepted | The constructed boundary transfers commute with relabeling, including boundary kinds and exterior data. |
| `CFDLean.Boundary.stationary_residual_reindex` | M4-O | FVM | accepted | The stationary residual commutes with relabeling of nodes, edges and boundary records. |
| `CFDLean.Boundary.mesh_residual_reindex` | M4-O | FVM | accepted | The concrete mesh residual commutes with relabeling of nodes, edges and boundary records. |
| `CFDLean.Boundary.transfer_compatible` | M4-C | FVM | accepted | With wall tangency or a matching exterior state the boundary transfer is the physical transfer. |
| `CFDLean.Boundary.stationary_common_defect` | M4-C | FVM | accepted | For a common state with compatible boundaries the residual is the physical flux through the metric defect. |
| `CFDLean.Boundary.stationary_common_closed` | M4-C | FVM | accepted | For a common state with compatible boundaries the residual vanishes at every node with zero metric defect. |
| `CFDLean.Boundary.stationary_common_correction` | M4-C | FVM | accepted | For a common state the residual is the defect flux plus the owned differences between constructed and physical transfers. |
| `CFDLean.Boundary.mesh_constant_state` | M4-C | FVM | accepted | On a conforming mesh a common admissible state with tangent walls and matching exterior data has zero residual. |
| `CFDLean.Boundary.mesh_common_correction` | M4-C | FVM | accepted | On a conforming mesh a common state's residual is the owned sum of patch transfer minus physical transfer. |
| `CFDLean.Time.mesh_residual_unused` | M5-V | FVM | pending | The mesh residual vanishes at unused nodes. |
| `CFDLean.Time.Controls.hot_cold_residual` | M5-C | FVM | pending | An incompatible hot/cold boundary control has the stated exact nonzero residual. |
| `CFDLean.Num.dissipativePairFlux_conservation` | MC-N.P1-2.6 | FVM | candidate | Central flux plus scalar second/fourth-difference dissipation with symmetric coefficients is antisymmetric and globally conservative. |
| `CFDLean.Num.dissipativePairFlux_freeStream` | MC-N.P1-2.7 | FVM | candidate | A uniform state with matching boundary data has zero residual for the dissipative pair-flux scheme. |
| `CFDLean.Num.WMesh.standardClosure_linear` | MC-N.P2-6.5b | FEM + FVM | candidate | For linear fluxes the standard boundary closure equals ½(B + diag β)F with weights (d+3):1. |
| `CFDLean.Num.quadratureClosure_freeStream` | MC-N.P2-8.2 | FVM | candidate | With a uniform state, physical boundary fluxes and matching quadrature normals the quadrature closure has zero residual. |
| `CFDLean.Num.quadratureClosure_linear` | MC-N.P2-8.3 | FVM | candidate | For linear fluxes the quadrature closure is ½(F_i β_i + Σ_k F_k Σ_q φ_qi φ_qk N_q). |
| `CFDLean.Burgers.Rusanov.consistent` | B0-F | FVM | accepted | The Burgers Rusanov (local Lax-Friedrichs) flux with wave speed max(\|uL\|, \|uR\|) equals the physical flux u²/2 on equal states. |
| `CFDLean.Scalar.FiniteVolume.rhs_constant` | B0-K | FVM | accepted | A consistent two-point flux gives a zero periodic finite-volume right-hand side on a constant state. |
| `CFDLean.Burgers.Schemes.RusanovForwardEuler.semidiscrete_constant` | B0-S | FVM | accepted | The Burgers Rusanov semidiscretization on ZMod N is zero on a constant state (composition of B0-F and B0-K). |
| `CFDLean.Burgers.Schemes.RusanovForwardEuler.semidiscrete_sum_zero` | B0-S | FVM | accepted | For dx ≠ 0 the Burgers Rusanov semidiscretization on ZMod N sums to zero (instance of B0-C). |
| `CFDLean.Burgers.Rusanov.monotone` | B1-M | FVM | accepted | The Burgers Rusanov flux is nondecreasing in the left state and nonincreasing in the right state. |
| `CFDLean.Burgers.Rusanov.abs_mean_le_waveSpeed` | B1-I | FVM | accepted | The mean of two states is bounded in absolute value by the Rusanov wave speed max(\|a\|, \|b\|). |
| `CFDLean.Burgers.Rusanov.step_eq_incrementalUpdate` | B1-I | FVM | accepted | The Burgers Rusanov Forward Euler step is in incremental form with C = (dt/dx)(a − ū)/2 and D = (dt/dx)(a + ū)/2. |
| `CFDLean.Burgers.Rusanov.waveSpeed_le_of_bounds` | B2-B | FVM | accepted | For states between m and M the Rusanov wave speed is at most max(\|m\|, \|M\|). |
| `CFDLean.Burgers.Rusanov.eval_lipschitz_left` | B3-K | FVM | accepted | For states with absolute value at most A the Burgers Rusanov flux is Lipschitz in the left state with constant 2A. |
| `CFDLean.Burgers.Rusanov.eval_lipschitz_right` | B3-K | FVM | accepted | For states with absolute value at most A the Burgers Rusanov flux is Lipschitz in the right state with constant 2A. |
| `CFDLean.Burgers.Rusanov.lipschitzOnBounds` | B3-K | FVM | accepted | Lipschitz certificate of the Burgers Rusanov flux on states between m and M with constants 2 max(\|m\|, \|M\|). |
| `CFDLean.JST1.Proofs.p1_2_5` | P1-2.5 | method-free | candidate | The Ismail-Roe flux is entropy conservative (Tadmor condition), symmetric, linear in the normal and consistent. |
| `CFDLean.JST1.Proofs.p1_2_6` | P1-2.6 | FVM | candidate | Central flux plus scalar second/fourth-difference dissipation with symmetric coefficients is antisymmetric and globally conservative. |
| `CFDLean.JST1.Proofs.p1_2_7` | P1-2.7 | FVM | candidate | A uniform state with matching boundary data has zero residual for the dissipative pair-flux scheme. |
| `CFDLean.JST1.Proofs.p1_3_1` | P1-3.1 | FVM | candidate | Under the first part of assumption (A) the mean over the cell splits of the nodal spectral sum Λ_i is Λ_i of the assembled coefficients. |
| `CFDLean.JST1.Proofs.p1_3_2` | P1-3.2 | FVM | candidate | The means over the cell splits of the linear nodal sums (Laplacian, sensor sums, counts) are exact, without (A). |
| `CFDLean.JST1.Proofs.p1_3_3` | P1-3.3 | FVM | candidate | Under (A) the mean over the splits of the JST pair dissipation is the dissipation with coefficient π^a Φ λ̂. |
| `CFDLean.JST1.Proofs.p1_3_4` | P1-3.4 | FVM | candidate | With share 1 (simplex mesh) the split-mean dissipation coefficient is the JST coefficient of eq. (jst). |
| `CFDLean.JST1.Proofs.p1_4_3` | P1-4.3 | FEM | candidate | The Galerkin viscous operator with one frozen K(w̄_T) per cell dissipates entropy: Σ w_i·R_i = −Σ ω\|T\| G:KG ≤ 0. |
| `CFDLean.JST1.Proofs.p2_6_5b` | P2-6.5b | FEM + FVM | candidate | For linear fluxes the standard boundary closure equals ½(B + diag β)F with weights (d+3):1. |
| `CFDLean.JST1.Proofs.p2_8_2` | P2-8.2 | FVM | candidate | With a uniform state, physical boundary fluxes and matching quadrature normals the quadrature closure has zero residual. |
| `CFDLean.JST1.Proofs.p2_8_3` | P2-8.3 | FVM | candidate | For linear fluxes the quadrature closure is ½(F_i β_i + Σ_k F_k Σ_q φ_qi φ_qk N_q). |
| `CFDLean.JST1.Proofs.p2_9_0` | P2-9.0 | FEM | candidate | Element balance: the viscous and wall terms of a cell produce −D^gal_T + Π^w_T plus the discrete wall flux. |
| `CFDLean.JST1.Proofs.p2_9_1` | P2-9.1 | FEM | candidate | Π^w_T ≤ D^gal_T/c for c > 0, so for c ≥ 1 the element term D^gal_T − Π^w_T is at least (1 − 1/c) D^gal_T ≥ 0. |
| `CFDLean.JST1.Proofs.p2_9_2` | P2-9.2 | FEM | candidate | c ≥ 1 is sharp for one wall element: for c < 1 there are nodal values with D^gal_T − Π^w_T < 0. |
| `CFDLean.JST1.Proofs.p2_10_5` | P2-10.5 | FVM | candidate | The matched k transport is conservative, reproduces uniform inflow k, and gives X_i ≤ 0 at wall nodes (M5). |
| `CFDLean.JST1.Proofs.p2_10_7` | P2-10.7 | FEM | candidate | The Galerkin dissipation with μ + μ_t splits into a laminar part and the turbulent part D_t, both nonnegative. |
| `CFDLean.JST1.Proofs.p2_10_8` | P2-10.8 | FEM + FVM | candidate | SST entropy bound: under (M1)-(M5) and (W_t) the semi-discrete entropy rate of the hat scheme obeys the bound of thm:sst. |
| `CFDLean.JST1.Proofs.p2_9_2b` | P2-9.2b | FEM | candidate | Sharpness with the Navier-Stokes K(w̄_T) and no-slip projector: for c < 1 some admissible nodal values give D^gal_T − Π^w_T < 0. |
| `CFDLean.JST1.Proofs.p2_10_8b` | P2-10.8b | FEM | candidate | On one simplex 0 ≤ D_t ≤ D^gal, and (W_t) holds without wall faces or for c ≥ 1 with D_t ≤ (1 − 1/c) D^gal. |
| `CFDLean.JST1.Proofs.p2_10_8c` | P2-10.8c | FEM + FVM | candidate | For differentiable SST trajectories the entropy rate d/dt Σ V_i η0(U_i) exists and obeys the bound of P2-10.8. |
| `CFDLean.JST1.Proofs.p3_14_1` | P3-14.1 | FEM + FVM | candidate | Entropy balance of the complete scheme: rate = B + Π² + Π⁴ − Σ ω_T(D^gal_T − Π^w_T) + wall flux, with Π² ≤ 0 and element terms ≥ 0 for c ≥ 1. |
| `CFDLean.JST1.Proofs.p3_14_3` | P3-14.3 | FEM + FVM | candidate | SST form of the complete scheme: the entropy rate exists and is bounded as in P3-14.1 with the SST terms of P2-10.8. |
| `CFDLean.JST1.Proofs.p4_15_1` | P4-15.1 | FVM | candidate | Wall-normal model of the fourth difference at a weak wall: L_k = (r−1)h f'(y_k) + ½(1+r²)h² f''(y_k) + O(h³) for a C³ profile, first order if r ≠ 1. |
| `CFDLean.JST1.Proofs.p4_15_2` | P4-15.2 | FVM | candidate | One-node balance of the fourth-difference wall term with the wall penalty: the unique wall slip −ϱL⁰/(1+ϱ) is opposite to the flow. |
| `CFDLean.JST1.Proofs.p4_15_3` | P4-15.3 | FVM | candidate | The momentum rows of the second-difference flux of the scheme are λε2(ρv_s − ρv_k), a difference without a power of h. |
| `CFDLean.JST1.Proofs.p4_15_4` | P4-15.4 | FEM + FVM | candidate | Cutting ε2 = ε4 = 0 on the wall-crossing edges removes only those dissipation terms, keeps the hypotheses of the complete scheme, and splits Π² and Π⁴ exactly. |
| `CFDLean.JST1.Proofs.p4_16_3` | P4-16.3 | FVM | candidate | ε2 ≤ 6κ2, ε4 ≤ 9κ4, and the weak effect of the scalar dissipation is at most d(6κ2 + 18n_Eκ4) Φmax σmax h \|Ω\| Gφ Gu. |
| `CFDLean.JST1.Proofs.p5_19_2` | P5-19.2 | method-free | candidate | The admissible Euler states form an open set, and the Ismail-Roe flux is Cⁿ for every n on admissible × admissible, diagonal included. |
| `CFDLean.JST1.Proofs.p5_19_3` | P5-19.3 | method-free | candidate | At every admissible state the Ismail-Roe flux differs from the mean of the Euler fluxes by at most C\|y\|\|u_k − u_i\|² near the diagonal, one constant for all vectors y. |
| `CFDLean.Burgers.fv1d_step_eq` | FV1D-B | FVM | accepted | The shared periodic Rusanov update agrees with the assembled B0 Forward Euler step in every cell. |
| `CFDLean.Euler1D.face_consistent` | FV1D-F | FVM | accepted | On equal admissible states the Euler numerical flux equals the M1 positive-unit-face flux. |
| `CFDLean.Euler1D.step_constant` | FV1D-K | FVM | accepted | One periodic Euler step preserves each admissible constant state. |
| `CFDLean.Euler1D.component_balance` | FV1D-C | FVM | accepted | One common step conserves the discrete integrals of density, x-momentum and total energy. |
| `CFDLean.Euler1D.step_admissible` | FVP-P | FVM | accepted | The local old-state CFL bound preserves strict M1 admissibility for one periodic Euler update. |

## Time (105)

| Theorem | ID | Methods | Status | Summary |
|---|---|---|---|---|
| `CFDLean.Time.euler_coordinates` | M5-U | method-free | pending | The explicit Euler step subtracts (τ/v) times the residual in state coordinates. |
| `CFDLean.Time.euler_zero_step` | M5-U | method-free | pending | A zero time step leaves the state unchanged. |
| `CFDLean.Time.euler_zero_residual` | M5-U | method-free | pending | A zero residual leaves the state unchanged. |
| `CFDLean.Time.euler_amount` | M5-U | method-free | pending | For nonzero volume the step changes the amount v·U by −τ times the residual. |
| `CFDLean.Time.mesh_point_amount` | M5-U | FVM | pending | At a used node the mesh step changes the dual-volume amount by −τ times the old-state residual. |
| `CFDLean.Time.mesh_zero_step` | M5-U | FVM | pending | Zero time steps leave every nodal state unchanged. |
| `CFDLean.Time.mesh_step_used` | M5-V | FVM | pending | At a used node the mesh step is the explicit Euler update with its dual volume. |
| `CFDLean.Time.mesh_step_unused` | M5-V | FVM | pending | At an unused node the mesh step holds the state. |
| `CFDLean.Time.mesh_amount_used` | M5-V | FVM | pending | The total amount equals the amount summed over used nodes only. |
| `CFDLean.Time.Controls.unused_all` | M5-V | FVM | pending | In the unused-node control the unused node has zero volume, zero residual and a held state. |
| `CFDLean.Time.mesh_amount_change` | M5-B | FVM | pending | The step changes the total amount by minus the step-weighted sum of nodal residuals. |
| `CFDLean.Time.mesh_common_balance` | M5-B | FVM | pending | With a common step on used nodes the total amount changes by −dt times the total patch transfer. |
| `CFDLean.Time.mesh_common_balance_physical` | M5-B | FVM | pending | For admissible nodal and exterior states and a common nonnegative step the total amount changes by −dt times the total patch transfer. |
| `CFDLean.Time.mesh_component_balance` | M5-B | FVM | pending | With a common step each amount component changes by −dt times its total boundary transfer. |
| `CFDLean.Time.mesh_mass_balance` | M5-B | FVM | pending | With a common step the total mass changes only by the prescribed-exterior mass transfer. |
| `CFDLean.Time.mesh_energy_balance` | M5-B | FVM | pending | With a common step the total energy changes only by the prescribed-exterior energy transfer. |
| `CFDLean.Time.mesh_momentum_balance` | M5-B | FVM | pending | With a common step the total momentum changes by the prescribed-exterior transfer and the wall/symmetry pressure forces. |
| `CFDLean.Time.mesh_traction_mass` | M5-B | FVM | pending | With only wall/symmetry boundaries a common step conserves total mass. |
| `CFDLean.Time.mesh_traction_energy` | M5-B | FVM | pending | With only wall/symmetry boundaries a common step conserves total energy. |
| `CFDLean.Time.mesh_local_balance` | M5-L | FVM | pending | With local steps the total amount changes by the edge step-difference defect plus owner-weighted boundary transfers. |
| `CFDLean.Time.mesh_local_balance_physical` | M5-L | FVM | pending | For admissible data and nonnegative local steps the same edge-defect balance holds with the actual Roe transfers. |
| `CFDLean.Time.Controls.local_amount_change` | M5-L | FVM | pending | In the standard control unequal local steps change the total amount by an exact nonzero vector. |
| `CFDLean.Time.Controls.local_nonconservation` | M5-L | FVM | pending | In the standard control unequal local steps do not conserve the total amount. |
| `CFDLean.Time.Controls.local_updated_admissible` | M5-L | FVM | pending | In the standard local-step control every updated state is admissible. |
| `CFDLean.Time.mesh_common_state` | M5-C | FVM | pending | On a conforming mesh a compatible common admissible state is preserved by any nonnegative steps. |
| `CFDLean.Time.Controls.standard_mixed_common` | M5-C | FVM | pending | On the standard tetrahedron with mixed boundary kinds a compatible moving state is preserved. |
| `CFDLean.Time.Controls.standard_wall_rest` | M5-C | FVM | pending | On the all-wall standard tetrahedron a state at rest is preserved. |
| `CFDLean.Time.Controls.oblique_rest` | M5-C | FVM | pending | On the oblique all-symmetry tetrahedron a state at rest is preserved. |
| `CFDLean.Time.Controls.two_cell_common` | M5-C | FVM | pending | On the two-cell mesh with mixed boundaries a compatible moving state is preserved. |
| `CFDLean.Time.Controls.negative_density_update` | M5-C | FVM | pending | A large step in the hot/cold control produces the stated update with negative density. |
| `CFDLean.Time.Controls.negative_update_not_admissible` | M5-C | FVM | pending | The large-step hot/cold update is not admissible. |
| `CFDLean.Time.held_reindex` | M5-O | method-free | pending | The held explicit step commutes with relabeling of nodes and transported data. |
| `CFDLean.Time.amount_reindex` | M5-O | method-free | pending | The total amount is invariant under relabeling of nodes. |
| `CFDLean.Time.mesh_step_reindex` | M5-O | FVM | pending | The mesh step commutes with relabeling of nodes, edges and boundary records with fully transported residual data. |
| `CFDLean.Time.Controls.transported_nonconstant` | M5-O | FVM | pending | The relabeled two-cell step with nonconstant transported data equals the original step. |
| `CFDLean.Time.Controls.transported_fields_nonconstant` | M5-O | FVM | pending | In the relabeling control the volumes, steps, states and exterior data differ between the swapped nodes and faces. |
| `CFDLean.Time.ForwardEuler.step_zero_rhs` | B0-T | method-free | accepted | A Forward Euler step with a zero right-hand side at the state returns the state. |
| `CFDLean.Time.ForwardEuler.step_constant` | B0-T | method-free | accepted | A Forward Euler step keeps a constant state when the right-hand side is zero on it. |
| `CFDLean.Time.ForwardEuler.step_sum` | B0-T | method-free | accepted | A Forward Euler step keeps the total sum when the right-hand side sums to zero. |
| `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_preserves_constant` | B0-S | FVM | accepted | The Burgers Rusanov Forward Euler step on ZMod N keeps every constant state, for every dx and dt. |
| `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_preserves_sum` | B0-S | FVM | accepted | For dx ≠ 0 the Burgers Rusanov Forward Euler step on ZMod N keeps the total sum of the cell averages. |
| `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_preserves_integral` | B0-S | FVM | accepted | For dx ≠ 0 the Burgers Rusanov Forward Euler step on ZMod N keeps the discrete integral dx · Σ u. |
| `CFDLean.Burgers.Rusanov.step_totalVariation_le` | B1-S | FVM | accepted | For dx > 0, dt ≥ 0 and dt · a_i ≤ dx at every interface the Burgers Rusanov Forward Euler step does not increase the total variation, on any periodic grid. |
| `CFDLean.Burgers.Rusanov.step_bounds` | B1-S | FVM | accepted | For dx > 0, dt ≥ 0 and 2 · dt · a_i ≤ dx at every interface the Burgers Rusanov Forward Euler step keeps every lower and upper bound of the old state. |
| `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_totalVariation_le` | B1-S | FVM | accepted | Total variation under the per-interface CFL hypothesis for the assembled scheme on ZMod N. |
| `CFDLean.Burgers.Schemes.RusanovForwardEuler.step_bounds` | B1-S | FVM | accepted | Bounds under the per-interface CFL 1/2 hypothesis for the assembled scheme on ZMod N. |
| `CFDLean.Time.SSP.ssprk2_forwardEuler` | B2-R | method-free | accepted | SSPRK2 over a Forward Euler map is Heun's method: u + (dt/2)(L(u) + L(u + dt L(u))). |
| `CFDLean.Time.SSP.ssprk2_mem` | B2-C | method-free | accepted | SSPRK2 keeps every convex set that the one-step map keeps. |
| `CFDLean.Time.SSP.ssprk3_mem` | B2-C | method-free | accepted | SSPRK3 keeps every convex set that the one-step map keeps. |
| `CFDLean.Time.SSP.ssprk2_le` | B2-C | method-free | accepted | SSPRK2 does not increase a functional that is convex on an invariant set and not increased by the one-step map. |
| `CFDLean.Time.SSP.ssprk3_le` | B2-C | method-free | accepted | SSPRK3 does not increase a functional that is convex on an invariant set and not increased by the one-step map. |
| `CFDLean.Time.SSP.iterate_mem` | B2-N | method-free | accepted | A one-step map that keeps a set keeps it for every number of steps. |
| `CFDLean.Time.SSP.iterate_le` | B2-N | method-free | accepted | A functional not increased by one step on an invariant set is not increased by n steps. |
| `CFDLean.Time.SSP.ssprk2_fixed` | B2-L | method-free | accepted | A fixed point of the one-step map is a fixed point of SSPRK2. |
| `CFDLean.Time.SSP.ssprk3_fixed` | B2-L | method-free | accepted | A fixed point of the one-step map is a fixed point of SSPRK3. |
| `CFDLean.Time.SSP.ssprk2_linear` | B2-L | method-free | accepted | A linear functional kept by the one-step map is kept by SSPRK2. |
| `CFDLean.Time.SSP.ssprk3_linear` | B2-L | method-free | accepted | A linear functional kept by the one-step map is kept by SSPRK3. |
| `CFDLean.Burgers.Rusanov.eulerStep_mem` | B2-B | FVM | accepted | For dx > 0, dt ≥ 0 and 2 · dt · max(\|m\|, \|M\|) ≤ dx the Burgers Rusanov Forward Euler map keeps the bounds m ≤ u ≤ M. |
| `CFDLean.Burgers.Rusanov.eulerStep_totalVariation_le` | B2-B | FVM | accepted | Under the same hypothesis the Forward Euler map does not increase the total variation of a state with m ≤ u ≤ M. |
| `CFDLean.Burgers.Rusanov.eulerStep_iterate_stable` | B2-S | FVM | accepted | After n Burgers Rusanov Forward Euler steps with one dt from the initial bounds, the bounds hold and the total variation is not larger. |
| `CFDLean.Burgers.Rusanov.ssprk2Step_iterate_stable` | B2-S | FVM | accepted | The same multi-step bounds and total-variation result for n SSPRK2 steps. |
| `CFDLean.Burgers.Rusanov.ssprk3Step_iterate_stable` | B2-S | FVM | accepted | The same multi-step bounds and total-variation result for n SSPRK3 steps. |
| `CFDLean.Burgers.Rusanov.ssprk2Step_sum` | B2-S | FVM | accepted | For dx ≠ 0 one Burgers Rusanov SSPRK2 step keeps the total sum of the cell values. |
| `CFDLean.Burgers.Rusanov.ssprk3Step_sum` | B2-S | FVM | accepted | For dx ≠ 0 one Burgers Rusanov SSPRK3 step keeps the total sum of the cell values. |
| `CFDLean.Burgers.Rusanov.ssprk2Step_constant` | B2-S | FVM | accepted | One Burgers Rusanov SSPRK2 step keeps every constant state. |
| `CFDLean.Burgers.Rusanov.ssprk3Step_constant` | B2-S | FVM | accepted | One Burgers Rusanov SSPRK3 step keeps every constant state. |
| `CFDLean.Scalar.FiniteVolume.muscl_step_totalVariation_le` | B3-T | FVM | accepted | Under dt · (3/2)(KL + KR) ≤ dx one MUSCL Forward Euler step does not increase the total variation of a state with m ≤ u ≤ M. |
| `CFDLean.Scalar.FiniteVolume.muscl_step_mem` | B3-T | FVM | accepted | Under dt · (3/2)(KL + KR) ≤ dx one MUSCL Forward Euler step keeps the bounds m ≤ u ≤ M. |
| `CFDLean.Burgers.Rusanov.musclEulerStep_mem` | B3-S | FVM | accepted | Under 6 · dt · max(\|m\|, \|M\|) ≤ dx the MUSCL-Rusanov Forward Euler step keeps the bounds, for every limiter in the minmod region. |
| `CFDLean.Burgers.Rusanov.musclEulerStep_totalVariation_le` | B3-S | FVM | accepted | Under 6 · dt · max(\|m\|, \|M\|) ≤ dx the MUSCL-Rusanov Forward Euler step does not increase the total variation. |
| `CFDLean.Burgers.Rusanov.musclEulerStep_iterate_stable` | B3-S | FVM | accepted | Bounds and total variation after n MUSCL-Rusanov Forward Euler steps with one dt from the initial bounds. |
| `CFDLean.Burgers.Rusanov.musclSsprk2Step_iterate_stable` | B3-S | FVM | accepted | Bounds and total variation after n MUSCL-Rusanov SSPRK2 steps. |
| `CFDLean.Burgers.Rusanov.musclSsprk3Step_iterate_stable` | B3-S | FVM | accepted | Bounds and total variation after n MUSCL-Rusanov SSPRK3 steps. |
| `CFDLean.Burgers.Rusanov.musclEulerStep_sum` | B3-S | FVM | accepted | For dx ≠ 0 one MUSCL-Rusanov Forward Euler step keeps the total sum of the cell values. |
| `CFDLean.Burgers.Rusanov.musclSsprk2Step_sum` | B3-S | FVM | accepted | For dx ≠ 0 one MUSCL-Rusanov SSPRK2 step keeps the total sum of the cell values. |
| `CFDLean.Burgers.Rusanov.musclSsprk3Step_sum` | B3-S | FVM | accepted | For dx ≠ 0 one MUSCL-Rusanov SSPRK3 step keeps the total sum of the cell values. |
| `CFDLean.Burgers.Rusanov.musclEulerStep_constant` | B3-S | FVM | accepted | One MUSCL-Rusanov Forward Euler step keeps every constant state. |
| `CFDLean.Burgers.Rusanov.musclSsprk2Step_constant` | B3-S | FVM | accepted | One MUSCL-Rusanov SSPRK2 step keeps every constant state. |
| `CFDLean.Burgers.Rusanov.musclSsprk3Step_constant` | B3-S | FVM | accepted | One MUSCL-Rusanov SSPRK3 step keeps every constant state. |
| `CFDLean.Scalar.FiniteVolume.muscl_step_totalVariation_le_bounded` | B3b-T | FVM | accepted | Under dt · (1 + θ/2)(KL + KR) ≤ dx one MUSCL Forward Euler step with a θ-bounded slope (θ ≤ 2) does not increase the total variation. |
| `CFDLean.Scalar.FiniteVolume.muscl_step_mem_bounded` | B3b-T | FVM | accepted | Under dt · (1 + θ/2)(KL + KR) ≤ dx one MUSCL Forward Euler step with a θ-bounded slope (θ ≤ 2) keeps the bounds m ≤ u ≤ M. |
| `CFDLean.Burgers.Rusanov.musclEulerStep_mem_bounded` | B3b-S | FVM | accepted | Under (4 + 2θ) · dt · max(\|m\|, \|M\|) ≤ dx the MUSCL-Rusanov Forward Euler step with a θ-bounded slope (θ ≤ 2) keeps the bounds. |
| `CFDLean.Burgers.Rusanov.musclEulerStep_totalVariation_le_bounded` | B3b-S | FVM | accepted | Under (4 + 2θ) · dt · max(\|m\|, \|M\|) ≤ dx the MUSCL-Rusanov Forward Euler step with a θ-bounded slope (θ ≤ 2) does not increase the total variation. |
| `CFDLean.Burgers.Rusanov.musclEulerStep_iterate_stable_bounded` | B3b-S | FVM | accepted | Bounds and total variation after n MUSCL-Rusanov Forward Euler steps with a θ-bounded slope (θ ≤ 2). |
| `CFDLean.Burgers.Rusanov.musclSsprk2Step_iterate_stable_bounded` | B3b-S | FVM | accepted | Bounds and total variation after n MUSCL-Rusanov SSPRK2 steps with a θ-bounded slope (θ ≤ 2). |
| `CFDLean.Burgers.Rusanov.musclSsprk3Step_iterate_stable_bounded` | B3b-S | FVM | accepted | Bounds and total variation after n MUSCL-Rusanov SSPRK3 steps with a θ-bounded slope (θ ≤ 2). |
| `CFDLean.Burgers.Rusanov.musclSsprk3Step_minmodFactor_iterate_stable` | B3b-S | FVM | accepted | MUSCL-Rusanov SSPRK3 with the minmod limiter: bounds and total variation after n steps under 6 · dt · max(\|m\|, \|M\|) ≤ dx. |
| `CFDLean.Burgers.Rusanov.musclSsprk3Step_mc_iterate_stable` | B3b-S | FVM | accepted | MUSCL-Rusanov SSPRK3 with the MC limiter: bounds and total variation after n steps under 8 · dt · max(\|m\|, \|M\|) ≤ dx. |
| `CFDLean.Burgers.Rusanov.musclSsprk3Step_superbee_iterate_stable` | B3b-S | FVM | accepted | MUSCL-Rusanov SSPRK3 with the superbee limiter: bounds and total variation after n steps under 8 · dt · max(\|m\|, \|M\|) ≤ dx. |
| `CFDLean.Burgers.Rusanov.musclSsprk3Step_vanLeer_iterate_stable` | B3b-S | FVM | accepted | MUSCL-Rusanov SSPRK3 with the van Leer limiter: bounds and total variation after n steps under 8 · dt · max(\|m\|, \|M\|) ≤ dx. |
| `CFDLean.Burgers.Rusanov.musclSsprk3Step_vanAlbada_iterate_stable` | B3b-S | FVM | accepted | MUSCL-Rusanov SSPRK3 with the van Albada limiter: bounds and total variation after n steps under 13/2 · dt · max(\|m\|, \|M\|) ≤ dx. |
| `CFDLean.Burgers.Rusanov.stepData_mem` | B3b-N | FVM | accepted | The four-cell state (0, 0, 1, 1) is between 0 and 1. |
| `CFDLean.Burgers.Rusanov.unlimited_step_leaves_bounds` | B3b-N | FVM | accepted | The unlimited MUSCL-Rusanov scheme is not bound preserving: from (0, 0, 1, 1) with dx = 1, dt = 1/10 one Forward Euler step gives 167/160 in cell 3. |
| `CFDLean.FV1D.Nonuniform.firstOrderStep_uniform` | FVN-U | FVM | pending | On the uniform mesh with width dx and the FV1D Rusanov face, the non-uniform first-order step is the FV1D step in every cell. |
| `CFDLean.Burgers.Nonuniform.musclStep_uniform` | FVN-U | FVM | pending | On the uniform mesh the Burgers MUSCL step with rescaled differences is the B3 MUSCL-Rusanov Forward Euler step, for every slope function. |
| `CFDLean.FV1D.Nonuniform.firstOrderStep_constant` | FVN-K | FVM | pending | On a non-uniform mesh the first-order step keeps every constant state, for every two-point flux. |
| `CFDLean.FV1D.Nonuniform.musclStep_constant` | FVN-K | FVM | pending | On a non-uniform mesh the MUSCL step keeps every constant state, for every two-point flux and every limiter with lim 0 0 = 0. |
| `CFDLean.FV1D.Nonuniform.update_weighted_sum` | FVN-C | FVM | pending | The flux-form update on a non-uniform periodic mesh keeps the width-weighted sum of the states, for every face-flux function. |
| `CFDLean.Burgers.Nonuniform.firstOrderStep_mem` | FVN-B | FVM | pending | Under the cell CFL dt (a(prev i) + a i) ≤ w i the first-order Burgers step on a non-uniform mesh keeps the bounds m ≤ u ≤ M. |
| `CFDLean.Burgers.Nonuniform.firstOrderStep_totalVariation_le` | FVN-B | FVM | pending | Under the face CFL dt · a i ≤ min(w i, w(next i)) the first-order Burgers step on a non-uniform mesh does not increase the total variation. |
| `CFDLean.FV1D.Nonuniform.musclStep_mem` | FVN-M | FVM | pending | For a monotone flux with the Lipschitz certificate, a θ-bounded slope and mesh ratio θ, the scalar MUSCL step keeps the bounds under the local cell CFL condition. |
| `CFDLean.FV1D.Nonuniform.musclStep_totalVariation_le` | FVN-M | FVM | pending | For a monotone flux with the Lipschitz certificate, a θ-bounded slope and mesh ratio θ, the scalar MUSCL step does not increase the total variation under the local face CFL condition. |
| `CFDLean.Burgers.Nonuniform.musclStep_iterate_stable` | FVN-MB | FVM | pending | Under 8 · dt · max(\|m\|, \|M\|) ≤ w i, a θ-bounded slope and mesh ratio θ, n Burgers MUSCL Forward Euler steps keep the bounds and do not increase the total variation. |
| `CFDLean.Burgers.Nonuniform.musclSsprk2Step_iterate_stable` | FVN-MB | FVM | pending | The same non-uniform-mesh bounds and total-variation result for n Burgers MUSCL SSPRK2 steps. |
| `CFDLean.Burgers.Nonuniform.musclSsprk3Step_iterate_stable` | FVN-MB | FVM | pending | The same non-uniform-mesh bounds and total-variation result for n Burgers MUSCL SSPRK3 steps. |

## Execution (79)

| Theorem | ID | Methods | Status | Summary |
|---|---|---|---|---|
| `CFDLean.Exec.eulerStepArray_size` | E0-K | FVM | accepted | The kernel Euler step returns an array of the same size. |
| `CFDLean.Exec.axpby_size` | E0-K | FVM | accepted | The kernel linear combination returns an array of the smaller of the two sizes. |
| `CFDLean.Exec.ssprk3StepArray_size` | E0-K | FVM | accepted | The kernel SSPRK3 step returns an array of the same size. |
| `CFDLean.Exec.run_size` | E0-K | FVM | accepted | Running a size-preserving step k times preserves the size. |
| `CFDLean.Exec.rusanov_eq` | E0-R | FVM | accepted | With real arithmetic the kernel flux is the Burgers Rusanov flux. |
| `CFDLean.Exec.represents_iff_eq_ofFn` | E0-R | FVM | accepted | An array represents a cell function on Fin n exactly when it is Array.ofFn of that function. |
| `CFDLean.Exec.eulerStepArray_refines` | E0-S | FVM | accepted | If an array represents u, the kernel Euler step of the array represents the Rusanov Forward Euler step of u on the periodic grid Fin n. |
| `CFDLean.Exec.axpby_refines` | E0-S | FVM | accepted | The kernel linear combination of two arrays represents the pointwise linear combination of the two cell functions. |
| `CFDLean.Exec.ssprk2StepArray_refines` | E0-S | FVM | accepted | The kernel SSPRK2 step represents the Rusanov SSPRK2 step. |
| `CFDLean.Exec.ssprk3StepArray_refines` | E0-S | FVM | accepted | The kernel SSPRK3 step represents the Rusanov SSPRK3 step. |
| `CFDLean.Exec.run_refines` | E0-N | FVM | accepted | k applications of a kernel step that refines T represent the k-fold iterate of T. |
| `CFDLean.Exec.sumArray_eq` | E0-D | FVM | accepted | The kernel sum diagnostic of an array that represents u is the sum of the cell values of u. |
| `CFDLean.Exec.totalVariationArray_eq` | E0-D | FVM | accepted | The kernel total-variation diagnostic of an array that represents u is the periodic total variation of u. |
| `CFDLean.Exec.run_eulerStepArray_bounds` | E0-T | FVM | accepted | With real arithmetic, dx > 0, dt ≥ 0 and 2 · dt · max(\|m\|, \|M\|) ≤ dx, every entry stays in [m, M] after k kernel Euler steps. |
| `CFDLean.Exec.run_ssprk3StepArray_bounds` | E0-T | FVM | accepted | The same bounds result after k kernel SSPRK3 steps. |
| `CFDLean.Exec.run_eulerStepArray_sum` | E0-T | FVM | accepted | With real arithmetic and dx ≠ 0, k kernel Euler steps keep the sum of the entries. |
| `CFDLean.Exec.run_ssprk3StepArray_sum` | E0-T | FVM | accepted | With real arithmetic and dx ≠ 0, k kernel SSPRK3 steps keep the sum of the entries. |
| `CFDLean.Exec.run_eulerStepArray_totalVariation_le` | E0-T | FVM | accepted | Under the hypotheses of the bounds result, k kernel Euler steps do not increase the total variation of the entries. |
| `CFDLean.Exec.run_ssprk3StepArray_totalVariation_le` | E0-T | FVM | accepted | Under the hypotheses of the bounds result, k kernel SSPRK3 steps do not increase the total variation of the entries. |
| `CFDLean.Exec.instScalarReal_standard` | E0-K | FVM | accepted | The real instance of the kernel arithmetic is the standard real arithmetic of Mathlib, field by field. |
| `CFDLean.Exec.musclEulerStepArray_size` | E0b-K | FVM | accepted | The kernel MUSCL Euler step returns an array of the same size. |
| `CFDLean.Exec.musclSsprk2StepArray_size` | E0b-K | FVM | accepted | The kernel MUSCL SSPRK2 step returns an array of the same size. |
| `CFDLean.Exec.musclSsprk3StepArray_size` | E0b-K | FVM | accepted | The kernel MUSCL SSPRK3 step returns an array of the same size. |
| `CFDLean.Exec.min_eq` | E0b-L | FVM | accepted | With real arithmetic the kernel min, written −max(−a, −b), is the minimum. |
| `CFDLean.Exec.minmod_eq` | E0b-L | FVM | accepted | With real arithmetic the comparison-free kernel limiter max 0 (min a b) + min 0 (max a b) is the minmod limiter. |
| `CFDLean.Exec.musclEulerStepArray_refines` | E0b-S | FVM | accepted | If an array represents u, the kernel MUSCL Euler step of the array represents the MUSCL-minmod-Rusanov Forward Euler step of u on the periodic grid Fin n. |
| `CFDLean.Exec.musclSsprk2StepArray_refines` | E0b-S | FVM | accepted | The kernel MUSCL SSPRK2 step represents the MUSCL-Rusanov SSPRK2 step. |
| `CFDLean.Exec.musclSsprk3StepArray_refines` | E0b-S | FVM | accepted | The kernel MUSCL SSPRK3 step represents the MUSCL-Rusanov SSPRK3 step. |
| `CFDLean.Exec.run_musclEulerStepArray_bounds` | E0b-T | FVM | accepted | With real arithmetic, dx > 0, dt ≥ 0 and 6 · dt · max(\|m\|, \|M\|) ≤ dx, every entry stays in [m, M] after k kernel MUSCL Euler steps. |
| `CFDLean.Exec.run_musclSsprk3StepArray_bounds` | E0b-T | FVM | accepted | The same bounds result after k kernel MUSCL SSPRK3 steps. |
| `CFDLean.Exec.run_musclEulerStepArray_sum` | E0b-T | FVM | accepted | With real arithmetic and dx ≠ 0, k kernel MUSCL Euler steps keep the sum of the entries. |
| `CFDLean.Exec.run_musclSsprk3StepArray_sum` | E0b-T | FVM | accepted | With real arithmetic and dx ≠ 0, k kernel MUSCL SSPRK3 steps keep the sum of the entries. |
| `CFDLean.Exec.run_musclEulerStepArray_totalVariation_le` | E0b-T | FVM | accepted | Under the hypotheses of the bounds result, k kernel MUSCL Euler steps do not increase the total variation of the entries. |
| `CFDLean.Exec.run_musclSsprk3StepArray_totalVariation_le` | E0b-T | FVM | accepted | Under the hypotheses of the bounds result, k kernel MUSCL SSPRK3 steps do not increase the total variation of the entries. |
| `CFDLean.Exec.limiterEulerStepArray_size` | E0c-K | FVM | accepted | The kernel MUSCL Euler step with a limiter choice returns an array of the same size. |
| `CFDLean.Exec.limiterSsprk2StepArray_size` | E0c-K | FVM | accepted | The kernel MUSCL SSPRK2 step with a limiter choice returns an array of the same size. |
| `CFDLean.Exec.limiterSsprk3StepArray_size` | E0c-K | FVM | accepted | The kernel MUSCL SSPRK3 step with a limiter choice returns an array of the same size. |
| `CFDLean.Exec.isPos_eq` | E0c-L | FVM | accepted | With real arithmetic the kernel sign test is the decision of 0 < x. |
| `CFDLean.Exec.limiterSlope_eq` | E0c-L | FVM | accepted | With real arithmetic the kernel slope of each limiter (none, minmod, MC, superbee, van Leer, van Albada) is its mathematical slope function. |
| `CFDLean.Exec.Limiter.slopeBounded` | E0c-L | FVM | accepted | The slope function of every kernel limiter except none is θ-bounded with the constant of that limiter. |
| `CFDLean.Exec.Limiter.theta_le_two` | E0c-L | FVM | accepted | The bound constant of every kernel limiter is at most 2. |
| `CFDLean.Exec.limiterEulerStepArray_refines` | E0c-S | FVM | accepted | For every limiter, also none: the kernel MUSCL Euler step of an array that represents u represents the MUSCL-Rusanov Forward Euler step of u with that slope function. |
| `CFDLean.Exec.limiterSsprk2StepArray_refines` | E0c-S | FVM | accepted | For every limiter the kernel MUSCL SSPRK2 step represents the MUSCL-Rusanov SSPRK2 step. |
| `CFDLean.Exec.limiterSsprk3StepArray_refines` | E0c-S | FVM | accepted | For every limiter the kernel MUSCL SSPRK3 step represents the MUSCL-Rusanov SSPRK3 step. |
| `CFDLean.Exec.limiterEulerStepArray_minmod` | E0c-S | FVM | accepted | With the minmod choice the limiter kernel Euler step is the E0b MUSCL kernel step, for every arithmetic. |
| `CFDLean.Exec.limiterSsprk2StepArray_minmod` | E0c-S | FVM | accepted | With the minmod choice the limiter kernel SSPRK2 step is the E0b one, for every arithmetic. |
| `CFDLean.Exec.limiterSsprk3StepArray_minmod` | E0c-S | FVM | accepted | With the minmod choice the limiter kernel SSPRK3 step is the E0b one, for every arithmetic. |
| `CFDLean.Exec.run_limiterEulerStepArray_sum` | E0c-T | FVM | accepted | With real arithmetic and dx ≠ 0, k kernel MUSCL Euler steps keep the sum of the entries, for every limiter and for the unlimited scheme. |
| `CFDLean.Exec.run_limiterSsprk3StepArray_sum` | E0c-T | FVM | accepted | With real arithmetic and dx ≠ 0, k kernel MUSCL SSPRK3 steps keep the sum of the entries, for every limiter and for the unlimited scheme. |
| `CFDLean.Exec.run_limiterEulerStepArray_bounds` | E0c-T | FVM | accepted | For every limiter except none, with dx > 0, dt ≥ 0 and (4 + 2θ) · dt · max(\|m\|, \|M\|) ≤ dx, every entry stays in [m, M] after k kernel MUSCL Euler steps. |
| `CFDLean.Exec.run_limiterSsprk3StepArray_bounds` | E0c-T | FVM | accepted | The same bounds result after k kernel MUSCL SSPRK3 steps. |
| `CFDLean.Exec.run_limiterEulerStepArray_totalVariation_le` | E0c-T | FVM | accepted | Under the hypotheses of the bounds result, k kernel MUSCL Euler steps do not increase the total variation of the entries. |
| `CFDLean.Exec.run_limiterSsprk3StepArray_totalVariation_le` | E0c-T | FVM | accepted | Under the hypotheses of the bounds result, k kernel MUSCL SSPRK3 steps do not increase the total variation of the entries. |
| `CFDLean.Exec.FV1D.burgers_refines` | FVA-B | FVM | accepted | The shared real Burgers array step equals the assembled B0 and existing E0 updates. |
| `CFDLean.Exec.FV1D.euler_refines` | FVA-E | FVM | accepted | All three coordinates of the real Euler array step represent the assembled FV1D update. |
| `CFDLean.Exec.burgers_nonuniform_refines` | FVNA-F | FVM | accepted | Over the reals the first-order non-uniform array kernel with the Burgers model stores the FVN first-order Burgers step on the mesh of the width array, in every cell. |
| `CFDLean.Exec.euler_nonuniform_refines` | FVNA-F | FVM | accepted | For γ > 1 and an array storing an admissible Euler field, the first-order non-uniform array kernel stores the FVN Euler step on the mesh of the width array, in all three components of every cell. |
| `CFDLean.Exec.nuLimiterEulerStepArray_refines` | FVNA-M | FVM | accepted | For every limiter, including none, the non-uniform MUSCL Forward Euler array kernel over the reals stores the FVN Burgers MUSCL step with the limiter's slope function. |
| `CFDLean.Exec.nuLimiterSsprk2StepArray_refines` | FVNA-M | FVM | accepted | For every limiter the non-uniform MUSCL SSPRK2 array kernel over the reals stores the FVN Burgers MUSCL SSPRK2 step. |
| `CFDLean.Exec.nuLimiterSsprk3StepArray_refines` | FVNA-M | FVM | accepted | For every limiter the non-uniform MUSCL SSPRK3 array kernel over the reals stores the FVN Burgers MUSCL SSPRK3 step. |
| `CFDLean.Exec.burgers_nonuniformStepArray_uniform` | FVNA-U | FVM | accepted | If every width equals dx > 0, the first-order non-uniform kernel with the real Burgers model is the FVA stepArray with dx. |
| `CFDLean.Exec.euler_nonuniformStepArray_uniform` | FVNA-U | FVM | accepted | If every width equals dx > 0, the first-order non-uniform kernel with the real Euler model is the FVA stepArray with dx, for every γ. |
| `CFDLean.Exec.nuLimiterEulerStepArray_uniform` | FVNA-U | FVM | accepted | If every width equals dx > 0, the non-uniform MUSCL Forward Euler kernel is the E0c limiterEulerStepArray with dx, for every limiter. |
| `CFDLean.Exec.nuLimiterSsprk2StepArray_uniform` | FVNA-U | FVM | accepted | If every width equals dx > 0, the non-uniform MUSCL SSPRK2 kernel is the E0c limiterSsprk2StepArray with dx, for every limiter. |
| `CFDLean.Exec.nuLimiterSsprk3StepArray_uniform` | FVNA-U | FVM | accepted | If every width equals dx > 0, the non-uniform MUSCL SSPRK3 kernel is the E0c limiterSsprk3StepArray with dx, for every limiter. |
| `CFDLean.Exec.burgers_nonuniformStepArray_weighted_sum` | FVNA-T | FVM | accepted | The first-order Burgers non-uniform array kernel keeps the width-weighted sum ∑ w[i] u[i] for positive widths of the array size. |
| `CFDLean.Exec.nuLimiterEulerStepArray_weighted_sum` | FVNA-T | FVM | accepted | For every limiter the non-uniform MUSCL Forward Euler array kernel keeps the width-weighted sum ∑ w[i] u[i]. |
| `CFDLean.Exec.nuLimiterSsprk2StepArray_weighted_sum` | FVNA-T | FVM | accepted | For every limiter the non-uniform MUSCL SSPRK2 array kernel keeps the width-weighted sum ∑ w[i] u[i]. |
| `CFDLean.Exec.nuLimiterSsprk3StepArray_weighted_sum` | FVNA-T | FVM | accepted | For every limiter the non-uniform MUSCL SSPRK3 array kernel keeps the width-weighted sum ∑ w[i] u[i]. |
| `CFDLean.Exec.euler_nonuniformStepArray_weighted_sum` | FVNA-T | FVM | accepted | For every γ the first-order Euler non-uniform array kernel keeps the width-weighted sums of density, x-momentum and total energy, each separately. |
| `CFDLean.Exec.burgers_nonuniformStepArray_bounds` | FVNA-T | FVM | accepted | If every entry lies in [m, M] and the FVN-B cell condition dt (a(i-1) + a i) ≤ w[i] holds, the first-order Burgers non-uniform array kernel keeps every entry in [m, M]. |
| `CFDLean.Exec.burgers_nonuniformStepArray_totalVariation_le` | FVNA-T | FVM | accepted | Under the FVN-B face condition dt · a i ≤ min(w[i], w[i+1]) the first-order Burgers non-uniform array kernel does not increase the total variation of the entries. |
| `CFDLean.Exec.run_nuLimiterEulerStepArray_stable` | FVNA-T | FVM | accepted | For a limiter other than none with mesh ratio L.theta, 0 ≤ dt, entries in [m, M] and 8 · dt · max(\|m\|, \|M\|) ≤ w[i], any number of non-uniform MUSCL Forward Euler kernel steps keep [m, M] and do not increase the total variation. |
| `CFDLean.Exec.run_nuLimiterSsprk2StepArray_stable` | FVNA-T | FVM | accepted | The same bounds and total-variation result for any number of non-uniform MUSCL SSPRK2 kernel steps. |
| `CFDLean.Exec.run_nuLimiterSsprk3StepArray_stable` | FVNA-T | FVM | accepted | The same bounds and total-variation result for any number of non-uniform MUSCL SSPRK3 kernel steps. |
| `CFDLean.Exec.E1.value_isSome` | E1-1 | method-free | pending | Decoder succeeds exactly on finite binary64 values. |
| `CFDLean.Exec.E1.cast_step` | E1-2 | FVM | pending | Casting the rational Burgers update to reals agrees with the entire exact-real array step. |
| `CFDLean.Exec.E1.checkStep_sound` | E1-3 | FVM | pending | Acceptance implies finite output and a per-cell bound for the represented inputs. |
| `CFDLean.Exec.E1.real_cell_bound` | E1-3 | FVM | pending | Every present real-step output is within the supplied absolute budget of the decoded observed cell. |
