# M3 proposal: node-centered residuals and tetrahedral median-dual geometry

**Proposed only. Scientific approval and authorization to implement M3 are pending.** M2 is independently accepted at `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`; see [the full-M2 decision](../reviews/M2/Acceptance.md) and [downstream pin](accepted-M2.json). This proposal introduces no Lean implementation or amendment to an accepted specification.

## Proposed residual and caller contract

For a finite node set N, a finite set E of uniquely identified interior dual interfaces, and boundary pieces B, propose the integrated outgoing residual

\[
 f_e=\operatorname{encode}\bigl(\widehat F_\gamma(U_{t(e)},U_{h(e)},S_e)\bigr),\qquad
 R_i=\sum_{e\in E}\sigma(i,e)f_e+\sum_{b\in B:\,o(b)=i}g_b,
\]
\[
 \sigma(i,e)=\begin{cases}1&i=t(e),\\-1&i=h(e),\\0&\text{otherwise.}\end{cases}
\]

Here t(e) != h(e); S_e points outward from the tail's dual volume into the head's. Every interface has one record and is evaluated once. The head receives minus that same integrated transfer. U_i is an accepted M1 Conservative 3 state; widehat F is the unchanged accepted M2 numericalFlux. R_i, f_e and g_b live in the existing five-coordinate vector space, not a new physical-state model. Scalar multiplication and sums are coordinate arithmetic. No additive instances are added to Conservative solely for assembly.

The caller supplies a common gamma>1 and admissible nodal states for physical use. This first baseline uses the endpoint nodal states directly, with no reconstruction, gradients or limiter. It makes no second-order accuracy claim. The algebraic assembly may accept arbitrary five-vector edge/boundary transfers; its Roe specialization uses the actual accepted flux. Boundary transfers g_b are independent supplied data with an owner o(b), not a selected wall/far-field algorithm. An interface between dual volumes is an interior interface even when one or both endpoint nodes lie on the domain boundary. Exterior pieces have one owner and contribute once.

S_e and boundary area vectors T_b have area units. M2 already integrates over S_e, so assembly supplies no extra area multiplier. R_i has integrated conserved-transfer units. There is no division by dual volume or time step in M3; that belongs to M5. The residual has the outgoing sign, compatible with a later update U_new=U-dt R/V.

## Geometry and the selected aggregation rule

For generic assembly, the proposed node metric defect is

\[
 G_i=\sum_e\sigma(i,e)S_e+\sum_{b:o(b)=i}T_b.
\]

Cancellation of interior transfers requires paired incidence, not G_i=0. Conversely, constant-state preservation requires geometric closure and compatible boundary fluxes. A generic interface may assume G_i=0 and prove a conditional result. The concrete tetrahedral median-dual construction below must **derive** G_i=0; it may not receive that same conclusion as an input certificate.

For a concrete primal edge, sum its oriented partial-face area vectors first:

\[
 S_{ij}=\sum_{T\supset\{i,j\}}\sum_{\tau\subset\text{dual interface in }T}A(\tau),
 \qquad A(a,b,c)=\tfrac12(b-a)\mathbin\times(c-a).
\]

The proposed method evaluates **one** accepted Roe flux on this S_ij with the endpoint states. If S_ij=0, use M2's explicit zero-area result. Otherwise M2 uses a= sqrt(S_ij dot S_ij) and n=S_ij/a. In general this a differs from the sum of individual facet areas, and n differs from a sum of unit normals. No orthogonality of S_ij to the primal edge is assumed.

This edge-aggregated flux is a specific proposed discretization choice requiring approval. It is generally different from summing the Roe flux separately over nonparallel partial-face vectors. M2 proves positive homogeneity, not arbitrary area-vector additivity. For example, the project-derived preparation case gamma=2, rho_L=rho_R=1, u_L=u_R=0, p_L=1, p_R=4 gives cbar²=5 and mass transfer -3|S|/(2sqrt(5)). The sum on S_1=(1,0,0), S_2=(0,1,0) is -3/sqrt(5); the single flux on S_1+S_2 has mass transfer -3sqrt(2)/(2sqrt(5)). No equivalence is proposed. At an equal state, M1's physical flux is linear in S, which is the separate fact used for constant-state closure.

### Concrete geometric domain

Propose an initial restriction to a finite conforming embedded mesh of nondegenerate tetrahedra in real 3-space. This restriction is for approval; it does not cover hexahedra, prisms, pyramids, curved elements, hanging nodes or general polyhedra.

Input data are finite node coordinates, tetrahedra with four distinct vertices, and their face incidence. Each tetrahedron is affinely independent. Distinct elements intersect only in a common complete face, edge, vertex, or not at all. Each face belongs to one or two tetrahedra. A shared face has its incident tetrahedra on opposite sides of its plane; consistent outward face orientations follow from this geometric hypothesis. Single-incidence faces are the exterior boundary. These are mesh-validity assumptions, not an assertion that a mesh importer validates them. Every node for which positive dual volume is promised belongs to an element. The proof must expose exactly which of these assumptions it uses.

In tetrahedron T=[p0,p1,p2,p3], let m_ij=(p_i+p_j)/2, f_ijk=(p_i+p_j+p_k)/3, and c_T=(p0+p1+p2+p3)/4. The barycentric subdivision has 24 tetrahedra [p_i,m_ij,f_ijk,c_T], indexed by the 24 permutations (i,j,k,l). The six pieces with fixed first vertex i constitute that vertex's local dual volume. Orient each small tetrahedron positively; do not infer a physical volume from a signed determinant of arbitrary vertex order.

The interface for edge {i,j} inside T consists of the two triangles with vertex sets {m_ij,f_ijk,c_T} and {m_ij,f_ijl,c_T}. Orient them out of the local dual at i and toward the dual at j. Prove their dot product with p_j-p_i is positive from nondegeneracy, rather than silently selecting an unproved normal. The remaining local boundary consists of two triangles [p_i,m_ij,f_ijk] and [p_i,f_ijk,m_ik] on each primal face containing i, oriented outward from T.

Prove the oriented-triangle vector sum on every tetrahedron boundary is zero. Sum the six barycentric pieces, cancel their internal faces, and identify exactly the edge-interface triangles and primal-face patches just specified. Their area vectors close locally. Then sum over incident primal tetrahedra. Vertex patches on shared primal faces cancel; the surviving patches on exterior faces become T_b, with owner i and their original primal-face identity retained for later M4 boundary labels. This must give G_i=0 with the same S_e and T_b used by assembly. Boundary ownership is on patches; a corner node may own patches belonging to different physical boundaries.

Define Vol(T)=abs(det(p1-p0,p2-p0,p3-p0))/6. Prove each barycentric tetrahedron has volume Vol(T)/24, a vertex's local contribution is Vol(T)/4, and V_i=sum_{T contains i}Vol(T)/4. Prove positivity at every used node and sum_i V_i=sum_T Vol(T). These are geometric identities, not a time-update theorem or an independently assumed volume partition. Full measure-theoretic coverage of the union is not promised; the finite subdivision, incidence cancellation and determinant-volume identities must be proved explicitly.

## Proposed mathematical obligations

These six IDs are proposals for scientific review, not bindings to existing theorems. After approval, freeze the specification separately, then populate qualified Lean declarations as proofs are completed.

| ID | Proposed statement, hypotheses and derivation | Consumer |
| --- | --- | --- |
| M3-I | For finite distinct-endpoint interfaces, define incidence and show each edge has exactly one +1 and one -1 contribution. The signed-area and transfer sums agree with explicit outgoing-node enumeration. Project finite-sum derivation. | Makes pairing and ownership explicit. |
| M3-R | For arbitrary five-vector transfers and owner-assigned exterior data, sum_i R_i=sum_b g_b. Specialize to the actual M2 edge flux without assuming cancellation or closure. Project sum exchange and M2-F2 local-orientation interpretation. | M5/M6 global boundary balance. |
| M3-O | Swapping an edge's endpoints, reversing S_e, and correspondingly using the swapped nodal states leaves every assembled R_i unchanged. Prove equality with separately evaluated outward physical-interface orientation using M2-F2; include zero area. Also prove invariance under finite reindexing of nodes/edges/boundary pieces with transported data. | Representation-independent residual. |
| M3-G | The explicit tetrahedral barycentric interface/boundary construction derives local and global vector closure, outward pairing and correct boundary ownership under the stated mesh-validity assumptions. No closure conclusion is an input. Cross-product and finite incidence derivation from the inspected construction. | Supplies G_i=0 for an actual selected dual. |
| M3-V | The 24 barycentric determinant volumes, six-per-vertex grouping, V_i formula, used-node positivity and total-volume identity follow from nondegenerate primal tetrahedra and incidence. Project determinant derivation. | Supplies fixed positive volumes to M5. |
| M3-C | For one common admissible U, nodal values U_i=U and supplied g_b=encode(physicalFlux gamma U T_b), derive R_i=encode(physicalFlux gamma U G_i). Hence G_i=0 implies R_i=0; instantiate with M3-G. Use actual M2-F1/F2 and M1 flux linearity. Do not assume arbitrary future M4 boundary data are compatible. | Constant-state spatial consistency before time integration. |

Physical specializations retain gamma>1 and the accepted M1 admissibility predicate. Generic linear incidence identities need neither admissibility nor positive volume; distinguish those stronger algebraic statements from physical applicability. No global state positivity, entropy inequality, accuracy order or convergence theorem is included.

## Source traceability and convention decision

Use the already approved Blazek **first edition (2001)**, local file identified by SHA-256 `c37225f646c5e237a20361db0979cf09218de9800dc9a85448314e7646758fc5`. No new authoritative reference or edition is requested.

| Actual source inspected | Proposed use and boundary of authority |
| --- | --- |
| Section 5.1.2, printed pp. 135-137 (PDF pages 158-160), Fig. 5.4, Eqs. (5.8)-(5.13). | Oriented triangular face vectors and volume/normal conventions. Cross-product and determinant formulations here are project derivations. General quadrilateral approximations are excluded by the tetrahedral scope. |
| Section 5.2, printed pp. 138-139 (PDF pages 161-162). | Element/face incidence and consistent boundary-face orientation; boundary labels are associated with faces, not a unique label per corner node. |
| Section 5.2.2, printed pp. 142-145 (PDF pages 165-168), Figs. 5.7(a), 5.8, 5.9, Eq. (5.19), and the edge loop on p. 145. | Centroid/face-centroid/edge-midpoint median dual, aggregation around primal edges, and equal-and-opposite residual accumulation. The exact tetrahedral subdivision/closure proof is a project derivation, not a theorem imported from the text. |
| Accepted M1 and M2 at their immutable mathematical revisions. | Actual physical-flux linearity, numerical consistency/reversal/zero branch, chart and physical domain. No SU2 source supplies definitions. |

Printed pp. 142, 143 and 145 were rendered and visually inspected; the other listed pages were read in full from the local PDF text. On p. 142 the prose says mean unit normal while Eq. (5.19) visibly sums the normals, followed by a sum of partial areas. A bare sum of unit normals is generally not unit, and multiplying it by the sum of areas is not in general the sum of area vectors. This proposal therefore specifies the oriented area-vector sum and its Euclidean normalization explicitly as a project convention requiring approval. It does not import the ambiguous wording literally or claim an authenticated correction to the book. No new errata-history investigation or publisher-confirmed correction is asserted. The edge-loop conservation mechanism on p. 145 is retained.

## Implementation and validation plan after approval

- **M3a:** add a small assembly module for finite incidence, transfers and residuals; prove I/R/O and conditional C, with boundary data explicitly external. Before relying on it, extend the inherited guard to all 66 accepted M2 bindings/types and preserve every accepted definition/proof source against the pinned M2 candidate. Retain original M2 approval and review evidence.
- **M3b:** add the tetrahedral median-dual geometry module, derive G/V, and compose it with the very same assembly to instantiate C and the global balance. A final full-M3 review requires both stages, not just the abstract conditional result.

Proposed files are CFDLean/Discretization/Assembly.lean and CFDLean/Geometry/MedianDual.lean, plus their expected-type/examples checks and the cumulative audit/result mapping. Introduce smaller supporting modules only if proofs require them. Preserve Lean/mathlib pins and the solver-independent architecture. Do not edit accepted specifications to close proof goals or use SU2's geometry as authority.

Exact checks after approval must include: a single interface with opposite node transfers; a nontrivial three-node incidence cycle; per-edge reversal/reindexing; zero-area interfaces; an admissible constant state on a closed dual; an explicitly incompatible boundary transfer producing a nonzero residual; the standard tetrahedron and a genuinely oblique affine tetrahedron; two tetrahedra sharing a face, with shared vertex patches cancelling; all 24 flag volumes and all four local dual closures; and zero-volume/isolated/nonmanifold input exclusions. Check the nonparallel aggregation distinction, not only parallel area scaling.

The accompanying Fraction-based preparation script checks determinant subdivision, outward triangle pairing, local/global closure and incidence on exact small cases. These are proposal feasibility controls, not Lean proofs or acceptance. The nonlinear flux example above is a displayed algebraic derivation from the accepted projector formula and must receive an explicit check during implementation/review. Full owning-module and transitive kernel audits, the existing allowed foundational axioms, exact preservation of all inherited contracts, and a fresh pinned-source replay with both cache controls remain mandatory for each submitted mathematical checkpoint. Future guards must distinguish the independently accepted M2 verdict from historical machine-evidence pending fields at the original submission.

## Decisions requested before implementation

Approve or amend (1) the direct nodal-state, edge-aggregated original Roe residual with supplied boundary transfers; (2) the tetrahedral conforming-mesh scope and exact median-dual geometry/volume obligations; (3) the explicit area-vector aggregation/normalization resolution of the source convention; and (4) the six proposed IDs, two-stage implementation sequence and preservation/audit plan in the existing private repository.

Proposal review may recommend implementation, but Andrea's scientific/repository authorization is still required before M3 Lean work. No M4 boundary algorithm, time update, entropy/positivity repair, mixed-element extension or SU2 correspondence is requested here.
