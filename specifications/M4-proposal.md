# M4 proposal: explicit stationary boundary transfers

**Proposal only: scientific review and Andrea's approval are required before M4 Lean implementation.** Full M3 is independently accepted, without conditions, at `e2ea538b8da38c01c098ef28a3ea31030d90c6bb`; see reviews/M3/Acceptance.md and accepted-M3.json. This proposal changes no accepted mathematical source or scientific specification.

## Proposed choices and physical domain

Propose a first-order boundary baseline for the already selected stationary, inviscid, calorically perfect Euler model on the accepted conforming tetrahedral median dual. Retain exact real arithmetic, common gamma>1, actual M1 admissibility, direct owner nodal states, the accepted edge-aggregated original Roe interior flux, and outgoing integrated residual signs. No reconstruction, entropy modification or time update is introduced.

Choose three explicit boundary kinds: stationary slip wall, stationary inviscid symmetry traction, and prescribed-exterior Roe. Wall and symmetry use the same pressure transfer but retain distinct labels. The prescribed-exterior kind is a weak two-state numerical-flux boundary with a fixed admissible exterior state. It is proposed as the initial open/far-field baseline, with no claim of nonreflection, characteristic PDE well-posedness, physical accuracy order or equivalence to characteristic-variable boundary reconstruction. These algorithm choices require approval separately from the already accepted interior Roe flux.

This scope implements the inviscid flux contribution at a symmetry plane. It does not implement symmetry conditions on reconstructed gradients, mirror a missing half-volume, remove residual components or modify accepted face vectors. The current direct-state Euler model contains no gradient reconstruction or viscous terms.

## Face labels and exact reuse of accepted geometry

For MeshData M with Conforming, retain its actual Boundary type, owner map, faceID, edgeArea and boundaryArea unchanged. For a boundary record b, let F_b be its existing three-node primal-face ID, i_b its owner and T_b its outward integrated patch vector. Choose a boundary-kind function k on primal-face IDs, and an exterior-state function V on primal-face IDs. Values on non-exterior faces are unused. Every prescribed exterior face must have V(F) admissible at the common gamma; all used nodal states are admissible. Wall/symmetry transfers do not use V.

The choice k(F_b) gives every owner patch of the same primal face the same kind, by construction. A corner node may own patches of different kinds on different faces. No single node boundary label, duplicate exterior face, new geometric normal or replacement area vector is introduced. Existing boundaryKey injectivity/range supplies exact face/owner enumeration. External group names may later index this face map; a mesh-tag importer is outside M4.

## Wall and symmetry transfer

In the existing five-coordinate conserved-transfer layout, define the proposed integrated pressure transfer

    W_gamma(U,T) = (0, p_gamma(U) T_0, p_gamma(U) T_1, p_gamma(U) T_2, 0).

The pressure is the actual M1 pressure of the owner state U, sampled directly at that owner. There is no face interpolation, average unit normal, division by area or extra area multiplier. Zero area gives zero transfer. This owner-pressure rule is an explicit project baseline; it is not Blazek's tetrahedral pressure interpolation (6 p_i+p_j+p_k)/8, Eq. (8.13).

For physical slip compatibility require dot(m,T)=0 on each wall/symmetry patch. With positive density this is the zero normal-velocity condition. Prove

    W_gamma(U,T) = encode(physicalFlux gamma U T)  iff  dot(m,T)=0.

The raw equality may be stronger than its admissible physical specialization. Mass and energy transfers vanish for all raw inputs; the momentum transfer is p T and generally does not vanish. Prove linearity in T and orientation reversal. For gamma>1 and admissible U, the wall pressure is positive.

Computing W does not itself force the nodal velocity tangent after an update. No projected velocity, reflected-state Roe wall, strong resetting of momentum, or proof of time-evolved impermeability is included. Equality of W to the actual physical flux must retain the tangency qualification. At corners tangency is required separately for every incident wall/symmetry face; no averaged normal substitutes for these conditions.

## Prescribed-exterior Roe transfer

With outward T and owner U on the left, define exactly

    P_gamma(U,V,T) = encode(CFDLean.Roe.numericalFlux gamma U V T).

V is the prescribed admissible exterior state of that primal face, independent of the current U for the fixed boundary data under study. There is one accepted integrated Roe evaluation on the existing grouped owner patch T. There is no ghost-volume geometry, state projection or independent replacement solver. Reconstructed or time-dependent exterior data would require a further specification.

Use accepted M2 to prove: P(U,U,T)=encode(physicalFlux gamma U T); zero area gives zero; nonnegative area scaling holds; reversing T with swapped interior/exterior arguments gives the negative transfer. The last identity is an algebraic orientation identity, not invariance under changing the physical boundary's outward orientation while leaving its roles fixed.

For T nonzero, n=T/area(T), and the actual two-state Roe average ubar,cbar, prove full upwind reductions:

- If cbar <= dot(ubar,n), P equals the owner's physical transfer.
- If dot(ubar,n) <= -cbar, P equals the exterior physical transfer.

These are sufficient Roe-average spectral conditions, including sonic equality. They are not tests based only on the interior Mach number. Subsonic, stationary and mixed-sign cases use the same original Roe expression without branch-specific characteristic formulas. No reflection coefficient or exterior-state-independent supersonic theorem is promised outside the stated two-state condition.

This is a project composition of the accepted Riemann flux with prescribed exterior data. It is not the Whitfield/Janus characteristic-variable scheme in Blazek Eqs. (8.20)-(8.23), Giles' nonreflecting method, a lifting-body vortex correction, or a positivity/entropy repair. Those variants require their own source/definition/domain decisions before use.

## Mixed boundary residual, compatibility and balance

Define g_b(U) as W_gamma(U_i,T_b) for wall/symmetry, or P_gamma(U_i,V(F_b),T_b) for prescribed exterior. Feed this actual g to the unchanged accepted Assembly.residual and actual interior roeTransfer. Do not divide by V_i or introduce dt.

Derive the global five-vector balance as the sum of these exact boundary transfers, using accepted M3. Projecting its mass and energy components leaves only the prescribed-exterior contributions. Global momentum also contains the wall/symmetry pressure traction. Neither total residual nor total momentum is generally zero on an open domain or a pressured wall.

For one common admissible state U*, require on every wall/symmetry patch dot(m*,T_b)=0, and on every prescribed-exterior face V(F)=U*. Then prove g_b=encode(physicalFlux gamma U* T_b) for the same accepted B/T, and invoke the concrete accepted metric closure/common-state theorem to derive R_i=0. Matching V is sufficient; it is not an if-and-only-if characterization of all open-boundary compatibility.

A common state with nonzero normal momentum at a wall is not asserted preserved. Likewise, different prescribed exterior data can generate nonzero residual. Controls must use the actual accepted Roe numericalFlux and these selected boundary transfers, not an arbitrary algebraic correction in place of the algorithm.

Transport all node/edge/boundary IDs, ownership, areas, states, kinds and prescribed exterior data in generic finite reindexing. Prove the constructed boundary transfers transport with them, then use accepted M3 reindexing. For the concrete instance first derive patch kinds/states from face maps, then transport these values on the same boundary records. Rebuilding a separately renumbered mesh and proving construction naturality is not added to this milestone.

## Proposed mathematical obligations

These IDs are proposals, with no M4 theorem bindings or implementation yet.

| ID | Proposed statement and hypotheses | Consumer |
| --- | --- | --- |
| M4-B | Face-based boundary kinds and prescribed data produce exactly one transfer per accepted exterior owner patch, consistent across a primal face and allowing different kinds at a corner. | Concrete tagged boundary interface. |
| M4-W | Direct owner-pressure wall/symmetry transfer has zero mass/energy, pressure traction, zero area, area linearity/reversal and physical-flux equality exactly under zero normal momentum; admissible pressure is positive. | Slip/symmetry compatibility. |
| M4-P | Actual prescribed-exterior original Roe transfer has consistency, zero area, nonnegative scaling, swapped reversal and the two stated Roe-average full-upwind reductions, including sonic equality. | Explicit selected open-boundary algorithm. |
| M4-R | Compose these actual transfers with unchanged M3 residual; derive the full boundary balance and mass/energy/pressure-traction component balances. | Later M5/M6 conservation. |
| M4-O | Constructed transfer and residual commute with finite transported node/edge/boundary relabeling, including kinds/exterior data. | Representation independence. |
| M4-C | Common admissible state plus per-wall tangency and matching prescribed exterior state gives compatible physical transfers and concrete zero residual. Exhibit actual incompatible cases. | Qualified stationary consistency. |

## Source traceability and convention decisions

Use only the already approved Blazek first edition (2001), local SHA-256 `c37225f646c5e237a20361db0979cf09218de9800dc9a85448314e7646758fc5`, plus accepted M1/M2/M3 definitions and proofs. This proposal requests no new reference or edition.

| Inspected source | Use and boundary of authority |
| --- | --- |
| Section 8.2.1, printed p. 270, PDF p. 293, Eqs. (8.1)-(8.2). | Physical stationary inviscid tangency and pressure-only wall flux. Our integrated vector uses T, rather than multiplying a unit-normal flux by a second area factor. |
| Printed pp. 272-273, PDF pp. 295-296, Eqs. (8.7)-(8.11); printed p. 275, PDF p. 298, Eq. (8.13). | Distinct cell-vertex/median-dual pressure and enforcement choices. Direct owner pressure on each accepted patch is a project choice for approval; it is not the book's tetrahedral interpolation or its averaged-normal projected update. |
| Section 8.1, printed pp. 268-269, PDF pp. 291-292. | Boundary states and use of the interior spatial flux at an exterior interface. The proposed direct owner/exterior Roe composition is project-defined; no dummy mesh or stencil extrapolation is imported. |
| Section 8.3/8.3.1, printed pp. 277-279, PDF pp. 300-302, Eqs. (8.20)-(8.23). | Identifies the different characteristic farfield alternative and incoming/outgoing distinction. Those characteristic formulas are not claimed as the selected P algorithm. |
| Section 8.5, printed p. 285, PDF p. 308, Eqs. (8.37)-(8.38). | Physical symmetry qualifications and alternative discrete enforcement. The selected inviscid traction does not implement the text's mirrored half-volume, residual projection, geometry correction or gradient conditions. |
| Accepted M1, full M2 and full M3 at their immutable mathematical pins. | Actual pressure/physical flux, original Roe transfer/upwind properties, exact concrete exterior ownership/areas, conservation and qualified common-state interface. |

All listed source pages were read completely from local PDF text. PDF pages 293, 298, 302 and 308 were also rendered and visually inspected, including the pressure-flux and interpolation formulas. Exact-real algebra, ownership/transport and composition statements are project derivations. No publisher correction, source-authenticated equivalence of different algorithms or SU2 definition is asserted.

## Implementation and validation plan after approval

1. Before any M4 mathematical work, preserve all 117 accepted cumulative bindings, exact M3 parts/stages/types and all accepted mathematical sources against e2ea538. The current acceptance/proposal checkpoint extends and tests that guard. Keep the original reviewer archive and independent full-M3 verdict separate from historical worker evidence.
2. Freeze an approved M4 contract separately from this proposal, with exact IDs and algorithm choices. M4a would add the local tagged-transfer interface, W/P properties and exact local controls (B/W/P). M4b would compose R/O/C on the same accepted concrete median dual and request a separate full-M4 verdict. Do not fill a future part with a conditional result from an earlier stage.
3. Proposed new files are CFDLean/Boundary/Stationary.lean and, if composition needs separation, CFDLean/Boundary/Assembly.lean, plus exports, expected-type checks, cumulative bindings/audit and source maps. No new dependency or toolchain change is proposed.
4. Exact controls: zero area; admissible rest and tangential moving walls; oblique pressure traction; nonzero normal momentum showing physical incompatibility; prescribed-state consistency and mismatching exterior state; strict and sonic Roe-average upwind cases in both directions; the same owner at a wall/open corner with face-based kinds; generic transported relabeling; mixed wall/open closure on the standard and two-cell accepted meshes; all-wall rest-state preservation; global mass/energy excluding wall transfers while retaining pressure momentum.
5. Use the actual pressure/Roe interface for controls. Check that W is generally different from Roe with reflected momentum and from Eq. (8.13) interpolation. No equivalence claim may erase this variant decision. reviews/M4/PreparationChecks.py provides exact rational feasibility controls, not Lean proofs or independent acceptance.
6. Run the unchanged full owning-module/transitive kernel audit, all expected-type checks and checker fixtures; require the existing three foundational axioms and no reachable unsafe declaration. Every submitted mathematical stage needs a new clean pinned-source replay, both binary-cache controls, local pinned widget compilation and deterministic evidence comparison. A proposal/checker-only checkpoint does not claim a new mathematical cold replay.

## Decisions requested before implementation

Review, then approve or amend (1) direct owner-pressure transfer on each wall/symmetry owner patch, with qualified tangency and no projection/reflection enforcement; (2) the explicit prescribed-exterior original Roe open-boundary baseline, with the stated physical/spectral scope and no nonreflection claim; (3) primal-face labeling and exact reuse of accepted B/T; (4) the six IDs, two-stage sequence and preservation/replay plan.

If a characteristic/nonreflecting farfield or tetrahedral pressure interpolation is desired instead, amend and review the relevant formulas/domain before freezing or implementing them. Proposal review may recommend implementation; Andrea's scientific/repository approval is still required. No M4 Lean implementation, time update, entropy/update-positivity repair or SU2 correspondence is authorized by this proposal.
