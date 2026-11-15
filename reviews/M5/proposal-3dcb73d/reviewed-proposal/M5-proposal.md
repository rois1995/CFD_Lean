# M5 proposal: one lumped explicit Euler step on fixed median-dual volumes

Status: **scientific proposal awaiting independent review; no M5 Lean implementation or frozen M5 contract**. The user has already supplied standing implementation authorization in reviews/Standing_Authorization.md. After the independent proposal recommendation and resolution of mandatory findings, freeze the exact contract and proceed under that authorization without another approval request. A proposal recommendation is not implementation acceptance.

## Accepted dependencies and preservation

Full M4 B/W/P/R/O/C and scoped M4b R/O/C are independently accepted without conditions at `3a586a42546cba1784cc79269e3f9d1c5d843f0c`, tree `670a0ff21ce84187b04547b30ba27530983209aa`. See specifications/accepted-M4.json, reviews/M4/Acceptance.md and reviews/M4b/Acceptance.md. All 28 original reviewer payloads and five deterministic candidate/worker matches were checked; the original archive is reviews/M4b/independent-3a586a4. Full M3 retains its separate accepted mathematical pin `e2ea538b8da38c01c098ef28a3ea31030d90c6bb`.

Before later mathematics, the inherited baseline advances to accepted full M4: protect all **156** ordered bindings/types, all six accepted M4 result records/stages and every accepted mathematical source, including Boundary/Assembly.lean and AssemblyControls.lean. Retain Integrity/KernelAudit, compiler and nine dependency pins, prior scientific/precision/approval files, exact prior result maps and historical archives. The 182-example file remains an exact prefix. This proposal adds no active result-map entry or theorem claim.

The original roadmap in M2-proposal.md assigns M5 explicit Euler with positive fixed volumes and common-step conservation, followed by M6 composition. M5 here supplies the precise single-step interface and its direct accepted-residual specializations. It does not declare M6 complete or add a new M6 contract, multi-step evolution, solver implementation or source correspondence.

## Selected discrete ODE and state conventions

Keep gamma common and greater than 1 in physical uses. The current nodal values U_i are the accepted Conservative 3 states; q_i = encode(U_i) is the accepted five-vector (density, three momentum densities, total energy density). Volume-weighted q is conserved amount. Do not replace energy density by specific energy.

Use a fixed stationary mesh M, its actual accepted dualVolume v_i, actual interfaces, one accepted Roe transfer per canonical edge with the assembled integrated edgeArea, and the actual M4 patchTransfer with outward boundaryArea. Kinds and exterior data remain functions of actual primal-face IDs. Evaluate every interior/boundary transfer at the old state U and the prescribed exterior data supplied for this step. No in-place nodal refresh, stage reevaluation, extra area factor, pressure interpolation or wall projection is introduced.

The selected semidiscrete baseline is **lumped**:

    v_i dq_i/dt = -R_i(U),       R_i = meshResidual M gamma k V U i.

This makes an explicit mass-matrix choice: identity after factoring the diagonal fixed dual volumes. It does not solve a consistent node-centered mass matrix. Blazek's Eq. (6.4) retains a mass matrix and discusses when it may be lumped; choosing lumping here for the node-centered one-step baseline is a project decision for scientific review. Do not present it as an equivalence theorem with the book's consistent-mass unsteady method or as a proved PDE temporal-accuracy result.

The outgoing residual fixes the **minus sign** in the update. The proposed single explicit Euler correction is

    q_i^+ = q_i - (tau_i / v_i) • R_i(U),
    U_i^+ = decode(q_i^+).

A common physical step uses tau_i = dt for every used node. The physical domain is dt >= 0; dt = 0 is identity. Local nonnegative tau_i are separately supported as a pseudo-time algebraic step and are not represented as one common physical time. No time-step estimator or CFL upper bound is chosen in M5. Raw algebraic lemmas may quantify over real steps with weaker nonzero-volume hypotheses, with their physical specialization stated separately.

## Positive volumes and unused allocated nodes

For abstract update algebra, require v_i > 0 at every updated node; helpers may use v_i != 0. Do not derive cancellation of v_i against 1/v_i without that hypothesis.

For the concrete MeshData, use the actual predicate M.Used i. The accepted dualVolume_pos proves positivity for each used node; dualVolume_unused proves v_i = 0 otherwise. Neither a replacement volume field nor an input positivity certificate should substitute for this concrete derivation. Conforming is needed where accepted metric closure is consumed; volume positivity itself uses its actual accepted theorem's domain.

Define the concrete nodal step by **branching on M.Used**: on a used node apply the quotient update above; otherwise return U_i unchanged without evaluating a quotient. Initial unused states and their local steps are arbitrary. Derive that no actual edge endpoint or boundary owner is unused and hence R_i = 0 at every unused node. Show that the weighted sum over all allocated nodes equals the sum over used nodes, because unused volumes are zero. A used zero/negative-volume input is outside the abstract physical domain; do not silently skip it or use Lean's total division to justify a physical update.

## Common-step balance on the actual selected boundary rule

Let Q(U) = sum_i v_i • encode(U_i), with the same fixed volumes before and after. Derive the pointwise used-node amount identity

    v_i • (encode(U_i^+) - encode(U_i)) = -tau_i • R_i(U).

For a common dt, derive from the actual accepted M4 mesh_global_balance

    Q(U^+) = Q(U) - dt • sum_b patchTransfer M gamma k V U b.

Prove the vector identity and expose its density, energy and three momentum components. Both traction kinds contribute zero mass/energy. Their momentum contribution remains the actual OLD owner's p_gamma(U_owner) T_b, alongside prescribed-exterior Roe momentum. Do not assert general zero total momentum or erase pressure forces. A zero relevant boundary sum implies conservation of that component; all-wall/symmetry boundaries imply common-step total mass/energy conservation, while their pressure momentum generally remains.

Finite algebraic helpers can be stronger than the physical domain. Public physical specializations must make initial admissibility on used nodes and exterior admissibility on prescribed faces explicit, with no irrelevant exterior hypothesis on traction faces. Do not assume or conclude that the new states are admissible as part of the balance theorem. The boundary transfer is evaluated at U, not at U^+.

## Unequal local steps: exact qualified balance

Use the same accepted incidence convention: tail contributes +f_e, head contributes -f_e, and a boundary record contributes g_b to its owner. With tau_i varying, derive

    Q(U^+) - Q(U)
      = -sum_e (tau_tail(e) - tau_head(e)) • f_e
        -sum_b tau_owner(b) • g_b,

where f is the actual accepted interior Roe transfer and g the actual constructed M4 boundary transfer. This follows by weighted finite incidence, not by assuming cancellation. Setting all used steps to dt must recover the common-step theorem. A weaker graph condition tau_tail = tau_head also eliminates the edge term but still leaves owner-weighted boundary terms; it does not supply a common physical time.

Do not call unequal-step integration physically globally conservative in general. The unweighted residual sum still satisfies the accepted M4 boundary balance, but it is not the weighted update sum. A sum with weights v_i/tau_i could describe a different algebraic quantity only when every denominator is nonzero; it is not the physical amount Q and is not a target for this proposal.

## Qualified compatible-common-state preservation and transport

For one common admissible state U on the allocated nodes, retain M.Conforming, gamma > 1, zero dot(U.momentum,T_b) on each wall/symmetry patch and V_b = U on prescribed faces. Use the actual accepted mesh_constant_state, then the update's zero-residual identity, to prove U_i^+ = U at every used node for any nonnegative local steps. Unused nodes are held by definition. No input residual-zero certificate or new closure assumption should replace the concrete accepted theorem. This is preservation of this compatible common state; it does not show that an arbitrary wall state gains or retains tangency after an update.

The update commutes with finite node relabeling when the state, residual, used-node predicate, volume and local-step data are all transported. Instantiate the residual part with accepted M4 transport, including kinds, exterior data, ownership, edges and areas. Common-step Q transforms by the corresponding finite sum reindexing. As in M4, this is transport of already constructed geometry/interface values; no naturality claim about rebuilding a renumbered mesh constructor is added.

## Proposed result obligations

These IDs are proposed, **not active or frozen**. There is one implementation checkpoint for this small milestone, followed by independent M5 implementation review. Any mandatory proposal amendment must be resolved before freezing IDs, exact definitions/domains and bindings.

| ID | Proposed obligation | Downstream use |
| --- | --- | --- |
| M5-U | Actual minus-sign encode/decode update; zero-step/zero-residual identities; positive-volume pointwise amount identity; residual evaluated at old state. | Exact single-step interface. |
| M5-V | Concrete used-node volume positivity, unused volume/residual zero and hold branch; all-node/used-node amount equality without division on unused nodes. | Correct concrete domain. |
| M5-B | Common-step vector/component amount balance composed with actual M4 transfer; traction mass/energy exclusion and retained pressure momentum. | M6 conservation interface. |
| M5-L | Exact local-step edge-defect/owner-weighted boundary balance; common-step specialization and actual unequal-step nonconservation control. | Qualified pseudo-time limits. |
| M5-C | Concrete compatible-common-state preservation using accepted derived closure and actual selected transfers; actual incompatible/nontrivial update controls. | Stationary consistency of the step. |
| M5-O | Update/amount transport with used mask, fixed volumes, steps and fully transported actual M4 residual data. | Representation independence. |

Proposed files are CFDLean/Time/ExplicitEuler.lean and a compact control file only if needed, plus the umbrella export, expected-type examples, cumulative bindings/guards/audit and source map. Reuse accepted scalar/vector arithmetic and actual encode/decode rather than introducing a new state representation. No new library dependency, compiler change or executable solver is needed.

## Exact preparation controls and required future Lean checks

reviews/M5/PreparationChecks.py uses Fraction arithmetic and reuses the existing M4 preparation evaluator/accepted standard-tetrahedron geometry. It is not a Lean implementation or proof, and assumes accepted equal-state Roe consistency when evaluating common-state interior transfers. It checks:

1. Minus sign, nonzero-volume cancellation, dt=0, zero residual, used zero-volume exclusion, unused-node volume zero and hold behavior. Add a genuinely unused allocated node with arbitrary state/step; no quotient is evaluated there.
2. Standard-tetrahedron v_i = 1/24. At gamma=2 and common U=(1,0,0,1,3/2), all faces use wall traction. Actual residuals are r,0,0,-r with r=(1/6,0,0,1/6,5/12). A common step preserves Q. Local steps 1/48 except node 3 at 1/24 give Q(U^+)-Q(U)=(1/288,0,0,1/288,5/576), although the unweighted boundary sum is zero. Both initial and resulting states are admissible. The old common state is not tangent to every wall; no common-state preservation claim applies. Check the actual interior/owner-weighted boundary formula as well as this nonzero amount vector.
3. Actual mixed wall/open tangential moving common states and all-wall rest states are unchanged, even under different local steps. Future kernel checks must also instantiate accepted oblique and conforming two-cell geometry, including the actual mixed-kind corner, without substituting arbitrary geometry or residuals.
4. For a positivity limit control, set the common old state to gamma=2, rho=1, momentum=0, energy=3 (pressure 3). Use the actual standard mixed boundary, with a resting pressure-1 exterior state on just open primal face 1 and matching pressure-3 data on the other prescribed faces. The wall rest state is tangent and all input/exterior states are admissible. The actual owner-0 residual is (1/12,1/6,0,0,1/3). At dt=1 and v_0=1/24 the updated state is (-1,-4,0,0,-5), with negative density. This rules out unconditional update positivity; no CFL condition was supplied, so it refutes no separately qualified CFL theorem.
5. Future kernel expected-type checks must expose the actual accepted meshResidual/patchTransfer, actual volume field and Used predicate, generic common/local steps and nontrivial relabeling with nonconstant volumes/steps/data. Protect all 182 accepted examples as an exact prefix. Project preparation arithmetic does not establish any of these proposed kernel results.

## Source traceability and scientific choices

Use only the already approved J. Blazek first edition (2001), local SHA-256 `c37225f646c5e237a20361db0979cf09218de9800dc9a85448314e7646758fc5`, and accepted M1-M4. The local original was rehashed, the complete relevant pages extracted, and PDF pages 204, 205 and 322 rendered and visually inspected for this proposal.

| Source locator | Use and qualification |
| --- | --- |
| Chapter 6, printed p. 181 / PDF p. 204, Eq. (6.1). | Stationary finite-volume method-of-lines equation with outgoing-residual minus sign, volume and a mass matrix. |
| Same page, Eqs. (6.2)-(6.3). | General stationary-grid time correction and definition of the new-minus-old increment. |
| Section 6.1, printed p. 182 / PDF p. 205, Eq. (6.4). | Basic explicit correction with the mass matrix retained. Identity/lumped mass is the explicit project choice here, not a derived equivalence to consistent-mass node-centered dynamics. |
| Same page, Eq. (6.5), one stage with coefficient 1. | Supports the chosen single-stage lumped correction; multistage coefficients, higher-order time accuracy and acceleration algorithms are excluded. |
| Section 9.1, printed p. 299 / PDF p. 322. | Local steps accelerate steady convergence and change the physical-time interpretation. The exact edge-defect theorem is a project finite-incidence derivation, not a quotation of a book conservation theorem. |
| Accepted M1-M4 at immutable pins; M2-proposal.md original M5/M6 roadmap. | Actual conserved-coordinate layout, Roe/boundary residual, geometry/positive volumes, balance and qualified common states. |

No new source/edition, publisher correction or SU2 definition is imported. No new author/publisher errata search was performed for these temporal pages; the visual/source check is not an exhaustive errata determination. The mass-lumping, unused-node hold, common/local step domains and exact finite-sum statements are project scientific decisions submitted for independent review.

## Review and implementation sequence

1. Record both independent M4 verdicts and original evidence. Advance and verify inheritance protection to all 156 accepted bindings/types and accepted mathematical sources, keeping the separate full-M3 pin.
2. Independently review this exact proposal, especially lumped versus consistent mass, the minus sign, positive used volumes, unused-node policy, common/local-step distinction, physical initial domains, exact controls and M5/M6 boundary. Resolve mandatory findings. No M5 Lean code is introduced at this checkpoint.
3. Under standing user authorization, freeze the reviewed scientific/representation/domain choices and exact six-ID layout separately before implementation. Add active result bindings only as the implementation is delivered. A reviewer recommendation is not a new implementation acceptance.
4. Implement the small single-step milestone using accepted definitions. Run the full owning-module/transitive audit, expected-type checks and all guard fixtures. Require only propext, Classical.choice and Quot.sound and no reachable unsafe declaration, with compiler non-roots/metadata still visible.
5. Every mathematical implementation checkpoint needs a new clean pinned-source replay with both caches disabled, nine fresh pins, local widget compilation, source checksum preservation and five deterministic output comparisons. This proposal/checker-only checkpoint does not claim another fresh source replay. Request an independent M5 verdict before the next scientific milestone.

Excluded: time-step/CFL estimator, linear/nonlinear stability or convergence/temporal-order proof, multi-step trajectory, automatic state admissibility, entropy inequality/fix, positivity limiter or fallback, evolved wall tangency/projection, full symmetry evolution, characteristic/nonreflecting update, source/viscous terms, moving/adaptive volumes, Runge-Kutta/implicit/dual-time scheme, floating-point implementation and SU2 source correspondence.
