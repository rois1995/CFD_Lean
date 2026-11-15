# Independent M5 scientific-proposal review

**Verdict: RECOMMEND IMPLEMENTATION. No mandatory amendments or blockers.**

This recommendation covers the proposed M5-U/V/B/L/C/O scope at **3dcb73dce26149673f6669725fc3b371bd95defd**, tree **a8e2948c2d5aa1b7478227d17a0e0ed20b87e28f**. Handoff checkpoint: **704ddbf217571c66ea60ca05292b70071bd3183a**. Accepted full-M4 mathematics remains **3a586a42546cba1784cc79269e3f9d1c5d843f0c**; accepted M3 remains **e2ea538b8da38c01c098ef28a3ea31030d90c6bb**.

This is a scientific proposal recommendation. There is no M5 Lean implementation, frozen M5 contract or active M5 theorem binding to accept. The exact contract freeze and later independent implementation acceptance remain separate checkpoints. No repository was modified by this reviewer; no new milestone implementation or message to another agent was initiated.

## Findings by proposed obligation

All locators refer to specifications/M5-proposal.md at the exact candidate.

| ID | Locators | Assessment |
| --- | --- | --- |
| M5-U | Lines 15-30, 78 | Correct conserved-coordinate layout, outgoing minus sign, simultaneous old-state evaluation and one volume division. Fixed volumes and prescribed data are fixed for this step. Zero-step and zero-residual identities are appropriate. |
| M5-V | Lines 34-38, 79, 91 | Positive used-node volumes derive from accepted geometry. Unused allocated nodes are explicitly held, have zero volume and must have zero actual residual. This avoids using total division to interpret a zero-volume physical update. |
| M5-B | Lines 42-52, 80 | The common-step conserved-amount identity follows from the actual accepted M4 boundary balance. Component specializations correctly remove traction mass/energy and retain old-owner pressure momentum. |
| M5-L | Lines 56-64, 81, 92 | The local-step edge defect has the correct sign and weighting. Equal steps recover common-step balance. Unequal steps generally change the physical conserved amount even with zero unweighted boundary sum. |
| M5-C | Lines 68, 82, 93-94 | Compatible common-state preservation uses the actual accepted geometric closure and boundary conditions. It provides no general evolved tangency or update-admissibility result. Both incompatible controls are mathematically meaningful. |
| M5-O | Lines 70, 83, 95 | Transport includes the used predicate, volumes, steps, states and fully constructed M4 data. Finite-sum amount reindexing is appropriate. The constructor-naturality limitation is explicit. |

## Mass matrix, scientific basis and scope

The selected mathematical object is the lumped fixed-volume ODE v_i dq_i/dt = -R_i(U), followed by one forward Euler correction. It is a scientifically suitable small baseline for the independent library. With node-centered values on an arbitrary median dual, it must retain the proposal's explicit mass-lumping qualification. Its exact finite balance is meaningful without a theorem identifying these nodal values with consistent-mass unsteady control-volume averages.

I independently checked retrieved first-edition book text for Chapter 6, printed pp.181-182, and Section 9.1, printed p.299. It distinguishes the retained mass matrix from identity substitution, discusses known-state explicit residual evaluation, and assigns local stepping a steady-convergence role. The proposal's lumped baseline is clearly identified as a project choice. It claims no equivalence to consistent-mass node-centered dynamics or PDE temporal-accuracy result. These are appropriate qualifications. The finite-incidence formulas reviewed below are project derivations.

Source-check limit: the approved local PDF with submitted SHA-256 c37225f646c5e237a20361db0979cf09218de9800dc9a85448314e7646758fc5 was not included or available locally to this reviewer. I did not independently rehash that PDF or reproduce the worker's rendered-page inspection. Retrieval supplied first-edition text; attempted PDF screenshots failed. The source-byte hash and original visual inspection remain submitted evidence, while the mathematical formulas and distinctions received independent review.

I also checked the author's public corrections page. Its downloadable correction list is explicitly for the third edition (2015), last updated 8 April 2024. That supplies no automatic first-edition correction, and I applied none. This limited screen does not establish an exhaustive absence of first-edition errata. It introduces no new authoritative basis for a numerical definition.

External source locators used for this review, with no copyrighted pages bundled:

- J. Blazek, Computational Fluid Dynamics: Principles and Applications, first edition, Elsevier, 2001, ISBN 0-08-043009-0. Retrieved primary book text: https://www.academia.edu/3126437/Computational_fluid_dynamics_principles_and_applications, Chapter 6 and Section 9.1. The first-edition text clearly identifies its edition; this does not authenticate the submitted local PDF hash.
- Author's correction register: https://www.cfd-ca.de/bookcorrections.html. Third-edition scope only.

## Independent algebraic review

Write q_i = encode(U_i), R_i for the actual accepted meshResidual and q_i^+ for the proposed updated coordinates. On a used node with v_i nonzero,

    v_i • (q_i^+ - q_i)
      = v_i • (-(tau_i/v_i) • R_i)
      = -tau_i • R_i.

The cancellation uses v_i != 0. Physical positivity supplies this hypothesis. On an unused node, the hold branch and actual zero residual make the corresponding amount identity zero on both sides. No quotient cancellation is needed there.

Summing over all allocated nodes, fixed volumes give

    Q(U^+) - Q(U) = -sum_i tau_i • R_i(U).

For common dt on used nodes, unused residuals vanish, so the right-hand side is -dt times the unweighted residual sum. Accepted CFDLean.Boundary.mesh_global_balance identifies that sum with the actual patchTransfer boundary sum. This proves the proposed common-step formula with its outgoing minus sign. Admissibility and nonnegative steps belong in public physical statements, while this finite algebra itself can have weaker hypotheses. Output admissibility must remain a separate property, as proposed.

For each accepted interior edge e, its two weighted incidence terms are

    tau_tail • f_e + tau_head • (-f_e)
      = (tau_tail - tau_head) • f_e.

Each boundary record contributes tau_owner • g_b. Substitution into the preceding summed update gives exactly the proposed negative edge-defect sum and negative owner-weighted boundary sum. Edge endpoints and owners are used, so a common step on used nodes suffices even when unused-node step values are arbitrary. Equality of steps only along graph edges removes the interior defect; it does not identify disconnected components' clocks or remove the owner weights on their boundaries. The proposal correctly says so.

Mass and energy follow by projecting the same five-vector equation. Both accepted traction kinds have zero corresponding transfers. Momentum keeps p_gamma(U_owner) times the integrated outward area at the old state. No general zero force follows for nonconstant pressures. A new q_i^+ is decoded into a Conservative record; that type conversion alone supplies no positivity theorem.

For M5-C, accepted mesh_constant_state supplies zero actual residual from Conforming geometry, admissibility, gamma>1, per-traction tangency and matching prescribed data. The zero-residual update identity then preserves each used node for any proposed nonnegative local steps; unused nodes are held. This composition does not assume the desired residual theorem as a new premise. It does not evolve arbitrary wall states into tangent ones.

Accepted IsEdge includes a common cell occurrence for each endpoint; Boundary membership includes a node of an actual face. Thus every endpoint and owner is used by construction. The proposed unused-residual theorem is feasible without a new geometric closure certificate. dualVolume_pos and dualVolume_unused have the intended concrete domains; Conforming is needed separately where metric closure is consumed.

Transport is finite pullback of all fields through equivalences. It preserves used/unused branching, volume quotients on used nodes, scalar-vector operations and finite sums. Instantiating accepted M4 residual transport avoids an arbitrary residual-transport certificate. This concerns already constructed interface/geometry data, exactly as the proposal states.

## Exact controls and their interpretation

I ran reviews/M5/PreparationChecks.py and inspected the retained evaluator it imports. It passed. Its Roe helper is a supplementary rational evaluation of the accepted shifted-projector formula, restricted to controls with exact rational square roots. It is not a new scientific authority or proof. Equal-state interior transfers use accepted Roe consistency.

I also independently assembled standard-tetrahedron edge/patch contributions in checks/Rational.py, without importing the worker's evaluator. For the hot/cold resting example, the mean sound speed is 2 and the acoustic polynomial gives |A| times the energy jump equal to (-1,0,0,0,-4); this supplies the specific unequal-state Roe contribution used in that check.

- All-wall normal-flow state: residuals are r,0,0,-r, with r=(1/6,0,0,1/6,5/12). Standard nodal volumes are 1/24. Steps 1/48 except node 3 at 1/24 produce Delta Q=(1/288,0,0,1/288,5/576). The actual weighted edge/boundary formula gives the same vector. Initial and resulting states are admissible. This common initial state is incompatible with some wall tangency conditions, so it contradicts no proposed compatible-common-state theorem.
- Hot rest state with one cold prescribed face: the actual owner-0 residual is (1/12,1/6,0,0,1/3). The minus-sign dt=1 update gives (-1,-4,0,0,-5). All inputs are admissible, but the output density is negative. This disproves unconditional update positivity for the selected algorithm. It says nothing against a future separately qualified CFL theorem.
- The worker's compatible mixed-wall moving and all-wall rest cases remain unchanged with unequal steps, as expected from zero residual.

I additionally ran 300 exact rational cases for generic finite-incidence weighting, nonconstant volume/step/state transport and an unused zero-volume node. These are arithmetic supplements, not Lean theorem acceptance or evidence that arbitrary test states are physical.

The proposed future kernel controls are sufficient and should remain in the frozen contract: actual standard, oblique and conforming two-cell/mixed-corner instances; actual unused allocation and its hold; incompatible update witnesses; and nontrivial transport with nonconstant volumes, steps and data. No substitute geometry or arbitrary supplied residual should replace the requested actual-algorithm instances. These are already proposal obligations, not new amendments.

## Preservation and audit review

The complete offline bundle verified and contains full history. The proposal commit was independently found through the connected private GitHub repository, and its local tree agrees with the handoff metadata. The standalone proposal is byte-identical to the pinned repository file. All four uploaded payload hashes and all eight checkpoint handoff hashes passed.

checks/Preservation.py independently compared the candidate to accepted full M4. Forty-seven accepted mathematical/configuration/specification files are byte-identical, including every mathematical module, root export, Integrity/KernelAudit, the complete StatementChecks.lean, old result maps and compiler/dependency pins. All 375 pre-existing historical archive files checked remain unchanged. No M5 Lean source, active result map or frozen M5 contract exists. references/M4b.md changes only its acceptance-status reporting.

All 156 accepted ordered promises and elaborated statement types are unchanged. Every current accepted_type is present and equal to current_type; the binding-map diff is empty. The complete full-index patch is exactly the checkpoint's Changes_from_Accepted_M4.patch, SHA-256 2928bba44b1336e9f10421d527e8b9612f6a135e6c533de9eec8caa556176dc3. All 28 original M4b review payload hashes and their actual bytes agree with the original independently delivered ZIP. All five archived independent/worker replay outputs agree with accepted M4 Git blobs.

The audit change at scripts/verify.py:11-14 advances the baseline to full M4 while retaining the separate accepted-M3 pin. check_m4_inherited at line 117 checks every accepted result record/stage/ordered binding and type. The added current-stage rollback check closes the M4b-to-M4a rollback route. scripts/test_verify.py:212 exercises all six records, ordered binding changes, every M4 type and rollback. The source-module hash guard automatically includes both accepted Boundary/Assembly files and controls. No new proof route or kernel-audit source is introduced.

## Independently executed checks

Using pinned Lean/Lake 4.19.0 and local artifacts copied from the prior independent M4b fresh-source build, I ran:

    python3 -m unittest discover -s scripts -p test_verify.py
    python3 reviews/M5/PreparationChecks.py
    LAKE_NO_CACHE=1 MATHLIB_NO_CACHE_ON_UPDATE=1 python3 scripts/verify.py
    sha256sum -c evidence/SHA256SUMS

All exited 0. The complete incremental verifier passed the build, all 182 explicit Lean checks, 17 guard fixtures and all nine pinned dependencies. All 64 current source hashes passed. The five regenerated deterministic outputs match the exact proposal candidate, and the mathematical kernel inventory is also byte-identical to accepted M4. No tracked file changed after these checks.

The inventory remains 1,726 records, 988 safe roots and 21,175 reached declarations. Permitted axioms are propext, Classical.choice and Quot.sound, with no reachable unsafe declaration. All 459 unsafe non-roots (421 definitions and 38 compiler axiom records) and 279 metadata-only records remain visible. I also reran the prior reviewer-authored independent dependency traversal and composition checks against this candidate; they exited 0 with the same root/closure/axiom counts. Skipped compiler non-root queries establish no executable correctness claim.

This was an incremental proposal/checker verification, not a new cold source replay. That is appropriate because accepted mathematical sources are unchanged and the prior cold replay is preserved. M5 mathematical implementation must supply a new clean pinned-source replay as already required by the proposal.

## Mandatory findings, optional suggestions and next permitted scope

Mandatory findings: none. No additional user decision is needed for this proposed scope. The existing standing implementation authorization remains active.

One optional traceability improvement is to add the already approved book's Section 3.2, printed p.45, to explain explicitly how a cell-vertex mass matrix relates node values to control-volume averages. This would clarify the existing lumping qualification; it changes no proposed algorithm or theorem. Preserve the edition-specific correction status rather than carrying third-edition corrections into the first edition automatically.

Next, record this exact proposal verdict and freeze its reviewed scientific/domain/representation choices and six-ID layout before implementation. Preserve all 156 accepted bindings/types/sources, contracts and pins. The worker may then implement M5 under standing authorization and return the actual definitions/types, concrete controls, complete audit and fresh-source evidence for independent M5 acceptance. No repeated implementation-approval request is needed.

The original M6 composition milestone remains separate. The direct M4-residual specializations in M5 are appropriate for checking the selected update; they do not constitute an M6 acceptance. Time accuracy, stability/convergence, CFL selection, update positivity/entropy, evolved tangency, nonreflection, moving volumes, implementation arithmetic and SU2 correspondence remain outside this recommendation.
