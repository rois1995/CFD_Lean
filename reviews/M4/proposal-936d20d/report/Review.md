# Independent M4 scientific proposal review

**Verdict — Recommend approval. No blocking scientific finding or mandatory amendment.** Approve the owner-pressure traction rule and prescribed-exterior original Roe rule as two explicit algorithm choices. Andrea's scientific/repository decision and a frozen contract are required before boundary implementation.

Proposal/checker candidate `936d20d32fdd3e18c9f1782a868cbd0378fde7df`, tree `c4953cceb9b3bbc420882d9c31d6494451a29b07`. The attached proposal equals specifications/M4-proposal.md at this revision. Accepted full M3 remains `e2ea538b8da38c01c098ef28a3ea31030d90c6bb`. The handoff's main branch contains later review documentation; its literal full-index comparison was independently matched against this exact candidate.

## Separate algorithm decisions

**Owner-pressure wall/symmetry transfer — recommend approval.** W=(0,p(U)T,0) is a precise inviscid traction contribution on each accepted exterior owner patch. The first conserved component of physicalFlux is m dot T. Its remaining advective terms are proportional to q=(m dot T)/rho. Hence equality with W forces zero normal momentum by comparing mass components, and zero normal momentum makes the advective terms vanish. This establishes the intended iff on the physical domain, with a possible stronger total-real Lean statement. For a nonzero patch, positive density converts the condition into zero normal velocity. The zero-area equality remains valid algebraically.

Mass/energy are zero directly, pressure traction has the outgoing sign, and W is real-linear in T at a fixed owner state. Positive pressure follows from the actual admissibility predicate. These properties suffice for the intended M3 compatibility and component-balance composition. The rule leaves the nodal momentum state untouched, so preservation of tangency after an update remains a separate obligation. Requiring tangency separately at all incident wall/symmetry patches is correct at corners. The symmetry label covers the selected inviscid transfer contribution. Gradient parity, mirrored geometry, residual projection and evolution of a symmetry-invariant solution have separate specifications.

Direct owner sampling is a legitimate explicit project choice within the proposed baseline. It differs locally from the tetrahedral pressure interpolation in Blazek Eq. (8.13), and from a reflected-state Roe wall. The preparation's values 7/4 and 19/4 demonstrate the latter distinction. There is no scientific reason to force these distinct algorithms into one definition. Andrea must approve this sampling choice explicitly.

**Prescribed-exterior original Roe transfer — recommend approval for the defined initial open-boundary baseline.** P(U,V,T) calls the actual accepted numericalFlux with owner U left, prescribed V right and outward integrated T. Accepted M2 consistency, zero-area handling, nonnegative scaling and simultaneous state-swap/normal-reversal immediately supply the proposed local contracts. Full-upwind reductions are valid under the actual two-state Roe-average inequalities qbar>=cbar and qbar<=-cbar, with gamma>1, two admissible endpoints and T nonzero. Sonic equality is retained. They need no interior-Mach-only criterion.

At subsonic/mixed-sign states the method remains the defined Roe expression with prescribed exterior data. The contract makes no characteristic reconstruction, nonreflection, stability, PDE well-posedness or exterior-independent outflow claim. This is suitable for an initial mathematically explicit open-boundary transfer milestone. It does not close a later investigation of characteristic or nonreflecting farfield algorithms. Retain the precise prescribed-exterior Roe name in interfaces and releases so subsequent variants remain identifiable.

## Geometry, composition and proposed theorem list

The selected k and V are functions of actual primal-face identity. Each accepted Boundary record retains its face, owner and area. This supplies same-face kind coherence while allowing mixed-kind corners. Wall/symmetry kinds ignore V; admissibility of V is needed on prescribed-exterior faces. No accepted geometry or incidence is changed, and transfers on differently labeled faces remain separate. Grouping the coplanar triangles already belonging to one accepted owner patch is consistent with the accepted geometry; no nonlinear aggregation across different labels is proposed.

M4-R must use the exact g constructed by these rules in the unchanged M3 residual. The global five-vector sum equals the sum of those exterior transfers. Mass and energy receive only prescribed-exterior contributions, while momentum retains p(U_i)T_b on wall/symmetry patches. The outgoing pressure contribution has the correct sign for the later update convention U_new=U-dt R/V. A general zero momentum balance is not promised.

For common admissible U*, per-wall tangency identifies W with actual physicalFlux. Matching prescribed V=U* identifies P with the same physicalFlux. Every constructed exterior transfer then satisfies the exact accepted M3 compatibility hypothesis on the same B/T records, and derived metric closure gives every residual zero. This is a sufficient criterion. The preparation correctly tests non-tangent wall flow and mismatching exterior data as concrete incompatible cases, using the actual algorithm formula.

The transport requirement is coherent: derive patch kinds/exterior values from face maps in the concrete instance, transport those values together with ownership, areas and state data under finite relabeling, and invoke M3 reindexing. A proof that rebuilding an independently renumbered mesh commutes with its constructor is outside this proposal and is explicitly excluded.

All six proposed IDs are suitable without replacing the statement list:

| ID | Review disposition |
| --- | --- |
| B | Approve exact face-derived kinds/data and one transfer per accepted owner patch. |
| W | Approve zero mass/energy, traction, area laws, positive admissible pressure and tangency-qualified physical equality. |
| P | Approve the exact accepted Roe boundary transfer and the listed two-state spectral reductions. |
| R | Approve actual-rule residual composition and vector/component boundary balances. |
| O | Approve transported transfer/residual identities with kinds and prescribed data included. |
| C | Approve the common-state sufficient compatibility theorem and actual incompatible controls. |

M4a B/W/P and M4b R/O/C form a useful small sequence for later fixed-volume update reasoning. M4-C must continue to state every tangency and data-matching hypothesis. The implementation examples should retain the planned oblique traction, mixed-kind corner, concrete two-cell composition and both sonic directions. The preparation script is a design control; actual accepted-flux Lean checks remain necessary after approval.

## Independent literature assessment

I recovered the supplied Blazek first-edition PDF and independently computed SHA-256 c37225f646c5e237a20361db0979cf09218de9800dc9a85448314e7646758fc5, exactly the approved digest. I read PDF pages 291–302 (printed 268–279) and page 308 (printed 285). I rendered and visually inspected pages 293, 298, 302 and 308.

Printed p.270, Eqs. (8.1)–(8.2), supports the physical tangency qualification and pressure-only flux. The nodal/dual alternatives on pp.272–273 include interpolation and a nodal rule paired with velocity projection. Printed p.275 visibly gives Eq. (8.13), (6p_i+p_j+p_k)/8. The selected owner sampling remains an explicit project derivation/variant. The farfield discussion on pp.277–279 specifies a different characteristic formulation, with state reconstruction formulas and separate inflow/outflow regimes. The proposal correctly avoids claiming that its direct two-state composition implements those formulas. The symmetry discussion on p.285 contains gradient and discrete-enforcement requirements beyond the selected traction contribution.

Source locators and distinctions in the proposal are accurate. No additional authoritative source, edition, erratum or algorithm equivalence is required for these explicitly bounded choices. Selecting another farfield or wall variant later requires its own literature/domain decision.

## Preservation and control findings

Independent comparison with accepted M3 found all mathematical modules, the CFDLean export file, Integrity/KernelAudit, all 112 examples, scientific specifications/result maps and Lean/Lake/dependency pins byte-identical. All 117 accepted elaborated types are preserved. Kernel inventory is byte-identical to accepted M3. The handoff's complete diff matches the independent full-index Git diff.

The checker baseline now pins accepted full M3. Its M3 inherited loop therefore protects all active M3a and M3b parts, including all 51 M3 theorem types, alongside 66 M2 bindings. Metadata/stage layout remain separately frozen. The 13 fixtures passed independently, including the expanded inherited-part tamper controls. These are preservation checks, with no M4 mathematical theorem acceptance.

I independently ran PreparationChecks.py and reproduced its printed controls. Its rational implementation uses gamma=2, conservative energy and the accepted shifted/projector formula. It checks strict/sonic upwind cases in both directions, reversal/scaling, mismatching-exterior mass -1/2, direct/reflected traction, and owner/interpolated pressure differences. The standard-tetrahedron mixed/all-wall controls use accepted equal-state consistency and actual geometry data. A nonzero normal velocity yields the stated 1/6 mass residual at the relevant wall owners. These calculations have the intended scope. They provide no general reflection, accuracy or update result.

## Decisions and next steps

There are no mandatory scientific amendments. For clarity, carry the prescribed-exterior Roe and inviscid symmetry traction names verbatim into the frozen interface, and state any velocity interpretation of dot(m,T)=0 with positive density and nonzero T. The raw zero-area transfer statements remain independent of that interpretation.

Andrea should explicitly approve or amend owner-pressure sampling, prescribed-exterior Roe, face-based labels with unchanged geometry, and the six-ID/two-stage/audit plan. After that approval, freeze the exact algorithms, domains and result map before M4a begins. M4b must compose these selected transfers, followed by a separate full-M4 review. This recommendation authorizes no implementation. No new wall projection, characteristic boundary, time update, positivity/entropy repair or SU2 correspondence is part of the proposal.

## Fresh preservation replay

The bundle's candidate commit/tree was authenticated against the connected repository. Its file hashes and attached proposal snapshot passed independent checks. Earlier build files had been pruned, so I used the optional clean-source procedure to exercise the requested verifier without relying on submitted worker logs. I downloaded the official pinned Lean/Lake 4.19.0 release, used LEAN_NUM_THREADS=8, and ran the unchanged scripts/reproduce.sh on the exact clean detached proposal candidate without .lake. All nine manifest revisions were fetched afresh, both binary-cache controls were enabled and pinned widget JavaScript was built locally.

The procedure exited 0. The fresh build, 13 fixtures, all 112 unchanged Lean examples and all 51 pre/post source checksum entries passed. All five deterministic files matched the proposal candidate byte for byte. The fresh kernel inventory also matched accepted M3 byte for byte, with 1,356 records, 780 safe roots, 20,935 reached declarations, precisely propext/Classical.choice/Quot.sound and no reachable unsafe declaration. Original compiler/metadata classifications are unchanged. All 117 inherited comparisons passed. Only evidence/build.log changed in the tracked checkout.

This independently establishes preservation and reproducibility of the accepted mathematics under the checker update. It grants no M4 mathematical acceptance or implementation authorization. The remote repository and accepted mathematical sources were not modified.
