# Agent A handoff · close M1 and propose M2

**Decision: Accept M1.** The mathematical candidate is `0a88e36b3810cd5adc3881db526ca8a35f81afbb`. Follow-up `180ff1be1aa95d943574efd9c05cd4de320a88b6` closed both conditions. The final acceptance record in this package supersedes the original conditional verdict. Preserve both as dated review history.

## 1. Record the decision

In the existing private `rois1995/CFD_Lean` repository, check whether the final acceptance is already recorded. If needed, add the supplied acceptance record under `reviews/M1/`, update the current status and link it from the README. Distinguish the accepted mathematical revision from its documentation follow-up. Keep the historical report, checksums and logs intact. The machine verifier reports proof checks; the independent decision belongs in the review record. Return the closeout commit and links. The evidence archive in this package is the previously published evidence and does not need reimporting.

## 2. Return a scientific proposal for M2 and await approval

Prepare a reviewable Markdown proposal for the **original three-dimensional Roe flux for the stationary, calorically perfect Euler equations**. Reuse the approved M1 state, pressure, admissibility and oriented physical flux. A deliverable for this stage is a proposed specification, module structure and theorem list. Begin M2 Lean implementation after Andrea approves these statements and any new authoritative references.

Begin the proposal with the numerical flux in the project's notation. Define every symbol and give the units or scaling needed to distinguish a unit-normal flux from an integrated face flux. State how a caller supplies left and right states and which way the area vector points. Then cover the following.

| Proposal item | What the reviewer needs to decide |
|---|---|
| Sources | Use the approved editions and the original Roe (1981) paper. Inspect the actual pages and record section, page and equation locators, assumptions, errata status and any differences in convention. Identify each project derivation. Request approval for additional authoritative sources. The reference collection already established Blazek's first edition (2001), Toro's third edition (2009) and LeVeque's 2002 print edition. |
| Physical flux Jacobian | M1 accepted the physical flux. Its Jacobian remains an obligation from the original brief. Propose the directional Jacobian for a fixed normal, the state domain on which it is the derivative, and its relationship to the equal-state Roe matrix. If deferred to a submilestone, identify exactly which later result depends on it. |
| Two-state linearization | Define the density weighting, averaged velocity and total enthalpy, and the resulting sound speed. Distinguish the physical Jacobian at one state from the Roe matrix built from two states. State the proposed flux-difference identity with matching unit-normal or area scaling on both sides. Show how admissibility gives meaning to every square root and denominator. |
| Eigenstructure and dissipation | Specify the acoustic and repeated convective eigenvalues, and how the absolute-value dissipation operator is constructed. If the representation uses tangential basis vectors, explain how the resulting numerical flux is independent of that choice. Identify expected proof difficulties and a possible split into independently reviewable parts. |
| Orientation and zero area | State equal-state consistency with M1's integrated physical flux and the signed conservation identity obtained by swapping left/right states and reversing the area vector. Specify the zero-area value separately so the interface also handles a degenerate face without normalizing its vector. |
| Limitations and variants | Keep the original absolute-characteristic-speed dissipation identifiable. Give any proposed entropy correction its own definition and approval. Distinguish positivity of the averaged sound-speed square from positivity preservation of a finite-volume update. Record unsupported properties, counterexamples and unresolved proofs explicitly. |

For each proposed theorem, give its mathematical statement, hypotheses, source or derivation, and role in the eventual discrete step. Pair numerical examples with the proof obligations they exercise. Use exact-real Lean proofs as the acceptance evidence for mathematical claims.

**Proof audit.** Include a plan for inventorying qualified declarations from the elaborated project modules, rejecting duplicate audit rows, and comparing the results with the separately approved theorem list. Do this before relying on the verifier at M2 scale. Preserve the tested cache-disabled source-build procedure. At the end of implementation, identify an immutable candidate commit and provide reproducible proof and axiom evidence to an independent reviewer.

## 3. Keep the route to a complete discrete step visible

| Milestone | Interface or result that the next milestone consumes |
|---|---|
| M1 · accepted | Exact-real primitive/conservative states, ideal-gas pressure, admissibility and oriented physical flux. |
| M2 · proposal now | A two-state oriented numerical flux with consistency and reversal theorems, supported by the necessary Jacobian and Roe linearization results. |
| M3 · node-centered spatial discretization | Assemble edge fluxes into dual-control-volume residuals. Derive interior cancellation from incidence and flux reversal. State the geometric closure required for constant-state preservation and identify what the median-dual construction proves. |
| M4 · stationary boundaries | Specify physical slip-wall and symmetry conditions separately from each discrete enforcement. Select and obtain approval for a precise far-field variant before treating it as authoritative. Supply boundary contributions to the residual. |
| M5 · explicit Euler | Use residuals and positive dual volumes in the update. State the global balance with a common time step and identify how unequal local pseudo-time steps change the cancellation argument. |
| M6 · composition | Compose the approved geometry, interior and boundary residuals, and time update into one discrete Euler step. State the inherited assumptions and the resulting conservation or boundary-balance theorem. |

The CFD library remains solver-independent. Use approved literature to determine the method. After review, the separate SU2 project can compare its existing foundations, propose compatibility lemmas and import a pinned revision. Keep SU2 changes and compiled-solver correspondence in that separate workstream.

**Next response to Andrea:** give the M1 closeout commit, the M2 proposal, and the specific decisions needed before implementation. At every future review, return a verdict, identify blocking and nonblocking findings, and say what the agent may do next and what requires Andrea's decision.
