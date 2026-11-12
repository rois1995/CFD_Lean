# Original M0 proposal and approval record

## Provenance and limits

This is a transcription of relevant excerpts from the original exchange visible in the project's continuing conversation. It is supplied by the implementation worker, not a platform-authenticated chat export or a new approval by the worker. The scientific approver can compare it with the original conversation. The project originally recorded the exchange date as 2026-11-12; exact message timestamps are not exposed in the available conversation view. No new ratification date is invented here.

The independent reviewer lacked this exchange when reviewing commit `0a88e36b3810cd5adc3881db526ca8a35f81afbb`. This record supplies the previously missing proposal and replies. Whether it closes the approval-evidence condition remains for the reviewer/scientific approver to confirm.

## Proposal excerpts preceding implementation

The assistant presented the inventory and these source choices:

- Blazek, *Computational Fluid Dynamics: Principles and Applications*, first edition, 2001.
- Roe, *Approximate Riemann Solvers, Parameter Vectors, and Difference Schemes*, 1981.
- Barth and Jespersen, *The Design and Application of Upwind Schemes on Unstructured Meshes*, AIAA 89-0366, 1989.
- Toro, *Riemann Solvers and Numerical Methods for Fluid Dynamics*, third edition, 2009.
- LeVeque, *Finite Volume Methods for Hyperbolic Problems*, first printed 2002, local electronic copy marked ©2004.
- Giles, AIAA 1989-1942, reserved for a separate boundary-method choice.

The following mathematical choices were proposed (verbatim excerpt):

> - **Physics:** stationary-mesh, inviscid Euler equations for a calorically perfect gas, with fixed γ > 1.
> - **Dimension:** general finite spatial dimension for state and physical flux; begin Roe's explicit eigenstructure in 3D.
> - **State:** U = (ρ, m, ℰ), where ℰ is energy **per volume**. Require ρ > 0 and p = (γ − 1)(ℰ − ‖m‖²/(2ρ)) > 0.
> - **Normals:** use an oriented area vector S. Normalize only where required, with S ≠ 0 explicit; define the physical flux also at S = 0.
> - **Roe variant:** original Roe dissipation using absolute characteristic speeds first. Any entropy fix receives a separate definition and approval.
> - **Geometry:** median-dual node-centered FVM, with an abstract oriented incidence/assembly interface. Clearly separate assumed closure identities from geometry-derived results.
> - **Boundaries:** begin with the physical slip-wall condition and direct pressure flux. Approve reflected-state, projected-update and characteristic algorithms separately.
> - **Arithmetic:** exact real mathematics initially. Floating-point correspondence is a later, separate obligation.

Typography and mathematical delimiters in the excerpt above are normalized for this Markdown file; the wording and proposed choices are retained.

The proposed M1 results were conversion inverses on admissible states, admissibility preservation, physical-flux linearity in the area vector and orientation reversal, and an explicit admissible-state witness. The proposal named γ > 1, positive density/pressure and explicit treatment of zero density/area as key assumptions or limits.

The assistant explicitly proposed:

> **Recommended first implementation milestone: M1 only.** Its scope is the core state/ideal-gas/physical-flux modules, library exports, source-to-statement records and integrity checks.

The architecture proposal was an independent repository at `/media/rausa/4TB/SU2_Versions/CFD_Lean`, remote `rois1995/CFD_Lean`, one Lake package, separate working/build trees from SU2, and no SU2 dependency. Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` were proposed for interoperability. Books and papers would remain outside Git.

## Explicit approval request and user response

The assistant asked the user to approve or amend:

1. The source/edition choices above, with Giles reserved for a separate boundary choice.
2. The method defaults, with separate entropy-fix and boundary-algorithm approvals.
3. M1 and its proposed statements as the first implementation milestone.
4. The independent architecture and Lean/mathlib pins.
5. Creation of `rois1995/CFD_Lean`, including the visibility choice.

The user's next reply, before implementation, was exactly:

> Approve

The assistant then stated that it would start M1 and keep the repository local pending a visibility choice. It asked:

> Should the approved GitHub repository rois1995/CFD_Lean be private or public? I'll finish and verify M1 locally while you choose.

The user's answer was exactly:

> Private (recommended)

M1 was subsequently implemented, checked, committed and pushed privately as `0a88e36b3810cd5adc3881db526ca8a35f81afbb`. The user later requested the reviewer handoff and reference ZIPs and supplied the independent review bundle.

## Relation to the frozen candidate

This record documents approval of the proposal and first-milestone scope. It does not claim that every line of the later M1 contract had already been individually approved, that implementation success constitutes scientific acceptance, or that later numerical algorithms are authorized as reviewed mathematical contracts.

The external review of the frozen commit recommends retaining its mathematical statements and gives **accept with conditions**. The current follow-up supplies reproducibility instructions and this approval record; independent confirmation of condition closure is still required.
