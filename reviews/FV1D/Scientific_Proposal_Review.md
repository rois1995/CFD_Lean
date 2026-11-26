# Independent FV1D scientific proposal review

The repository owner supplied the independent AI review of
`specifications/FV1D-proposal.md` at revision `9dc798766f0e577bbb1d80c929e2044191849827`.

> **Recommend freezing FV1D-B, FV1D-F, FV1D-K and FV1D-C as written. I found no mandatory scientific changes to the four proposed claims.**

The reviewer checked the following points against B0 and M1.

- **FV1D-B.** The negative right-minus-left flux difference followed by Forward Euler gives the proposed
  update, including old-state evaluation, successor order and timestep scaling. The domain includes one cell
  and a zero time step. Positive width suffices.
- **FV1D-F.** The positive unit area in one dimension gives the M1 physical flux. At equal states the
  Rusanov dissipation vanishes. Admissibility and `γ > 1` give the endpoint speed its physical interpretation.
- **FV1D-K.** Both faces on a constant field have the same physical flux. The update preserves the state,
  including at one cell and zero time step.
- **FV1D-C.** Reindexing cancels adjacent incidences and each conserved component inherits the balance.
  Initial admissibility is the specified domain. Neither a CFL restriction nor output positivity is required.

For the three-cell control the reviewer independently obtained sound speeds `(2,1,2/3)`, endpoint speeds
`(3,2,5/3)`, right-face mass fluxes `(−2,3/2,17)`, updated densities and momenta `(35/16,121/32,257/32)`,
and energies `(99/32,249/64,385/64)`. The local control detects a reversed update sign even when the sum is conserved.

The review confines the scientific scope to the exact-real uniform periodic first-order Rusanov and Forward Euler
step. It treats the shared method, distinct coefficient and state types, generic conservation with projections and
additional exact control components as implementation guidance.

> **No mandatory changes. Recommend freezing the four claims at revision `9dc798766f0e577bbb1d80c929e2044191849827` and proceeding to implementation under the repository's standing authorization and normal acceptance workflow.**
