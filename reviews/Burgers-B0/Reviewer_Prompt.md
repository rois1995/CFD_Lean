# Burgers B0 proposal reviewer prompt

Review `specifications/Burgers-B0-proposal.md` as an architectural and mathematical contract proposal. No Burgers theorem or implementation is accepted by this PR.

Please check the following points independently.

1. **Scope discipline.** Confirm that B0 is only exact-real 1D inviscid Burgers on a periodic uniform cell-average finite-volume mesh with a two-point flux and Forward Euler. Flag any wording that accidentally implies entropy convergence, TVD, CFL stability, positivity, temporal order, floating-point correctness or executable-code refinement.

2. **Flux convention.** Check the Burgers physical flux (f(u)=u^2/2) and selected local Lax--Friedrichs/Rusanov flux
   [
   (f(u_L)+f(u_R))/2 - max(|u_L|,|u_R|)(u_R-u_L)/2.
   ]
   Confirm that the requested consistency theorem is exact.

3. **Finite-volume sign/orientation.** Check
   [
   L_i=-(\widehat f_{i+1/2}-\widehat f_{i-1/2})/\Delta x.
   ]
   Confirm that periodic total-sum cancellation should be flux-generic and independent of flux consistency.

4. **Composition boundary.** Check that constant-state preservation follows from two-point-flux consistency and that Forward Euler should consume a generic zero-RHS or zero-sum theorem rather than prove Burgers-specific identities directly.

5. **Index representation.** Assess whether `ZMod N` with nonzero (N) is a sound first representation for periodic cells in Lean 4.19/Mathlib at the repository's pinned revision. If a different representation makes finite-sum shift proofs materially safer or simpler, recommend it explicitly.

6. **Property packaging.** Assess whether consistency should be stored inside a `NumericalFlux` structure or represented as a separate predicate/certificate. Prefer an architecture that will later accommodate monotonicity, entropy, Lipschitz and order properties without forcing one monolithic structure.

7. **Isolation.** Confirm that the new Burgers modules can be added without modifying the accepted Euler M1--M4 mathematical sources or changing current M5 claims.

Return one of:

- **Recommend implementation without mandatory amendments**
- **Recommend implementation after mandatory amendments**
- **Do not recommend implementation**

List mandatory findings separately from optional architectural suggestions.
