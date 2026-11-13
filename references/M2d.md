# M2d flux and complete M2 obligation map

Worker implementation of the approved M2-F1/F2/F3/F4/C obligations. M2c is independently accepted at 6ee9d53e79e0c6f11e75b1b387c21256572d0fcd. All 58 inherited J/A/R/L/E/D/O bindings, stages, elaborated types and mathematical sources are frozen against that revision. The scientific contract is specifications/M2.md, unchanged from approval revision 79fd2a03d7b15325c56a88ec83991b4fb4f498bb. M2d and composed M2 acceptance require an independent verdict.

## Flux construction and domain

CFDLean/Flux/Roe/Flux.lean defines roeFluxCoordinates and the public numericalFlux on the accepted Conservative 3 layout through the accepted encode/decode chart. The S=0 branch returns zero before using a unit normal. Otherwise it is half the sum of the two actual M1 integrated physical fluxes minus area(S)/2 times the accepted M2c dissipation at unitNormal(S), applied to the conservative jump R-L. Geometry is explicitly Euclidean, area(S)=sqrt(squareSum S). The central term already contains area; the dissipation contains exactly one area factor.

This reuses the original Roe absolute-speed operator without entropy correction, alternate density average, fallback, tangent choice or changed parameter. The frozen source locators in M2.md apply: Roe 1981 pp. 364–365; Blazek 2001 pp. 106–108 with the entropy correction excluded; Toro 2009 pp. 349–351, particularly (11.29); LeVeque pp. 315–320. No new scientific source or source edition is introduced. The integrated scaling, orientation and counterexample proofs are project derivations from the approved definitions.

Consistency follows from the zero jump. Signed reversal uses M1 physical-flux reversal, accepted state-swap invariance of dissipation and normal-reversal invariance. Scaling first proves area(bS)=b area(S) and preservation of the unit normal for b>0, then handles b=0 and S=0 separately. These algebraic identities actually hold for all raw states and parameters; that stronger type supplies the approved physical-domain statements but assigns no physical meaning to invalid inputs.

For full upwinding the physical hypotheses remain gamma>1, both M1-admissible endpoints and nonzero S. Accepted sound-speed positivity and spectral reconstruction give D=A when all speeds are nonnegative and D=-A when all are nonpositive. The accepted integrated secant identity then gives the actual left/right physical flux. The inequalities q>=c and q<=-c are non-strict: stationary and sonic characteristic speeds remain included. The proof assumes neither the secant conclusion nor the upwind conclusion.

## Positivity witness

witnessLeft and witnessRight are formed by M1 Primitive.toConservative with gamma=2, rho=1, p=1/2 and velocities (-2,0,0), (2,0,0). Their encodings are (1,-2,0,0,5/2) and (1,2,0,0,5/2); both are admissible. The averages are ubar=0, Hbar=3 and cbar²=3.

witnessIntermediate is defined as decode(encode(left)+roeProjector(...,n,0)(encode(right)-encode(left))) with n=(1,0,0). This is the identical minus projector used in dissipation and hence in numericalFlux. Its full encoding is proved to be (1-2/sqrt(3),0,0,0,5/2-2sqrt(3)). The density is strictly negative because 0<sqrt(3)<2. This concerns the approximate Riemann intermediate state; it does not exhibit failure of a particular finite-volume update under a particular CFL bound and does not assert intermediate admissibility.

## Complete result mapping

The machine-readable qualified map is specifications/M2-results.json; every approved ID is populated and no ID remains deferred. All names below are in namespace CFDLean, with Roe names under CFDLean.Roe.

| ID | Qualified declaration map / proof role | Status at this submission |
| --- | --- | --- |
| M2-J | Coordinates round trips, physical-flux Frechet derivative, integrated derivative and admissible-domain openness; 8 names in the result map. | Independently accepted M2a. |
| M2-A | Roe weights/variance/sound positivity and symmetry; 10 names. | Independently accepted M2b. |
| M2-R | Roe parameter maps, midpoint derivatives/jumps, B inverse, C B-inverse and secant; 15 names. | Independently accepted M2b. |
| M2-L | Roe operator continuity, diagonal derivative and equal-state limit; 4 names. | Independently accepted M2b. |
| M2-E | Roe.Spectral sound parameters, cubic, eigenvectors, projector algebra/ranges/ranks, 1+3+1 dimensions and complete/tangent bases; 13 names. | Independently accepted M2c. |
| M2-D | Roe.Spectral.roe_absolute_basis and roe_absolute_eigen. | Independently accepted M2c. |
| M2-O | Roe.Spectral matrix/shift/projector/speed/absolute reversal and state swap; 6 names. | Independently accepted M2c. |
| M2-F1 | Roe.numericalFlux_consistency. | New: same-state flux is the actual M1 physical flux for any S. |
| M2-F2 | Roe.numericalFlux_reverse. | New: swapping endpoints and negating S negates every output component. |
| M2-F3 | Roe.numericalFlux_zero; Roe.numericalFlux_scale. | New: explicit zero branch and nonnegative scaling, including b=0. |
| M2-F4 | Roe.numericalFlux_upwind_left; Roe.numericalFlux_upwind_right. | New: original full upwinding with sonic equality included. |
| M2-C | Roe.witness_intermediate_coordinates; Roe.positivity_counterexample. | New: full intermediate vector and admissible-endpoint/positive-sound/negative-density bundle. |

There are 66 promised bindings: 58 inherited and 8 new. Supporting definitions and lemmas receive the same full owning-module inventory and safe-root dependency traversal. The import-only umbrella exports Flux.lean; accepted mathematical modules, Integrity.lean, KernelAudit.lean, scientific specifications and dependency pins remain unchanged.

## Validation and limits

StatementChecks.lean retains all 41 prior examples and adds explicit public theorem types, the literal integrated flux formula and exact M1 primitive-conversion controls. These cover equal moving and oblique states, stationary contact, moving sonic contact in both orientations, stationary shear, zero area and signed reversal/scaling. The stationary contact/shear controls prove that the actual Roe matrix annihilates the jump and use the accepted absolute-speed eigen-action to remove dissipation. The counterexample checks its same-projector intermediate definition through the proved full vector.

The nine checker fixtures reject inherited binding substitutions, changed stages and weakened types for all seven accepted IDs. The verifier compares all 58 inherited types/source hashes with 6ee9d53, checks all 66 promises and the full axiom/dependency inventory, and verifies all nine dependency pins. A fresh source-only replay of the immutable candidate must pass scripts/reproduce.sh with both binary-cache controls and exact comparison of all five deterministic outputs before the worker handoff is complete.

No M2 scientific obligation is intentionally deferred. Independent M2d/composed-M2 acceptance remains pending. Entropy stability, update positivity, floating-point behavior, mesh assembly, boundary algorithms, time updates and SU2 correspondence are outside the approved M2 scope. M3 requires a separate next-stage decision.
