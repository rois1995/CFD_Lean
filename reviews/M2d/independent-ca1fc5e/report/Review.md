# Independent M2d and composed M2 review

**M2d verdict — Accept F1–F4/C. No blocking findings or outstanding acceptance conditions.**

**Full-M2 verdict — Accept all 12 approved result groups at this candidate, preserving accepted M2a/M2b/M2c. No blocking findings or outstanding conditions within the approved exact-real Roe scope.**

Candidate `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`. Checkpoint `b2309641866ec79f137655153c24b37954f98399`. Accepted inherited baseline `6ee9d53e79e0c6f11e75b1b387c21256572d0fcd`. Frozen scientific specification `specifications/M2.md`, approved revision `79fd2a03d7b15325c56a88ec83991b4fb4f498bb`.

## Mathematical findings

Declaration names below have prefix `CFDLean.Roe` and refer to `CFDLean/Flux/Roe/Flux.lean` at the candidate.

| Obligation | Finding and references |
| --- | --- |
| Definition and domain | `roeFluxCoordinates` (11–16) returns zero explicitly when S=0. Otherwise it uses half the sum of the actual M1 integrated physical fluxes, minus area(S)/2 times the accepted M2c absolute-speed operator evaluated at the Euclidean unit normal and applied to R-L. `numericalFlux` (18–19) exposes this through the accepted Conservative/coordinate chart. There is one area factor on dissipation; the central term already contains area. The construction uses the original Roe absolute speeds, without entropy corrections or fallback. The physically justified domain is common gamma>1 and admissible endpoints. Algebraic evaluation outside it uses Lean's total real arithmetic and carries no additional physical claim. |
| F1 | `roeFluxCoordinates_consistency` (85) cancels the identical-state jump and uses linearity of D. The zero-area branch agrees with M1's zero physical flux. `numericalFlux_consistency` (136) returns the actual M1 physicalFlux after encode/decode round trips. Its raw-state theorem is stronger than the approved physical-domain theorem. |
| F2 | `roeFluxCoordinates_reverse` (94) combines M1 reversal with endpoint symmetry and normal-reversal invariance of the exact same dissipation operator, including the reversed R-L jump. `numericalFlux_reverse` (141) negates density-transfer, all three momentum-transfer components and energy-transfer. Zero area is handled explicitly. |
| F3 | `area_scale` (33) uses sqrt(sum of component squares), and `unitNormal_scale` (38) cancels a positive scale only after proving its nonzero factors. `roeFluxCoordinates_scale` (107) treats a=0 and S=0 separately. `numericalFlux_zero` (132) and `numericalFlux_scale` (147) give the specified zero branch and homogeneous scaling for a>=0 on all output components. This is positive homogeneity, with no assertion of arbitrary area-vector additivity. |
| F4 | `dissipation_upwind_left/right` (176,189) derive all speed signs from positive sound speed and q>=c or q<=-c. `dissipation_of_nonnegative/nonpositive` (153,164) reduce D to plus/minus the accepted Roe operator using spectral reconstruction. `roeFluxCoordinates_upwind_left/right` (202,218) then apply the inherited integrated secant identity. `numericalFlux_upwind_left/right` (234,243) return the actual left/right M1 physicalFlux. Their assumptions retain both admissible endpoints, gamma>1 and nonzero S. Inequalities are non-strict, so sonic equality is included. Neither secant nor the desired upwind conclusion is inserted as a premise. |
| C | `witnessLeft/Right` (272–273) are formed by the accepted primitive conversion at gamma=2, rho=1, p=1/2, velocities -2 and +2. `witnessIntermediate` (275) is left plus the actual minus-projector action on R-L, using the same projector as D. `witness_averages` (287) proves ubar=0, Hbar=3, cbar²=3. `witness_intermediate_coordinates` (296) proves the full vector (1-2/sqrt(3),0,0,0,5/2-2sqrt(3)). `positivity_counterexample` (314) proves endpoint admissibility, positive averaged sound square and negative intermediate density. Since the wave speeds are -sqrt(3),0,+sqrt(3), this is a genuine intermediate vector of the approximate Riemann fan. It refutes unconditional intermediate-state positivity. No particular finite-volume step or CFL-dependent update failure is claimed. |

## Preservation and checker findings

The independent comparison against accepted M2c found every accepted mathematical definition/proof file unchanged, together with Integrity.lean, KernelAudit.lean, the Lean toolchain, Lake configuration/manifest and M1/M2 specifications. The import-only umbrella exports the new flux module. All seven inherited result records J/A/R/L/E/D/O, including their ordered qualified bindings and stages, are preserved. All 58 elaborated theorem types agree.

The full comparison has 66 entries, with precisely eight null accepted types for the new bindings. All 12 approved result IDs are populated, with no deferred M2 result. An independently generated full-index Git diff of specifications/M2-results.json and evidence/verification.json matches reviews/M2d/bindings-and-types.patch at the checkpoint byte for byte.

The inherited checker continues to derive every active group from the immutable baseline contract, now pinned to M2c. It checks full inherited result records and each theorem type, and checks accepted mathematical source hashes before the build. The regression fixture covers binding replacements, stage changes and weakened types in all seven groups. KernelAudit.lean is unchanged from accepted M2c and inventories generated declarations by owning module, with safe-root closure checks. No names are hidden to evade the permitted-axiom policy.

StatementChecks.lean retains the prior 41 examples and adds 15. These check the literal public flux formula, public F1–F4/C types, and actual M1 primitive-conversion cases for moving/oblique equal states, stationary contact/shear and both sonic upwind directions. The two-state sonic examples have different densities, so their branch checks do not collapse merely to equal-state consistency. The example count is supporting coverage information.

## Composition and full-M2 scope

The new code consumes the same accepted operator through each interface. M1 physical flux and chart feed M2-J's physical derivative. M2-A/R/L give admissible Roe parameters, the actual integrated secant identity and the physical derivative limit. M2-E/D/O give the complete spectral decomposition, basis-independent absolute-speed action and signed orientation results. The public numerical flux applies that operator to the same conservative R-L jump. F1–F4 then prove consistency, interface reversal, area behavior and all-wave upwinding of this concrete definition. The witness documents a genuine limitation of the same spectral method.

This closes the approved M2 obligations for the original 3-D exact-real ideal-gas Roe interface method. A full-M2 decision covers this mathematical scope. It supplies an interface for subsequent geometry/residual reasoning. Global mesh conservation still needs paired incidence and assembly, and constant-state preservation needs geometric closure and boundary compatibility. Entropy stability, admissibility of updates, floating-point execution, time integration, boundary algorithms and SU2 correspondence remain outside M2.

## Next steps

Record the separate M2d and complete-M2 decisions at the exact candidate and preserve the independent replay/evaluation evidence. Pin this revision for any approved downstream use. Before starting M3, obtain the next-stage scientific/repository decision required by the current plan. Its proposal can consume the accepted signed interface-reversal and consistency contracts to formulate residual conservation and geometric closure assumptions. This review changes no approved method and authorizes no new milestone implementation.

## Independent fresh-source reproduction

The authenticated candidate and checkpoint trees were reconstructed and matched their Git tree hashes `860dafd062db60ef3f22d31989a534a8739d8d43` and `a87f70c2edabf7eb5b418f3eefe50af513f18eda`. Historical accepted and approved objects were supplied to the isolated Git repository for the inherited guards. Starting at the clean detached candidate without .lake, I ran the submitted script unchanged with the previously verified official Lean/Lake 4.19.0 toolchain:

```bash
bash scripts/reproduce.sh ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1 ../replay
```

The procedure exited 0. All nine dependency source revisions were fetched afresh and checked. Both binary-cache controls were enabled. Pinned ProofWidgets JavaScript assets were built locally. All 32 source checksum entries passed before and after regeneration. The cold build succeeded, nine checker fixtures passed, and 56 explicit Lean examples elaborated with warnings treated as errors. The only tracked difference after replay was evidence/build.log. All five deterministic outputs matched both the immutable candidate and the checkpoint archive byte for byte: verification.json, kernel-inventory.log, inherited-types.json, bindings-diff.patch and binding-type-diff.json. Checkpoint archive checksums also passed independently.

The reproduced audit inventories 507 qualified declarations, all 66 promised bindings, all 58 inherited types, and no deferred result IDs. A separately implemented reviewer traversal follows types, values, inductive constructors and recursor rules. It reached 20,183 declarations from 400 safe roots, finding precisely propext, Classical.choice and Quot.sound and no reachable unsafe declaration. Unsafe compiler/executable auxiliaries and metadata-only names remain visible as non-roots.

Additional reviewer Lean checks combine the actual public flux with the arbitrary complete eigenbasis representation and verify the witness's actual minus-projector definition. Earlier reviewer checks of the integrated secant and M1 derivative/limit also pass. A supplementary witness check initially reached Lean's elaboration-depth limit. The final replayable reviewer file uses an explicit unfolding of witnessIntermediate and sets maxRecDepth to 4096; it passes with no change to repository sources.

Six independent exact symbolic controls differentiate the physical Euler flux, reconstruct Roe projectors, and check secant, consistency, reversal, scaling, zero area and applicable all-wave upwinding. Cases include distinct endpoint states, both sonic equalities and genuinely oblique dissipation. They also reproduce the full same-projector intermediate vector and its negative density. These are supplementary checks alongside the general Lean proofs.

The remote repository was not modified. Replay regeneration and reviewer artifacts reside in an isolated local checkout.
