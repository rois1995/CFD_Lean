# Independent M4a review

**Verdict — Accept M4a B/W/P. No blocking findings or outstanding acceptance conditions. Full M4 remains pending M4b.**

Candidate `37c1e6ee4618b0183135c2795b3aa6ebea2f22d5`, tree `0d31314c056f70957e6afe77b0488d49fdbe2c65`. Handoff checkpoint `a7fcf3be226f77981d49352e7f054310f962eb4f`. Accepted M3 baseline `e2ea538b8da38c01c098ef28a3ea31030d90c6bb`; M4 freeze `0cff4af244b85f4e2071e7bf941d40fdd0a399b5`.

## Scientific findings

The following declarations have prefix CFDLean.Boundary in CFDLean/Boundary/Stationary.lean.

**Selected variants and W.** Kind retains distinct slipWall, inviscidSymmetryTraction and prescribedExteriorRoe constructors. pressureTransfer is exactly (0,pT,0); wallTransfer uses the actual accepted owner pressure. wall_mass, wall_energy and wall_momentum identify every conserved component. wall_zero/add/smul/reverse establish the specified area laws, including arbitrary real scaling for W. wall_pressure_pos consumes actual admissibility. There is no pressure interpolation, ghost reflection, averaged normal, state projection, residual projection or extra area factor. The two traction kinds dispatch to the same rule while retaining different labels.

wall_eq_physical_iff compares the actual encoded M1 physicalFlux with this W. Its forward implication uses the mass component to obtain dot(momentum,T)=0. Its reverse implication cancels the advective terms using exactly that zero scalar. Its raw total-real theorem is stronger than the physical specialization, without narrowing the approved domain. wall_eq_physical_iff_normalVelocity separately requires density>0 and T!=0, proves the normalized dot expression is dot(momentum,T)/(density*area(T)), and uses the nonzero denominator. Zero area remains an algebraic case and supplies no physical normal direction. No update or nodal tangency enforcement is proved.

**P.** prescribedExteriorRoeTransfer is exactly encode(Roe.numericalFlux gamma U V T), with owner left, exterior right and outward integrated area once. prescribed_consistency/zero/scale/reverse inherit the actual accepted M2 identities. Scale is restricted to nonnegative factors. Reversal swaps the states together with T; it does not change the interpretation of a fixed exterior domain by reversing only T. prescribed_upwind_owner and prescribed_upwind_exterior retain gamma>1, admissibility of both endpoints, T!=0 and the actual two-state Roe-average inequality. Their non-strict inequalities include sonic equality. No alternate flux, owner-only Mach classification, characteristic reconstruction, nonreflection or positivity/entropy repair is introduced.

**B and exact geometry.** primalFace reads the actual accepted Boundary occurrence's faceID. patchKind and patchExterior apply face-indexed maps to that same ID. patchKind_coherent and patchExterior_coherent therefore prove same-face coherence. boundary_record_unique and boundary_record_range reuse the actual accepted boundaryKey enumeration and actual interfaces.owner. They neither create replacement patches nor erase their owner/face distinctions. patchTransfer uses that owner state, the selected kind and unchanged boundaryArea. The three dispatch theorems expose the exact W/P branch. Exterior data are ignored by both traction branches; raw dispatch imposes no irrelevant admissibility requirement on those unused values. Physical use of the prescribed branch retains the endpoint hypotheses stated above. Different primal faces at one owner may have different kinds and separate transfers.

## Supporting controls and domain checks

CFDLean/Boundary/Controls.lean defines moving(q,p) with rho=1, momentum=(q,0,0), total energy p+q²/2 at gamma=2. moving_pressure/admissible prove its actual thermodynamic interpretation. moving_averageVelocity/enthalpy/sound give cbar=2 for pressures 1 and 3. The q=+/-3 and +/-2 examples then evaluate the actual accepted P as full five-vectors. Distinct pressures make these genuine unequal-state branch checks.

absolute_axis is derived using accepted Spectral.minus_apply/plus_apply and the proved sound-square/unit-normal relations. It does not define a replacement solver. reflected_roe evaluates the real Roe expression to (0,19/4,0,0,0) for the admissible reflected pair, while the direct wall pressure is 7/4. mismatching_exterior gives (-1/2,2,0,0,-2). owner_sampling_differs independently distinguishes the approved direct sampling from Eq. (8.13)'s weighted pressure. The generic actual-flux signatures and numeric results are checked in StatementChecks.lean, including explicit reflected-pair admissibility.

The oblique owner has rho=2, momentum=(8,-6,2), energy=29 and pressure 3. On T=(3,4,0), normal momentum is zero and W=(0,9,12,0,0), equal to physicalFlux. normal_flow_incompatible supplies the opposite qualification. mixed_corner uses accepted standard-tetrahedron wall/open patches with one owner, different primal-face identities and separate actual transfers on their own areas. It does not conflate same-face kind coherence with equality of transfers across faces.

These are local boundary contracts and controls. M4b's residual/component balances, transported constructed transfers and concrete common-state/two-cell composition remain deferred. Old generic M3 results and these local cases provide dependencies for that work, without replacing it.

## Preservation, scientific freeze and audit

Independent comparisons against accepted full M3 found all accepted mathematical sources, Integrity/KernelAudit, M1/M2/M3 contracts and result maps, compiler and dependency pins unchanged. The import-only umbrella exports the boundary modules. All 117 inherited elaborated types agree, and all 112 prior Lean examples remain an exact prefix. The 140-row comparison contains exactly 23 null accepted types for new B/W/P claims. The handoff's complete full-index diff matches the independent Git diff byte for byte. Historical archived reviewer/worker payloads match their preimplementation approval snapshot, including original pending fields/counts.

M4.md is byte-identical to the reviewed proposal; precision and approval files match the immutable freeze. The checker verifies their hashes/content and approval record against that freeze, with frozen metadata/result-stage layout. B/W/P have 23 active bindings; R/O/C remain empty M4b entries and explicitly deferred. M3 independent acceptance, M4 implementation authorization and M4a theorem acceptance have separate status records. The approval message is preserved as a repository transcription; original platform provenance is not independently authenticated by this review.

KernelAudit.lean is unchanged. It covers declarations by owning module, including Kind and supporting/generated names. The compiler auxiliaries and metadata-only records remain visible as non-roots; skipped non-root axiom queries do not verify executables. The sources introduce no explicit safe axiom, unsafe proof route, custom elaboration budget or disabled linter. Existing M3 scoped algebra budgets are preserved unchanged.

**Next-stage finding, nonblocking for M4a.** Before M4b relies on accepted M4a, freeze all 140 cumulative bindings/types, accepted M4-B/W/P result records/stages and boundary mathematical sources/controls against this candidate. The current inherited baseline protects the 117 prior contracts as required for this submission. Without the extension, a future safe-theorem substitution or boundary-definition change would not be caught by that M3-only baseline. Keep R/O/C separately deferred until their exact statements and proofs are delivered.

## Next permitted work

Record scoped M4a acceptance at this immutable candidate. Under the existing approved two-stage plan, M4b may then compose the selected patchTransfer with the unchanged accepted residual, prove vector/component balances and transported relabeling, and derive the qualified concrete common-state result with actual compatible/incompatible controls, including two-cell and mixed-corner cases. Preserve M4a first as described above. A separate full-M4 verdict follows that review. New boundary variants, projected/time updates, entropy/update-positivity repairs, mixed meshes and SU2 correspondence remain outside this acceptance.

## Independent fresh-source reproduction

The uploaded handoff checksums passed. The Git bundle's exact mathematical commit/tree was authenticated against the connected repository. From a clean detached candidate without .lake, I ran scripts/reproduce.sh unchanged with the official pinned Lean/Lake 4.19.0 release and LEAN_NUM_THREADS=8. All nine manifest-pinned sources were fetched afresh, both binary-cache controls were enabled and pinned widget assets were compiled locally.

The procedure exited 0. The cold build, all 15 checker fixtures and all 153 Lean examples passed. All 58 source checksum entries passed before and after regeneration. All five deterministic outputs matched the frozen candidate Git blobs and the worker checkpoint archive byte for byte. The worker archive hashes also passed independently. Only evidence/build.log differed in the tracked checkout.

The reproduced owning-module inventory has 1,585 records and all 140 promised bindings, with all 117 inherited types checked. It retains 417 unsafe non-roots (381 definitions and 36 compiler axiom records) and 263 metadata-only names. A separate reviewer traversal of types, values, constructors and recursor rules reached 21,075 declarations from 905 safe roots, finding precisely propext, Classical.choice and Quot.sound and no reachable unsafe constant.

The reviewer Lean file passed with warnings treated as errors. Its new examples combine Kind dispatch with local physical-flux compatibility and establish independence of the wall branch from arbitrary exterior data. Earlier reviewer checks of the physical derivative, Roe secant, spectral formula and concrete M3 geometry/composition also pass again. These supplementary checks confer no M4b residual/transport/common-state acceptance.

The remote repository was not modified. Scoped M4a acceptance follows from the independently inspected definitions/statements and reproduced proofs/evidence. The next-stage inheritance extension is a requirement for M4b, with no outstanding condition on the current candidate.
