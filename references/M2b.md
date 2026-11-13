# M2b provenance and review map

Worker implementation of approved M2-A/R/L, extending independently accepted M2-J at 3788009. The scientific contract remains specifications/M2.md at approval revision 79fd2a0, byte-for-byte. Independent M2b acceptance is pending.

## Source and definitions

The frozen contract's original Roe (1981) parameter vector and quadratic midpoint construction are implemented in CFDLean/Flux/Roe/Linearization.lean. The normal extension, exact identities, Fréchet derivatives and continuity proofs are project derivations. The existing reference collection and approved Roe/LeVeque/Blazek/Toro locators are reused; no new scientific source or numerical variant is introduced. The approved order is C B⁻¹, with no inverse of C required.

Averages.lean defines square-root density weights, averaged velocity/enthalpy and sound speed. Coordinates remain (density, three momenta, energy per volume). Its variance identity derives from the accepted M1 pressure. Strict sound-speed positivity requires common gamma > 1 and both M1-admissible endpoints; no positivity of an update or intermediate state is claimed.

Linearization.lean defines the explicit J(u,H,n), built from continuous linear coordinate projections. operator_physical identifies it with the accepted M2a physical derivative formula. roeMatrix substitutes only the approved square-root averages; no independently chosen averaged density is introduced. The parameter maps recover the actual state and M1 flux at each endpoint. B and C are proved to be their Fréchet derivatives, and the quadratic midpoint identities are exact. An explicit two-sided inverse proves B invertible for gamma and z0 nonzero. Physical hypotheses imply both. The proved product roeMatrix B = C and the midpoint jumps yield the secant identity and C B⁻¹ representation.

The secant identity holds for every fixed direction, including a zero vector. Its integrated form uses the accepted Euclidean area and unit normal for nonzero faces; the raw zero-area case is already included without normalization. Fixed-parameter joint continuity is in the normed space of continuous linear operators. Together with diagonal equality and the actual M2a derivative theorem, this proves the full equal-state limiting condition, not just diagonal formula equality. Continuity already holds on the open positive-density pair domain, stronger than the required admissible-pair restriction.

## Declaration and type review

specifications/M2-results.json binds every claimed J/A/R/L result to qualified theorem names. The eight accepted J bindings, their complete types and the accepted mathematical sources are compared to immutable revision 3788009 before accepting a new audit. StatementChecks.lean elaborates the inherited expected types plus explicit M2b interfaces, naming the M1 flux directly in endpoint/secant/derivative checks. Exact stationary-contact and stationary-shear sound-speed examples are included.

The generated evidence/bindings-diff.patch shows the complete binding-file diff from the accepted M2a revision. evidence/binding-type-diff.json lists the accepted and current types for every active promised declaration; null means newly added and awaiting independent acceptance. evidence/inherited-types.json records the eight unchanged J types. New supporting declarations receive the same full module/axiom audit but do not acquire scientific acceptance merely by being inventoried.

A new frozen candidate must pass scripts/reproduce.sh in a fresh clean checkout without .lake. The procedure compares regenerated verification.json, kernel-inventory.log and binding/type comparison outputs with the exact candidate byte for byte, while retaining the different cold-build transcript. Worker reproduction and typed checks are submitted evidence, not an independent review decision.

## Remaining obligations

M2-E/D/O and M2-F1/F2/F3/F4/C remain deferred. No spectral projectors, complete eigenbasis, absolute-speed dissipation or final numerical flux is implemented here. The combined M2a/M2b candidate requires independent review. Later mesh assembly and SU2 correspondence remain separate workstreams.
