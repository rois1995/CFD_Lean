# Next steps for Andrea and Agent A

**Andrea's decision.** I recommend approving the proposal at 2264bc0. If you agree, send the following instruction to Agent A.

> I approve the original 3D Roe proposal at 2264bc0, including the C B⁻¹ matrix order, the basis-free spectral projectors, all listed theorem obligations and the M2a–M2d sequence. Record this approval, freeze the proposed contract and begin M2a. Preserve the accepted M1 mathematical definitions. Return any substantive change in domain, numerical variant or theorem statement to me for a decision.

**Agent A, after approval:**

1. Bind the approved result IDs to the frozen proposal. When transcribing the formulas, fix the inline math delimiters and the missing backslashes on Delta in line 122. Keep the published proposal identifiable by commit.
2. Start with the coordinate chart and the derivative of the actual M1 flux. Use the Euclidean length √(S·S) for face geometry. In Lean, the default norm on a finite function space is the supremum norm. That coordinate norm can support the derivative topology, but using it for face area would give the wrong normal. For S=(2,3,0), check that the area is √13 and the normalized vector has dot product one with itself.
3. For M2b, prove the parameter maps recover the M1 state and flux at each endpoint, then use the midpoint jump identities and A B = C. Derive invertibility from z₀>0. Prove positive sound speed before dividing by it. At the M2a/M2b checkpoint, return the immutable commit, qualified declarations for J/A/R/L, proof audit and any unresolved goals.
4. In M2c, prove completeness and the ranks 1, 3, 1, followed by the projector identities and basis independence. Include zero convective and zero acoustic speeds in the domain. In M2d define the intermediate state in M2-C directly as U_L + P₋(U_R−U_L). This ties the counterexample to the same projector used in the flux and removes any dependence on wave-strength normalization.
5. Finish with the M2 theorem-to-declaration map, cache-disabled clean build, axiom and dependency audit, and independent review candidate. The later mesh assembly consumes the signed reversal theorem. Starting M3 or claiming SU2 correspondence is a separate decision.

The mathematical approval above is suggested wording for Andrea to send. The reviewer's recommendation alone does not authorize implementation.
