# P4 statement review (items 15-18)

Independent reviewer: one fresh agent (Opus, high effort), 2026-11-26. It received the paper lines
(`prop:wallJST` 347-372 / 1092-1113, `prop:consistency` 282-298 / 938-955, `lem:sstentropy` 395-407 / 1115-1121,
`prop:sstpde` 411-422 / 1123-1133, scheme and eq. (jst)) and the four statement files with the definitions they use,
but not the author's opinion. Read-only review; it ran numeric checks with numpy (no Lean build).

Numeric checks of the reviewer: P4-15.6 on 3000 random symmetric graphs (2-11 nodes, random wall sets, self-loops):
max |Im λ| = 2.7e-8 (roundoff at defective eigenvalues), min Re λ = -4e-14. P4-16.4 witness family (stretched triangle,
|Ω| = 1): ½ΣΣ|n||e| = 2.46, 34.0, 3334 for L = 1, 10, 100.

**Verdict: no BLOCKING finding**; no false statement, no vacuous or contradictory hypothesis set, no sign error.

## Findings and follow-up

| # | Severity | Finding | Follow-up (before freeze) |
|---|---|---|---|
| S1 | should-fix | P4-16.2 is an abstract lemma (any C² symmetric consistent flux); the scheme's Ismail-Roe flux uses the piecewise log mean, whose C² smoothness across the diagonal is not stated. The paper's proof is equally abstract. | Docstring of P4-16.2 says the instance is not covered; paper gap G6 recorded. Not stated (would need the smoothness of the log mean at a = b). |
| S2 | should-fix | P4-15.4 splits Π^(2) but not Π^(4); (iii) "removes" the fourth-difference production at scheme level. | Added the conjunct `Pi4 S u = Pi4 S' u - ½ ΣΣ [cut] pairF (w_k - w_i) (diss4 i k)` to P4-15.4; docstring links it to P4-15.5. |
| M1 | minor | P4-15.2: the balance equation is the model, not derived from the scheme (sign checked: consistent). | Docstring states the model and the sign of `diss4` in `resid`. |
| M2 | minor | P4-15.3 definitional; scaling and "competes with the penalty" not stated. | Accepted (trivial, labelled; paper calls it a scaling). |
| M3 | minor | P4-16.1 mesh part is P2-6.7 chained; new content is the interpolant. | Recorded as bookkeeping in `P4.md`. |
| M4 | minor | P4-15.6 model: wall nodes have wall neighbours as N*; other boundary types not modelled. | Decision D6 (model of the paper's proof). |
| M5 | minor | P4-16.3 more general than the paper (λ not symmetric, ℰ(i) not tied to the mesh). | Accepted (stronger statement, still true). |
| M6 | minor | P4-17.1 redundant HasDerivAt hypotheses (determined by U). | Accepted (they pin D to U). |
| M7 | minor | P4-15.1 uses the two-sided limit. | Accepted (stronger, true for f ∈ C³(ℝ)). |

Paper gaps reported by the reviewer: G5 (`prop:wallJST`(ii) wording: the cut also removes fourth-difference terms),
G6 (`prop:consistency`(b): C² of F^ec near the diagonal not argued for Ismail-Roe), G7 (cosmetic: spectrum proof,
"PSD times PD" only per component; sign convention of G_II). Recorded in `specifications/JST1/PAPER_GAPS.md`.

## Per-statement verdicts (reviewer)

- P4-15.1: faithful, true (expansion about y_k; the two limits; "not a third difference" for r ≠ 1, f'(0) ≠ 0).
- P4-15.2: faithful, true, trivial as labelled.
- P4-15.3: faithful, trivial.
- P4-15.4: faithful, true (cut changes only ε2, ε4; residual identity sign right; SchemeHyp preserved); Π^(4) missing (S2, fixed).
- P4-15.5: faithful, true (production sign matches `Pi4`; ≥ 0 by `lem:eps2` for r ≥ 1; H̄ form deferred to P3-13.1).
- P4-15.6: faithful within the model, true (block lower triangular; products of two PSD matrices).
- P4-16.1: faithful given decision D1, true; part 2 bookkeeping.
- P4-16.2: true as an abstract lemma; instance for the scheme's flux missing (S1).
- P4-16.3: faithful, true; constant matches the paper's proof.
- P4-16.4: faithful, true; unboundedness is a pure aspect-ratio effect at fixed |Ω|.
- P4-17.1: faithful, true; hypotheses satisfiable (U(τ,y) = U0(y) + τU_t with U_t from the PDE).
- P4-18.1: faithful, true.
- P4-18.2: faithful, true; closes P2 review point M3 (Hessian singular at isolated points).
