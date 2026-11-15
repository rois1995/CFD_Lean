# M4 proposal review checkpoint

**Proposal/checker candidate: `936d20d32fdd3e18c9f1782a868cbd0378fde7df`. No M4 Lean implementation is included or authorized.**

Full M3 is independently accepted at e2ea538b8da38c01c098ef28a3ea31030d90c6bb. Separate scoped M3b and composed-M3 verdicts have no blockers or outstanding conditions; original supplied payloads and their manifest are retained unchanged in reviews/M3b/independent-e2ea538. The accepted pin is specifications/accepted-M3.json.

- [Scientific proposal](../../specifications/M4-proposal.md): exact stationary wall/symmetry pressure and prescribed-exterior Roe choices, physical domain/compatibility, six proposed obligations and two-stage sequence.
- [Ready-to-send reviewer prompt](Reviewer_Prompt.md).
- [Exact rational feasibility controls](PreparationChecks.py) and [results](PreparationChecks.log).
- [Source inspection provenance](Source_Inspection.json): the already approved book, actual verified hash, complete text pages and four visually inspected pages. The PDF remains in the external reference collection.
- [Preservation record](Preservation.json), fixture/verifier logs, current deterministic evidence and literal Changes_from_Accepted_M3.patch.

All accepted Lean source files and exports, the 112-example file, contracts/result maps, kernel inspector and compiler/dependency pins are unchanged. The guard now protects all 117 accepted cumulative bindings/types and M3 parts against the full-M3 pin. Thirteen checker fixtures and the full incremental verifier passed. The kernel inventory is byte-identical to accepted M3; every current type matches its accepted type and the binding-map diff is empty. Current machine metadata reports M3 accepted. Historical pending fields and 84-inherited/33-new counts in original M3b archives remain unchanged.

Reproduce the proposal controls and preservation check with existing pinned dependency builds:

```bash
python3 reviews/M4/PreparationChecks.py
python3 -m unittest discover -s scripts -p test_verify.py
LAKE_NO_CACHE=1 MATHLIB_NO_CACHE_ON_UPDATE=1 python3 scripts/verify.py
```

The current checkpoint claims an incremental preservation check, not a new mathematical cold replay. An optional entirely fresh replay can use the unchanged scripts/reproduce.sh on the exact candidate, from a clean detached checkout without .lake, with an external log directory. The future implemented M4 stages must each run the complete clean nine-pin source/widget bootstrap and deterministic comparisons with both binary caches disabled.

The reviewer should assess direct owner pressure and the prescribed-exterior Roe variant as separate scientific decisions, including source distinctions, zero/sonic/oblique/corner cases, actual-transfer compatibility and component boundary balance. The proposal makes no nonreflecting, characteristic-reconstruction, velocity-enforcement, time-evolution, entropy/update-positivity, mixed-element or SU2 claim. After an independent recommendation, Andrea must approve or amend the actual choices before a separate M4 contract is frozen and Lean implementation starts.
