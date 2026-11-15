# M5 scientific-proposal reviewer handoff

Proposal/checker candidate: **3dcb73dce26149673f6669725fc3b371bd95defd**. Accepted full-M4 mathematics: **3a586a42546cba1784cc79269e3f9d1c5d843f0c**.

Both scoped M4b and composed full M4 are independently accepted without conditions. The original 28-payload review is preserved unchanged under reviews/M4b/independent-3a586a4; all payload hashes and five exact accepted-candidate/worker output matches passed before archiving. Separate acceptance records are reviews/M4b/Acceptance.md and reviews/M4/Acceptance.md, with specifications/accepted-M4.json as the immutable downstream pin.

This checkpoint advances inheritance protection to all 156 accepted ordered bindings/types, all six M4 records/stages and all mathematical sources, including the selected-boundary assembly/controls. The separate accepted-M3 pin is unchanged. The accepted 182-example file, scientific/precision/approval content, prior maps and all compiler/dependency pins are byte-identical. No mathematical source or root import is changed.

[The proposal](../../specifications/M5-proposal.md) specifies a single lumped explicit Euler step on fixed actual dual volumes. Scientific choices include the explicit mass-matrix distinction, old-state evaluation and outgoing minus sign, positive used-node volumes, an unused-node hold branch, common-step boundary balance, exact local-step edge-defect terms, qualified common states and transported volume/step/used data. Six IDs are proposed for one implementation checkpoint; none is active or frozen. The exact rational preparation checks use the existing M4 evaluator and actual standard geometry. They supply feasibility evidence and limits, not Lean proofs.

The full incremental verifier passed: 156 promised results, all 156 inherited types, 182 Lean examples, 17 checker fixtures, 64 current source hashes and nine pinned dependencies. There are no null accepted types and the result-map patch is empty. The inventory/closure are identical to accepted full M4: 1,726 records, 988 safe roots and 21,175 declarations, only propext/Classical.choice/Quot.sound and no reached unsafe constant. All 459 unsafe non-roots and 279 metadata-only records remain visible. No executable verification claim follows from non-root skipped queries.

- Reviewer_Prompt.md: ready-to-send independent SCIENTIFIC PROPOSAL request.
- Candidate.json: immutable pins, scope/status and measured current evidence.
- Changes_from_Accepted_M4.patch: literal full-index diff from accepted full-M4 mathematics to this proposal/checker candidate.
- PreparationChecks.py/log: exact rational controls and the retained earlier controls they reuse.
- GuardFixtures.log and Verification.log: current worker checks.
- SHA256SUMS: separate handoff payload hashes.

With pinned Lean/Lake 4.19.0 on PATH, run:

```bash
python3 -m unittest discover -s scripts -p test_verify.py
python3 reviews/M5/PreparationChecks.py
LAKE_NO_CACHE=1 MATHLIB_NO_CACHE_ON_UPDATE=1 python3 scripts/verify.py
sha256sum -c evidence/SHA256SUMS
```

This proposal/checker-only checkpoint reuses local compiled dependencies and claims no new clean-source replay. Mathematical sources are unchanged. Original accepted implementation replay archives remain unchanged with their historical counts/status fields. Future M5 mathematics still requires a new fresh source replay with both caches disabled and five exact output comparisons.

Requested recommendation: implement / implement after mandatory amendments / do not implement the proposed scope. Do not issue M5 implementation acceptance. After review and mandatory-finding resolution, freeze the exact scientific contract before implementation under the already active standing user authorization. No repeated implementation approval is needed. M5 Lean code, active M5 result bindings, a frozen M5 contract and M6 work are not part of this checkpoint.
