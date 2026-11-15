# M4a local boundary checkpoint

Mathematical candidate: **37c1e6ee4618b0183135c2795b3aa6ebea2f22d5**.

Andrea approved the reviewed M4 proposal and the complete M4a/M4b plan. The original no-mandatory-amendment recommendation and 22 payloads remain unchanged under reviews/M4/proposal-936d20d. specifications/M4.md is the exact proposal copy, with explicit approval and reviewed naming/domain precision frozen at 0cff4af244b85f4e2071e7bf941d40fdd0a399b5. Historical pending wording in the copied proposal is superseded by M4-approval.md.

M4a implements B/W/P: actual face-derived kinds/data on the accepted Boundary records, direct owner-pressure wall/inviscid-symmetry traction, and the actual prescribed-exterior original Roe transfer. See references/M4a.md for complete assumptions, source/result map and exact control descriptions. The selected algorithm names and positive-density/nonzero-patch velocity qualification are explicit in the interfaces and types.

The worker checked 140 cumulative promised bindings, all 117 accepted inherited types, 153 Lean examples and 15 verifier fixtures. The 112 accepted examples are an exact unchanged prefix. The complete inventory has 1,585 records; 905 safe roots reach 21,075 declarations with only the three permitted foundational axioms and no unsafe dependency. All unsafe compiler auxiliaries and metadata-only declarations remain visible as non-roots. Original mathematical sources, scientific contracts and dependency/compiler pins are unchanged.

- [Ready-to-send reviewer prompt](Reviewer_Prompt.md).
- `Changes_from_Accepted_M3.patch`: literal full-index diff from accepted full M3 to this candidate.
- `evidence/M4a-source-replay`: implementation-worker fresh pinned-source replay and its separate hash manifest.
- Current deterministic evidence: verification.json, kernel-inventory.log, inherited-types.json, binding-type-diff.json and bindings-diff.patch under evidence/.

Independently reproduce from a clean detached candidate without .lake, with the existing Lean/Lake 4.19.0, Git, Python, Node/npm, sha256sum and realpath available:

```bash
bash scripts/reproduce.sh 37c1e6ee4618b0183135c2795b3aa6ebea2f22d5 /outside/checkout/M4a-review-logs
```

The unchanged procedure fetches all nine pinned source trees, disables both binary-cache mechanisms, builds pinned widget assets locally, runs the checker fixtures/verifier/examples, checks all 58 pre/post source hashes and compares the five deterministic candidate outputs byte for byte. The worker replay is implementation evidence rather than independent scientific acceptance.

The implementation-worker fresh source replay **passed** on the exact candidate: all 58 pre/post source hashes, 153 Lean examples, 15 fixtures and five byte-identical deterministic comparisons. Only evidence/build.log differs in the clean replay checkout; no ProofWidgets release archive is present. Raw logs and the worker classification remain separate from independent acceptance.

M4a independent theorem acceptance is pending. M4b R/O/C and a separate composed full-M4 verdict remain required under the approved plan. Local wall compatibility/P consistency and old generic M3 theorems do not themselves instantiate the deferred selected-boundary residual/transport/common-state composition. No new boundary variant, full symmetry enforcement, nonreflection, projected/time update, entropy/update-positivity repair or SU2 correspondence is claimed here.
