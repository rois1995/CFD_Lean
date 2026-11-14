# M3b and composed full-M3 review checkpoint

Mathematical candidate: **e2ea538b8da38c01c098ef28a3ea31030d90c6bb**.

M3a is independently accepted at a70270c3f771e66bcaaebc18b8480c32f9606b1e, without outstanding conditions. Its supplied original review is retained unchanged under reviews/M3a/independent-a70270c, with acceptance in reviews/M3a/Acceptance.md. The next-stage guard was extended before geometry work to all 84 accepted bindings, exact parts/stages/types and source hashes; its 12 fixtures pass.

This candidate implements M3-G/V and the concrete M3-C part under the already approved full M3 plan. The frozen scientific and representation contracts are unchanged. All six M3 IDs and every approved part are populated. The worker verified 117 cumulative promises, all 84 inherited types, nine unchanged dependency revisions, the complete 1,356-record inventory and all 112 Lean examples. Its 780 safe roots reach 20,935 declarations, only the three permitted foundational axioms and no unsafe dependency. Unsafe compiler/executable auxiliaries and metadata-only records remain visible as non-roots. See references/M3b.md for the construction, assumptions, proof/result map and exact controls.

- [Ready-to-send reviewer prompt](Reviewer_Prompt.md).
- `Changes_from_Accepted_M3a.patch`: literal full-index diff from accepted a70270c to this exact candidate, including the preservation guard and original supplied acceptance evidence.
- `evidence/M3b-source-replay`: fresh implementation-worker pinned-source replay; independent verdict remains pending.
- `evidence/verification.json`, `kernel-inventory.log`, `inherited-types.json`, `binding-type-diff.json` and `bindings-diff.patch`: deterministic candidate evidence.

Use a fresh clean detached checkout of the exact candidate, without .lake, and the existing compiler pin:

```bash
bash scripts/reproduce.sh e2ea538b8da38c01c098ef28a3ea31030d90c6bb /outside/checkout/M3b-review-logs
```

The script fetches nine fresh manifest pins, disables both binary-cache mechanisms, builds pinned ProofWidgets assets locally, runs 12 fixtures and the verifier, checks all 49 source hashes before/after and compares the five deterministic outputs byte for byte. It requires the existing Lean/Lake 4.19.0, Git, Python, Node/npm, sha256sum and realpath. Using a compiler already present elsewhere does not import another project's mathematical sources. Original historical archives and their hash manifests remain untouched.

The fresh implementation-worker replay **passed** on this exact candidate: 49 pre/post source checks, five byte-identical deterministic outputs, 112 Lean examples and 12 fixtures. The fresh tracked diff is only evidence/build.log, and no ProofWidgets release archive is present. Raw logs, environment/pin records, replay.json and a separate SHA256SUMS are archived in evidence/M3b-source-replay.

M3b and composed full M3 need separate independent scientific verdicts. Build success, worker cold replay and kernel audit establish neither that the frozen scientific model was the intended physical method nor that a compiled CFD solver implements it. No M4 work is started or claimed.
