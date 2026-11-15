# M4b and composed full-M4 review checkpoint

Mathematical candidate: **3a586a42546cba1784cc79269e3f9d1c5d843f0c**.

Accepted M4a B/W/P: **37c1e6ee4618b0183135c2795b3aa6ebea2f22d5**. Its supplied independent verdict has no blockers or outstanding conditions; original payloads remain unchanged under reviews/M4a/independent-37c1e6e. The required inheritance extension passed before M4b mathematics at commit 4c0a4d5. The immutable reviewed M4 freeze remains 0cff4af244b85f4e2071e7bf941d40fdd0a399b5. Andrea approved the complete plan and subsequently supplied standing implementation authorization; see reviews/Standing_Authorization.md.

M4b completes R/O/C with 16 new bindings, for 156 cumulative promises and 39 full-M4 bindings. All six M4 IDs are populated, with no deferred result. All 140 accepted bindings/types and mathematical sources are protected; the 153 accepted examples remain an exact prefix. The new modules are Boundary/Assembly.lean and Boundary/AssemblyControls.lean. See references/M4b.md for exact algorithm connections, hypotheses, numeric control vectors and source mapping.

The worker verifier passed: 182 Lean examples, 16 checker fixtures, 62 source hashes and nine pinned dependencies. The full inventory retains 1,726 records, 988 safe roots and 21,175 reached declarations, with only propext, Classical.choice and Quot.sound and no reachable unsafe constant. All 459 unsafe non-roots (421 definitions and 38 compiler axiom records) and 279 metadata-only records remain visible. Strong raw finite-algebra identities are distinguished from physically qualified results.

- [Ready-to-send reviewer prompt](Reviewer_Prompt.md).
- Changes_from_Accepted_M4a.patch is the literal full-index binary Git diff from accepted M4a to this mathematical candidate.
- Candidate.json records exact status and metrics.
- evidence/M4b-source-replay holds the passed implementation-worker cold replay and separate checksum manifest, independently of scientific acceptance.

From a clean detached candidate without .lake, with pinned Lean/Lake 4.19.0, Git, Python, Node/npm, sha256sum and realpath available:

```bash
bash scripts/reproduce.sh 3a586a42546cba1784cc79269e3f9d1c5d843f0c /outside/checkout/M4b-review-logs
```

The unchanged script fetches nine fresh source pins, disables both binary caches, compiles pinned widget JS locally, runs fixtures/verifier/examples, preserves all 62 pre/post source checksums and compares five deterministic outputs against candidate Git blobs. Worker fresh-source replay **passed** with exit code 0: 182 examples, 16 fixtures, all 62 pre/post source hashes, all five byte-identical deterministic outputs and nine fresh pins. Only evidence/build.log differs in the replay checkout; no ProofWidgets release archive is present. Raw logs, replay.json and their own hash manifest are archived in evidence/M4b-source-replay.

Please return two distinct verdicts: scoped M4b R/O/C and composed full M4 B/W/P/R/O/C. Both remain pending. Build/replay success is implementation evidence and supplies neither verdict. No M5 proposal or new boundary variant has been started. Further work follows the independent checkpoint under standing authorization.
