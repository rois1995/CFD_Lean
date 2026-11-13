# Independent M2d acceptance

The supplied independent verdict is **Accept M2d (M2-F1/F2/F3/F4/C)**, preserving accepted M2a/M2b/M2c. There are no blocking findings or outstanding acceptance conditions.

- Accepted mathematical candidate: `ca1fc5e14004ee56bb61c2f8d0baf65acc130fe1`.
- Worker checkpoint/evidence: `b2309641866ec79f137655153c24b37954f98399`.
- [Original report](independent-ca1fc5e/report/Review.md), [machine-readable decision](independent-ca1fc5e/report/Review_Record.json), [original payload checksums](independent-ca1fc5e/SHA256SUMS).
- The separate [full-M2 acceptance](../M2/Acceptance.md) covers composition of all 12 approved groups at this candidate.

All 27 supplied payload hashes were verified against the original manifest before extraction. The archive is unchanged. Its five deterministic replay outputs equal the candidate's Git blobs, and the reviewer's literal binding/type diff equals the original worker checkpoint. Candidate and checkpoint tree hashes agree with the report. The reviewer reports an independent fresh-source replay, nine checker fixtures, 56 Lean examples, 66 bindings, 58 preserved inherited types, a separate dependency traversal and six symbolic controls. Recording these results does not claim another worker execution of the reviewer programs.

The historical pending wording in the worker submission is superseded by these decisions. The original worker evidence remains unchanged. There is no M2d follow-up condition to resolve. M3 implementation needs a separate scientific/repository decision.
