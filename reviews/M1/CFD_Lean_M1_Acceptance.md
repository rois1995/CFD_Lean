# CFD_Lean M1 independent acceptance

**Decision — Accept. Both conditions of the independent M1 review are closed.**

| Revision | Role |
|---|---|
| `0a88e36b3810cd5adc3881db526ca8a35f81afbb` | Accepted mathematical candidate |
| `180ff1be1aa95d943574efd9c05cd4de320a88b6` | Direct child that closes the review conditions |

**Reproducibility.** The follow-up publishes both reviewer scripts, the two cache controls, the pinned ProofWidgets JavaScript bootstrap and the checksum check before evidence regeneration. The README correctly directs the reader to run the scripts against the frozen candidate with the published scripts available outside that checkout. All 45 files from the original reviewer ZIP, including its checksum manifest, match the Git blobs in the follow-up byte for byte. I also verified all 14 root evidence checksum entries and all seven worker follow-up checksum entries. The corrected worker history discloses that Lake downloaded a ProofWidgets release in the original worker run. The two independent cold builds retained in the review bundle establish source-only reproducibility. [Published procedure](https://github.com/rois1995/CFD_Lean/blob/180ff1be1aa95d943574efd9c05cd4de320a88b6/README.md)

**Approval record.** The transcript records the proposed sources, physical assumptions, area-vector convention, scope, architecture and dependency pins, followed by the user's explicit “Approve” and subsequent private-repository choice. These choices agree with the reviewed M1 contract. I accept the worker-supplied transcription as sufficient for this review. Its exact original timestamps and platform provenance remain independently unverified. [Approval record](https://github.com/rois1995/CFD_Lean/blob/180ff1be1aa95d943574efd9c05cd4de320a88b6/specifications/M0-approval.md)

**Independent checks.** The four project Lean files, M1 contract, toolchain, Lake configuration and dependency manifest match the frozen candidate byte for byte. The Python verifier has an identical abstract syntax tree. I reran the reviewer checks against the previously source-built candidate. The audit reached 5,612 declarations from 40 roots, found only the three accepted foundational axioms and reached no unsafe declaration. All 9,840 exact-arithmetic comparisons passed. This closure replay reused the existing build. The follow-up also supplies Blazek p. 12, Eq. (2.12), and distinguishes Toro’s printed DOI from its resolving publisher DOI. [Corrected reference map](https://github.com/rois1995/CFD_Lean/blob/180ff1be1aa95d943574efd9c05cd4de320a88b6/references/M1.md)

Acceptance covers exact-real ideal-gas Euler state algebra and the oriented physical flux. The existing recommendation to broaden theorem discovery and reject duplicate audit rows applies before relying on the verifier for a larger milestone. Roe flux and correspondence with compiled SU2 require separate review.
