# M1 final status: accepted

The supplied [final acceptance](CFD_Lean_M1_Acceptance.md) supersedes the original conditional verdict: mathematical candidate `0a88e36b3810cd5adc3881db526ca8a35f81afbb` is accepted, and follow-up `180ff1be1aa95d943574efd9c05cd4de320a88b6` closes both conditions. The acceptance and [next-step handoff](START_HERE_Agent_A.md) were preserved byte-for-byte from the user's new archive. Its nested evidence exactly matches all 45 previously preserved files, so no evidence was reimported.

The recommendation to harden declaration inventory before M2 remains. M1 acceptance does not extend to Roe flux or compiled SU2. The verifier reports machine proof checks and links to this independent decision; it does not decide scientific acceptance.

The following worker response records the preceding conditional-review stage. Its pending-status language is historical and is superseded by the final acceptance above.

## Historical follow-up response

# M1 review follow-up

## Frozen review and preserved evidence

The user supplied `CFD_Lean_M1_Reviewer_Evidence.zip`. All 45 original files are preserved here without alteration, including the report, reviewer programs, original SHA256SUMS and replay logs. Verify the original files from this directory with `sha256sum -c SHA256SUMS`. This README is a worker-authored follow-up and is not part of the reviewer's original checksum list.

Reviewed commit: `0a88e36b3810cd5adc3881db526ca8a35f81afbb`. Decision: **accept with conditions**. The submitted evidence passed all 44 original checksum entries before it was copied. The source-only reproduction script is published unchanged; the reviewer reports testing it in a fresh detached checkout and independently replaying the checks.

## Responses to findings

| Finding | Follow-up | Remaining acceptance boundary |
| --- | --- | --- |
| High: fresh source-only build procedure missing | Root README now publishes the preserved ReproduceM1.sh and RunReviewerChecks.sh procedure, both cache-control variables, the pinned local widget build, tool prerequisites, outside-checkout logs and checksum-before-verification order. | The reviewer/scientific approver must confirm that publishing the tested procedure closes this documentation condition. |
| Medium: original approval exchange unavailable | specifications/M0-approval.md supplies a transcript of the proposal's source, scope, convention and architecture choices, the user's literal `Approve` reply and the subsequent private-visibility answer. | The transcript is worker-supplied, not an authenticated platform export. Confirm it against the original conversation; no new ratification or historical timestamp is invented. |
| Medium: future audit coverage | Recorded as a prerequisite for reliance on the verifier in a larger milestone: environment-based qualified declaration inventory, duplicate-record rejection and a separately approved list of promised statements. The preserved KernelInventory.lean provides the reviewer's broader independent M1 check. | Nonblocking for frozen M1 according to the review. No claim that the original Python inventory handles other declaration forms. |
| Low: bibliographic precision | references/M1.md now records resolving Toro DOI 10.1007/b79761 alongside the identifier printed in the local book, and adds Blazek p. 12, Eq. (2.12), to the physical-energy-flux provenance. | Locators were checked against the publisher record and the local Blazek page; no change of source edition. |

No Lean mathematical source, original contract statement, dependency pin or historical reviewer file is changed by this follow-up. The verifier receives only a comment identifying its M1 coverage limit. The worker evidence narrative is corrected: the original run downloaded a ProofWidgets release through Lake; only the supplied reviewer builds establish fresh source-only reproduction. The theorem candidate remains the frozen reviewed commit; this documentation/evidence follow-up is a later revision. Original evidence at the frozen commit remains available in Git.

## Checks and limits

The preserved shell scripts receive syntax checks, the original 44 reviewer-file checksums are checked, and the current package verifier passed to refresh its source hashes after documentation changes. The worker also replayed RunReviewerChecks.sh against the unchanged mathematics: 40 roots and 5,612 dependencies reached only the three allowed foundational axioms and no unsafe declaration; all 9,840 exact-arithmetic cases passed. Separate worker replay logs are in evidence/review-followup/. This replay is not a new independent verdict. This follow-up does not claim another independently performed fresh source build; the two cache-disabled fresh reproductions are those documented in the submitted reviewer logs.

Unconditional acceptance is not self-certified. Scientific approval confirmation, authoritative errata completeness, larger-milestone audit hardening, and solver/floating-point correspondence remain separate matters.

The generated verification.json continues to mark independent review as pending for the current follow-up; the external accept-with-conditions verdict is recorded separately for the original frozen commit. The verifier cannot infer scientific sign-off.
