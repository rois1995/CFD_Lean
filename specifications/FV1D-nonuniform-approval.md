# FVN scope freeze

The [frozen contract](FV1D-nonuniform.md) reproduces the reviewed proposal at
`34650f15864d46de06f0c885b683420a7e283ea6` byte for byte. The
[independent proposal verdict](../reviews/FVN/Scientific_Proposal_Review.md) recommends freezing FVN-U, FVN-K,
FVN-C, FVN-A, FVN-B, FVN-R, FVN-M and FVN-MB with no mandatory change. This record supersedes the proposal status
in the copy. The [standing implementation authorization](../reviews/Standing_Authorization.md) applies.
Implementation starts after FV1D (PR #26) is merged into `develop`. Implementation acceptance remains pending.

## Quantification of FVN-A

The reviewer asked this record to state the intended quantification. It does not change the claim.

FVN-A holds pointwise at one arbitrary fixed cell `i`. Its hypotheses are only the two differences next to that
cell: `U (next i) − U i = δ i • β` and `U i − U (prev i) = δ (prev i) • β`, with the same `β : S`. It does not
require a globally affine field. On a periodic mesh a globally affine field is constant. The proof map calls FVN-A
"local affine reconstruction exactness".

## Implementation guidance from the review

These suggestions are not part of the frozen claims. The implementation follows them.

- The proof map for the mesh-ratio results cites M. J. Berger, M. J. Aftosmis and S. M. Murman, "Analysis of
  slope limiters on irregular grids", AIAA Paper 2005-0490, for the wider limiter problem on irregular grids.
- Documentation keeps two statements apart. The existing `SlopeBounded θ` certificate fails on stretched cells
  for `θ = 2` (control FVN-X). That does not mean a limiter cannot be used on stretched cells.
- `Mesh1D` stays a fixed periodic 1D mesh. The implementation does not generalize it to ALE, AMR or a general
  control-volume interface.
