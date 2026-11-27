# Independent FVN proposal review

The repository owner supplied the following external review of
`specifications/FV1D-nonuniform-proposal.md` at revision `34650f15864d46de06f0c885b683420a7e283ea6`.

> Mandatory changes
>
> None mathematically.
>
> Before freezing, I recommend making the intended quantification of FVN-A explicit in the approval/review record:
>
> FVN-A is pointwise at an arbitrary fixed cell i; its two adjacent differences are assumed locally affine with the same (\beta).
>
> This prevents the phrase “affine data” from being interpreted as requiring a globally nonconstant affine periodic field.
>
> I do not regard that clarification as changing the claim.
>
> Non-blocking suggestions
>
> Call FVN-A something like local affine reconstruction exactness in the proof map.
>
> Cite Berger–Aftosmis–Murman 2005 for the broader irregular-grid limiter issue.
>
> Preserve the distinction between:
>
> failure of the existing SlopeBounded θ certificate on stretched cells, and
>
> impossibility of using a limiter on stretched cells.
>
> The proposal currently makes this distinction correctly.
>
> Do not generalize Mesh1D into ALE/AMR/general-control-volume infrastructure during implementation.
>
> Independent external reviewer conclusion
>
> RECOMMEND FREEZING
>
> FVN-U
>
> FVN-K
>
> FVN-C
>
> FVN-A
>
> FVN-B
>
> FVN-R
>
> FVN-M
>
> FVN-MB
>
> at exact proposal revision:
>
> 34650f15864d46de06f0c885b683420a7e283ea6.
>
> I found no mandatory scientific correction.
>
> The rescaled reconstruction is geometrically correct, the mesh-ratio condition follows from the existing SlopeBounded θ certificate, both non-uniform FVN-M CFL formulas reduce correctly to B3b on uniform meshes, the Burgers constant 8 is a valid sufficient bound, and all three exact controls independently recompute to the values stated.
>
> This verdict is a proposal/scope freeze recommendation only. Implementation, trusted-statement review, comparator evidence, theorem-type verification and final implementation acceptance remain separate.

The [freeze record](../../specifications/FV1D-nonuniform-approval.md) states the FVN-A quantification and how the
non-blocking suggestions apply to the implementation.
