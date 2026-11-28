# Two-triangle oriented-face control

The independent reviewer recommended freezing the [two-triangle proposal](../../specifications/FV2D-oriented-face-proposal.md)
as written and passed its [exact controls](../../benchmarks/ReviewCases/OrientedTriangles.lean)
at `d36848e44ff7dc951594b6c1e449f4c6696f2cff`. The owner authorized integration conditional on the review
findings. The proposal SHA-256 is `b29b1a90d75704221289baa71475f8b3cb88321c35e0b0e55cf1fc299ffbbe79`.

The control uses one owner-oriented area vector on the oblique interface. Its outward transfer is 6.
The unequal cell measures are 1 and 2. The updated means at `dt = 1/8` are `3/2` and `63/16`.
These checks apply to this prescribed-boundary benchmark. The general fixed-mesh assembly contract
requires its own independent freeze.
