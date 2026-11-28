# Independent reconstruction review and scope decision

The [external verdict](Independent_Review.md) reviewed PR #66 at
`75b0f6cf790a3ed759126cbd50591c00d9281337`. The supplied report has SHA-256
`32f00df2219cbc4b597175df6cd4dfda87e13fbe376982d0bb807c2d14829b40`.
The reviewer recommended freezing U and B, and approved G and E subject to specified amendments.
The owner authorized integration after resolving the findings and passing required checks.

The [amended scientific scope](../../../specifications/FV1D-WENO-reconstruction-proposal.md) is pinned
at `ba97f56d70d1a20622d4df1e7a6b96655b6426bc`, SHA-256
`3053b887767a85a059baa669c4027629ec9f01e0b51bce207e19942347f5eae7`. This is the freeze
revision for the four scopes when PR #66 passes final Integration and merges into develop.

| Review item | Resolution |
|---|---|
| E1 obligation 4 | The [E1 result map](../../../specifications/E1-results.json) binds the compiled replay, its [observed binary and output words](../../../evidence/E1/native-replay.json), and the native trust assumption. E1-4 is a control. |
| FVT-A | The [trace result map](../../../specifications/FV1D-euler-traces-results.json) binds `face_admissible_m1`. Both real oriented traces satisfy M1 admissibility when the means do. |
| G-S | The scope specifies the six widths, six means, ε, the directed seam, both rational answers and the immutable test revision. |
| E | E-A covers face validity, E-P first-order parity, E-D adaptive timestep selection and E-R independent replay. The scope fixes exceptional-speed behavior, the initial means, three meshes, final time, step counts and tolerances. |
| Final integration | The merge must use an up-to-date develop base and a passing Integration check on the actual candidate. GitHub records the tested head, run and merge commit. |

The scientific decision concerns the specified method and its promised results. The WENO and Euler
implementation PRs carry their own bindings, controls and validation. The two-triangle verdict remains
specific to the reviewed benchmark.
