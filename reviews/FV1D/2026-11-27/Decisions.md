# Independent review and scope freezes, 2026-11-27

The owner supplied the [original review](Independent_Review.md) covering PRs #50–#65. Its SHA-256 is
`9786d48a89972163144fa3b67fb49593a07ca57e3e6a187f9c1b1e69c71af28e`. The reviewed heads and the verdict for each are recorded in that file.

The reviewer accepted the roadmap changes in #50, #59 and #61. Under the [standing authorization](../../Standing_Authorization.md), the following three proposed scopes are frozen **as written**, at the exact revisions independently recommended for freeze. The content hashes below identify the normative proposal bytes, including their historical status text.

| Frozen scope | Reviewed revision | SHA-256 |
|---|---|---|
| [E1 Burgers binary64](../../../specifications/E1-burgers-step-proposal.md) | `4b914b5bb3ea39ded55b958f5b29d72b7bd20c80` | `f96f2121f81a3cbe36032a64c9ce4e83a95b03dc192c8d50ac9fbe11243b1b5b` |
| [Uniform Euler MUSCL traces](../../../specifications/FV1D-euler-traces-proposal.md) | `5d76e8bea0390161aa388c92ec34f18d57bcbe50` | `f20ac41c496d449e73b5289b907c24c500f5f8bf1bab05cad293e90cd360e88f` |
| [Two-triangle oriented-face control](../../../specifications/FV2D-oriented-face-proposal.md) | `d36848e44ff7dc951594b6c1e449f4c6696f2cff` | `b29b1a90d75704221289baa71475f8b3cb88321c35e0b0e55cf1fc299ffbbe79` |

The source-level passes for #52–#55 and #57 and the controls in #58 apply to the reviewed draft declarations. Normal production promotion, bindings and a subsequent implementation verdict remain open. The review requests changes to #60 and #62–#64. The source-level pass for #65 is conditional on resolution of the Euler findings.

The [new scientific proposal](../../../specifications/FV1D-WENO-reconstruction-proposal.md) is presented for independent review. The freeze decision above covers only the three named scopes.
