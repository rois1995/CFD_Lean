# Independent freeze of first-order scalar advection

The external reviewer approved SA-F, SA-K and SA-C as written at `f32c86233f92f5c4de6b2749a5ff82cb0915e140`,
against `develop` at `8c957b18ea084ffc108154bef361b1fbfa966ed3`. The reviewer requested no mandatory changes.
The [frozen proposal](../../specifications/MD-scalar-advection-proposal.md) has SHA-256
`7f1dda0d430ce7af4b7a7b9456250176be056ac80c639987ffd94027b5e3fc4e`. [Proposal PR](https://github.com/rois1995/CFD_Lean/pull/76)

The reviewer independently reproduced the oblique shared transfer `6` and the four-cell transfers `2,4,−2,−4`.
The freeze calls for separate consistency, reversed-orientation and zero-speed checks, a common production adapter
on both meshes, and constant-state and amount proofs through the accepted MD declarations. The scalar implementation
receives a separate independent verdict. [Assembly acceptance](../MD/Acceptance.md)
