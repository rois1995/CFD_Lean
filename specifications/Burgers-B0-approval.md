# Burgers B0 implementation authorization

On 2026-11-25 the user explicitly authorized using the existing CFD_Lean repository as the core library and proceeding with implementation:

> Yep, let's use the CFD_Lean as core library. You can proceed

This approval resolves the architectural direction in `Burgers-B0-proposal.md` as follows:

- CFD_Lean remains the core package.
- Burgers is added under an isolated `CFDLean.Burgers` namespace.
- Numerical properties are separate proof certificates rather than fields of one monolithic flux structure.
- B0 introduces a scalar conservation-law object.
- The first periodic mathematical representation is `ZMod N` with nonzero size, subject only to compilation-equivalent adjustment required by the pinned Mathlib API.
- Conservation is stated for the raw finite sum first, with the constant-cell-width discrete integral as a corollary.
- No external scientific-computing repository becomes a core B0 dependency.

The frozen implementation contract is `specifications/Burgers-B0.md`. No accepted Euler M1--M4 mathematical source is authorized to change merely to support B0. The current M5 review status is unaffected.

Implementation is authorized. Independent review of the resulting B0 theorems remains pending and is not implied by this approval.
