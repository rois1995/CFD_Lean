# Burgers B4: review of the trusted statement file

Date: 2026-11-26. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed file and
did not check the implementation proofs. This is not a human review and not the independent implementation review.

Reviewed file: `CFDLean/Verification/BurgersB4Challenge.lean`
(sha256 `7f83b6db7ae57cdc30d6385eaac0180c37e0fed4a402176eeccc63018a49a341`).
Reference: `specifications/Burgers-B4.md`; comparison with the B1 trusted file.

## Verdict

**Faithful, with remarks.** No blocker and no required change.

## Checks made by the reviewer (own proofs on a scratch copy)

- Sign convention: the reviewer derived and proved in Lean the cell identity
  `v_i L_i + (Q_i - Q_{i-1})/dx = [(Δv_i F_i - Δψ_i) + (Δv_{i-1} F_{i-1} - Δψ_{i-1})]/(2 dx)`. So the semidiscrete
  inequality `d/dt η(u_i) + (Q_i - Q_{i-1})/dx ≤ 0` holds exactly when `(v(b) - v(a)) F(a, b) ≤ ψ(b) - ψ(a)`. This is
  Tadmor's direction with `ψ = v f - q`; it is not reversed. (Checked by derivation, not against the papers.)
- Burgers data: `q = u³/3`, `ψ = u³/6`; `Q(c, c) = q(c)` for Rusanov; the entropy-conservative flux identities; the
  Rusanov decomposition; `RusanovEntropyStable` proved independently. It is not trivially true: the central flux
  `(a² + b²)/4` fails it at `(0, 1)`.
- Same flux and operator as the B1 trusted file (`rusanovStep = u + dt * rhs` by `rfl`).
- `entropyFlux ... (next.symm i)` is the flux between cells `i-1` and `i`.
- All five statements proved by the reviewer; they hold for every permutation `next`.

## Findings (all remarks)

1. `dx > 0` is slightly stronger than necessary (`dx ≥ 0` is enough because `x / 0 = 0`); with `dx < 0` the statements
   fail.
2. The trusted file states the five statements of the contract table. Not trusted: the equality versions for
   entropy-conservative fluxes, `entropyFlux_constant`, `entropyPotential_eq`, the Rusanov decomposition, and the B4-S
   cell inequality (which follows from two trusted statements). No `η` and no `q` appear in the trusted file.
3. The name "entropy stability" is justified only through the chain rule `d/dt η(u_i) = v_i L_i`, which is not
   formalized (the contract says so). Not claimed: fully discrete inequalities, MUSCL, other entropies, convergence.

## Not checked by the reviewer

The bridge, `lake comparator`, the implementation files, the approval record.
