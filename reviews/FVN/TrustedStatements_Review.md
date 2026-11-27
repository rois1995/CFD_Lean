# FVN: review of the trusted statement file

Date: 2026-11-27. Reviewer: a separate AI review agent with read-only access. It did not write the reviewed file and
did not read the implementation or the implementer's notes. This is not a human review and not the independent
implementation review.

Reviewed file: `CFDLean/Verification/FV1DNonuniformChallenge.lean` at commit `2e7106b`
(sha256 `15919e1b025ba49faba2f897d78f68ea903d062b8c97755209d467bf6f5f4057`).
Reference: `specifications/FV1D-nonuniform.md` and `specifications/FV1D-nonuniform-approval.md`; wording compared
with the accepted B3b trusted file.

## Verdict

**No mandatory findings.** Every trusted definition and statement is faithful to the frozen contract.

## Per statement

| Statement | Contract | Result |
|---|---|---|
| `spacing`, `MeshRatio`, `backDiff`, `fwdDiff`, `slope`, `leftState`, `rightState`, `update`, `firstOrderStep`, `musclStep`, `faceSpeed`, `totalVariation` | Geometry, The step | Faithful. Spacing, rescaled differences, face states, own-width update and mesh ratio match symbol by symbol. |
| `burgersFlux`, `rusanovWaveSpeed`, `rusanov`, the six slopes, `SlopeBounded`, `ssprk2`, `ssprk3` | B3b meaning | Character-for-character identical to the accepted B3b definitions. |
| `MonotoneFlux`, `LipschitzOnBounds` | FVN-M hypotheses | Faithful. Global monotonicity and Lipschitz on `[m, M]`. |
| `FirstOrderBounds` | FVN-B (a) | Faithful. |
| `FirstOrderTotalVariation` | FVN-B (b) | Faithful; no bound hypothesis, as in the contract. |
| `ReconstructionBounds` | FVN-R | Faithful. |
| `MusclBounds` | FVN-M (a) | Faithful; cell CFL matches symbol by symbol and was re-derived from the Harten coefficients. |
| `MusclTotalVariation` | FVN-M (b) | Faithful; face CFL matches and was re-derived. |
| `MusclEulerMultiStep`, `MusclSSPRK2MultiStep`, `MusclSSPRK3MultiStep` | FVN-MB | Faithful. No `θ ≤ 2` hypothesis is needed: for a nonempty mesh the mesh ratio forces `θ ≤ 2`. |
| `MeshRatioOvershoot` | FVN-X | Faithful; every value recomputed by hand. |

## Deliberate choices evaluated

1. **FVN-B (a) written with `a (prev i)`.** Acceptable. It is the literal contract form; the term `u (next (prev i))`
   equals `u i` by `Equiv.apply_symm_apply`. The hypothesis is neither weaker nor stronger.
2. **`0 ≤ dt` in FVN-MB.** Acceptable and necessary. FVN-B and FVN-M fix `dt ≥ 0` and FVN-MB is derived from FVN-M;
   with `dt < 0` the claim is false. B3b's `MultiStepStable` has the same hypothesis.
3. **`n`-step iterates for Forward Euler, SSPRK2 and SSPRK3.** Acceptable. For Forward Euler this is the contract
   text; for SSPRK2 and SSPRK3, `n = 1` is the contract's one step and the `n`-step form is strictly stronger and
   true because the bounds, hence the CFL, are invariant. It matches B3b.
4. **FVN-X restating the control data.** Acceptable. Widths, state, bound membership, `back = 3/2`, `fwd = 3/10`,
   the six left-state values, `MeshRatio (5/4)` and `¬ MeshRatio 2` all appear and are correct.

## Non-blocking remarks

1. `next` is any `I ≃ I` and `I` may be empty. Quantifying over more meshes only strengthens the claims; this is the
   B3b convention.
2. FVN-M quantifies over any `H : ℝ → ℝ → ℝ` instead of `nf.eval`; no consistency is assumed, which is a
   strengthening. The reviewer asked for a check that `MonotoneFlux` and `LipschitzOnBounds` match B3. The
   controller compared them with `CFDLean/Schemes/Scalar/Monotone.lean` and `Lipschitz.lean`: they are the same
   global monotonicity and the same Lipschitz-on-`[m, M]` certificate.
3. No hidden vacuity: `SlopeBounded θ` with `θ < 0` is unsatisfiable; Lipschitz with `m < M` forces `KL, KR ≥ 0`;
   with `m = M` the state is constant and the claims hold trivially.
4. The FVN-M (b) docstring could say "with the face condition in place of the cell condition".
5. FVN-X records exact values; that the MC, superbee and van Leer slopes are `SlopeBounded 2` comes from the accepted
   B3b-L. FVN-X is an exact control, as the contract presents it.
