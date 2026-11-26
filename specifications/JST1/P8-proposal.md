# P8 proposal: the two open extensions of P7 (paper gap G8)

Written 2026-11-26. The user asked for the two extras that `P7.md` lists as not stated. Same process as P5-P7
(proposal, independent statement review, self-freeze, proofs). Paper `Handbook/paper1/paper1.tex`, sha256 `6993521d…`
(changed since P7 only in the numerical-results section). Numerics: `evidence/JST1/P8-search.py` (exact rationals,
Lean vertex numbering), output `P8-search.log`.

## Item 23

- **P8-23.1 (Kuhn splits).** A cube with its top face turned by θ (cos θ = -7/25, sin θ = 24/25, about 106°) about its
  centre axis: valid trilinear hexahedron (Jacobian `1 - 2w(1-w)(1 - cos θ) ≥ 9/25`), but one neighbour-fan (Kuhn)
  split has two sub-tetrahedra on the same side of a shared interior triangle (so it is not a triangulation). The
  numerics: no Kuhn inversion up to θ = 85°; at θ = 90° the Kuhn tetrahedra degenerate (determinant 0).
- **P8-23.2 (interior vertex).** The `2 × 2 × 2` block of unit cubes with the top layer turned about the central axis
  (cos θ = 3/5): 8 valid trilinear cells (4 unit cubes, 4 twisted), conforming (`Mesh.Conform`, 48 shared triangles),
  the central vertex on no boundary triangle, and `Σ_k n_ik = -β_i ≠ 0` there (`β_i = (0, 0, -7/30)`). The
  numerics also show that the symmetric choice (middle layer turned) gives `β_i = 0` at the centre, so the example
  needs the asymmetric layer.

## Decisions

- **D1.** Kuhn case: stated as "not a triangulation" (same side), not as a facet-balance failure of a Kuhn-averaged
  mesh (the assembly `Mesh.toW` averages all pulling splits; a Kuhn-weighted assembly would be a new definition).
- **D2.** Block: cells of the existing `Mesh` structure (affine fields unused), boundary triangles defined as the face
  triangles of exactly one cell (`bdTrisOf`), the closure stated as `Σ_k n_ik ≠ 0` (the paper's form).
- **D3.** Validity of the cells: trilinear map takes the reference vertices to the cell and has positive Jacobian on
  `[0,1]³` (as P7-22.4).
