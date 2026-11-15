# Frozen M4 interface precision

This companion carries the naming/domain clarifications in the independently reviewed proposal, approved by Andrea together with the unchanged two-stage plan. It adds no algorithm or result group.

1. Keep the interface names **prescribed-exterior Roe** and **inviscid symmetry traction** explicit. The latter is the selected pressure-flux contribution, not a complete symmetry enforcement/update algorithm. Wall pressure is sampled at the owner state on each existing primal-face owner patch.
2. Raw pressure-flux equality is qualified by zero normal momentum. Any velocity interpretation requires positive density; interpreting a nonzero patch by its unit normal also requires nonzero area vector. Zero-area transfer identities remain raw algebraic statements and do not imply a physical normal direction.
3. Face kinds/prescribed data are functions of the actual primal-face ID. Use the identical accepted Boundary, owner and boundaryArea; mixed-kind corners retain separate pieces. The prescribed-exterior numerical flux keeps interior owner left, prescribed exterior right and outward integrated area, without a second multiplier. Supersonic/sonic reductions use the actual two-state Roe-average inequalities, not an owner-only Mach classification.

M4a proves B/W/P. M4b proves R/O/C using these same transfers, followed by a distinct full-M4 review. Neither worker checks nor a proposal recommendation constitutes independent M4 theorem acceptance.
