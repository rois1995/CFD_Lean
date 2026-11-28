# Proposal — a first-order oriented-face control on two fixed triangles

**Status: proposed for review.** Exercise the geometric extension from the accepted 1D control with exact scalar
advection before selecting a 2D Euler reconstruction. The control uses piecewise-constant cell means and a prescribed
inflow value. Geometry, orientation and flux signs can each be checked by hand.

Join the counterclockwise triangles ABC and ACD along AC, with A=(0,0), B=(2,0), C=(2,1), D=(0,2).
Their areas are 1 and 2. For a counterclockwise directed edge from P to Q, the outward area vector is
`(Q.y − P.y, P.x − Q.x)`. Its length already equals the edge length. Use velocity (1,2) and inflow
state 1. If the signed speed `s = v·n` is nonnegative the outward flux is `s u_inside`, otherwise `s u_outside`.

| Cell | Directed edges | Outward area vectors | Signed speeds |
|---|---|---|---|
| ABC | AB, BC, CA | (0,−2), (1,0), (−1,2) | −4, 1, 3 |
| ACD | AC, CD, DA | (1,−2), (1,2), (−2,0) | −3, 5, −2 |

Both sets of area vectors sum to zero. Compute one flux on CA, owned by ABC, and subtract it from the ACD
outward residual. At cell means 2 and 5 the shared transfer is 6. The boundary contributes −4+2+25−2=21.
The two outward residuals are 4 and 17. At dt=1/8 the updated means are 3/2 and 63/16. The integral drops
from 12 to 75/8, exactly the outward boundary transfer times dt. Equal interior and boundary data give zero
residual in each cell.

Review the orientation convention, units, face ownership, exterior state and division by each cell's own area.
The candidate checks exact closure, reversal symmetry, constant preservation and boundary balance on this mesh.
A general mesh API, multidimensional limiter, Euler positivity and floating-point refinements have separate scopes.
