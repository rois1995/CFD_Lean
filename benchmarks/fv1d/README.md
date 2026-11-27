# Periodic Euler density wave

The [reference case](euler-density-wave.json) describes a smooth ideal-gas Euler solution on the unit periodic
interval. Constant pressure and velocity reduce the mass equation to advection at speed 2. Momentum density
is twice the density, and total energy density is one plus twice the density. Each snapshot therefore follows
from the translation of a single profile.

For a uniform cell with edges `l`, `r` and width `dx`, integrating the sine gives the exact mean density

```text
rho_avg(t) = 1 + (cos(2*pi*(l - 2*t)) - cos(2*pi*(r - 2*t))) / (16*dx).
```

At time 1/8 the wave has moved one cell to the right on the four-cell mesh. Reading the initial last row as the
new first row exercises the periodic wrap. The chosen amplitude gives exact dyadic values for both snapshots.

For a future FV1D run, initialize with cell averages and compare at time 1/8. The first-order Rusanov method
diffuses a smooth wave. Measure that error for each conserved component using
`dx * sum_i abs(numerical_avg[i] - exact_avg[i])`. Compare the domain integrals separately, since a reversed
translation would also conserve all three totals.
