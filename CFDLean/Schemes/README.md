# Numerical schemes

- [Scalar](Scalar/) contains the two-point numerical flux interface and consistency, monotonicity and Lipschitz certificates.
- [Burgers](Burgers/) combines Rusanov with [Forward Euler](Burgers/RusanovForwardEuler.lean),
  [SSP Runge–Kutta](Burgers/RusanovSSP.lean), [MUSCL](Burgers/RusanovMuscl.lean) and
  [selectable limiters](Burgers/RusanovLimiters.lean). Start with the [B0 proof map](../../references/Burgers-B0.md).
- [Roe/Flux](Roe/Flux.lean) defines the integrated Euler numerical flux. [Boundary](Boundary/) covers patch transfers,
  residual assembly and their controls. See the [M2d](../../references/M2d.md) and [M4b](../../references/M4b.md) proof maps.

For reusable spatial operators see [Discrete](../Discrete/README.md), and for executable Burgers kernels see
[Exec](../Exec/README.md).
