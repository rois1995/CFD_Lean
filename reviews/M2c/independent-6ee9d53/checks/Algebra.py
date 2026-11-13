import sympy as s
from itertools import product

rho, m1, m2, m3, energy, gamma = s.symbols('rho m1 m2 m3 energy gamma')
state = s.Matrix([rho, m1, m2, m3, energy])
momentum = s.Matrix([m1, m2, m3])
normals = [s.Matrix([1, 0, 0]), s.Matrix([s.Rational(2, 7), s.Rational(3, 7), s.Rational(6, 7)])]
count = 0
for n, c, q in product(normals, [s.Rational(1), s.Rational(2)], [-1, 0, 1]):
    g = s.Rational(7, 5)
    u = q * c * n + s.Matrix([-n[1], n[0], 0])
    H = c**2 / (g - 1) + u.dot(u) / 2
    pressure = (gamma - 1) * (energy - momentum.dot(momentum) / (2 * rho))
    vn = momentum.dot(n) / rho
    flux = s.Matrix([momentum.dot(n), *(vn * momentum + pressure * n), (energy + pressure) * vn])
    total_energy = (H + (g - 1) * u.dot(u) / 2) / g
    A = flux.jacobian(state).subs(dict(zip([rho, m1, m2, m3, energy, gamma], [1, *u, total_energy, g])))
    N = A - u.dot(n) * s.eye(5)
    P = [(N*N-c*N)/(2*c*c), s.eye(5)-N*N/(c*c), (N*N+c*N)/(2*c*c)]
    assert N**3 == c*c*N
    assert [p.rank() for p in P] == [1, 3, 1]
    assert sum(P, s.zeros(5)) == s.eye(5)
    for i, j in product(range(3), repeat=2):
        assert P[i]*P[j] == (P[i] if i == j else s.zeros(5))
    speeds = [u.dot(n)-c, u.dot(n), u.dot(n)+c]
    for i in range(3):
        assert A*P[i] == speeds[i]*P[i]
    D = sum([abs(v)*p for v, p in zip(speeds, P)], s.zeros(5))
    R = s.Matrix.hstack(*[v for p in P for v in p.columnspace()])
    values = [speeds[0], speeds[1], speeds[1], speeds[1], speeds[2]]
    assert R.det() != 0
    assert D == R*s.diag(*map(abs, values))*R.inv()
    count += 1
print(f'{count} exact Jacobian/projector/basis controls passed, including stationary, sonic and oblique cases.')
