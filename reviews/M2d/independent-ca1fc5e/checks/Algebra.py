import sympy as s

rho, mx, my, mz, energy, gamma, nx, ny, nz = s.symbols('rho mx my mz E gamma nx ny nz')
variables = s.Matrix([rho, mx, my, mz, energy])
momentum = s.Matrix([mx, my, mz])
direction = s.Matrix([nx, ny, nz])
pressure = (gamma-1)*(energy-momentum.dot(momentum)/(2*rho))
normal_velocity = momentum.dot(direction)/rho
physical = s.Matrix([momentum.dot(direction), *(normal_velocity*momentum+pressure*direction), (energy+pressure)*normal_velocity])
jacobian = physical.jacobian(variables)

def simplify(v):
    return v.applyfunc(s.simplify)

def state(r, u, p, g):
    u = s.Matrix(u)
    return s.Matrix([r, *(r*u), p/(g-1)+r*u.dot(u)/2])

def flux(U, S, g):
    return simplify(physical.subs(dict(zip([*variables, gamma, nx, ny, nz], [*U, g, *S]))))

def operator(U, V, n, g):
    r, t = U[0], V[0]
    u, v = U[1:4], V[1:4]
    u, v = s.Matrix(u)/r, s.Matrix(v)/t
    p = (g-1)*(U[4]-r*u.dot(u)/2)
    z = (g-1)*(V[4]-t*v.dot(v)/2)
    a = s.sqrt(r)/(s.sqrt(r)+s.sqrt(t))
    b = 1-a
    mean = simplify(a*u+b*v)
    H = s.simplify(a*(U[4]+p)/r+b*(V[4]+z)/t)
    c = s.sqrt(s.simplify((g-1)*(H-mean.dot(mean)/2)))
    E = (H+(g-1)*mean.dot(mean)/2)/g
    A = simplify(jacobian.subs(dict(zip([*variables, gamma, nx, ny, nz], [1, *mean, E, g, *n]))))
    q = mean.dot(n)
    N = A-q*s.eye(5)
    P = [simplify((N*N-c*N)/(2*c*c)), simplify(s.eye(5)-N*N/(c*c)), simplify((N*N+c*N)/(2*c*c))]
    speeds = [q-c, q, q+c]
    D = simplify(sum([abs(speed)*projector for speed, projector in zip(speeds, P)], s.zeros(5)))
    assert simplify(A*(V-U)-(flux(V,n,g)-flux(U,n,g))) == s.zeros(5,1)
    return D, P, q, c

def roe(U,V,S,g):
    area = s.sqrt(S.dot(S))
    if area == 0:
        return s.zeros(5,1)
    D, _, _, _ = operator(U,V,S/area,g)
    return simplify((flux(U,S,g)+flux(V,S,g)-area*D*(V-U))/2)

g = s.Rational(2)
cases = [
    (state(1,[3,0,0],1,g),state(4,[3,0,0],1,g),s.Matrix([2,0,0])),
    (state(1,[-3,0,0],1,g),state(4,[-3,0,0],1,g),s.Matrix([2,0,0])),
    (state(1,[1,0,0],1,g),state(4,[1,0,0],1,g),s.Matrix([2,0,0])),
    (state(1,[-1,0,0],1,g),state(4,[-1,0,0],1,g),s.Matrix([2,0,0])),
    (state(1,[-2,0,0],s.Rational(1,2),g),state(1,[2,0,0],s.Rational(1,2),g),s.Matrix([3,0,0])),
    (state(1,[0,1,0],1,g),state(1,[0,-1,0],1,g),s.Matrix([2,3,6])),
]
for U,V,S in cases:
    f = roe(U,V,S,g)
    assert simplify(roe(V,U,-S,g)+f) == s.zeros(5,1)
    assert simplify(roe(U,V,3*S,g)-3*f) == s.zeros(5,1)
    assert roe(U,V,s.zeros(3,1),g) == s.zeros(5,1)
    assert simplify(roe(U,U,S,g)-flux(U,S,g)) == s.zeros(5,1)
    D,P,q,c = operator(U,V,S/s.sqrt(S.dot(S)),g)
    if q >= c:
        assert simplify(f-flux(U,S,g)) == s.zeros(5,1)
    if q <= -c:
        assert simplify(f-flux(V,S,g)) == s.zeros(5,1)
U,V,_ = cases[4]
_,P,_,c = operator(U,V,s.Matrix([1,0,0]),g)
star = simplify(U+P[0]*(V-U))
assert star == s.Matrix([1-2/s.sqrt(3),0,0,0,s.Rational(5,2)-2*s.sqrt(3)])
assert star[0] < 0 and c*c == 3
print('Six exact two-state controls passed: consistency, reversal, scaling, zero area, secant and applicable upwinding, including both sonic equalities and oblique dissipation.')
print('Same-projector full intermediate vector and negative density independently reproduced.')
