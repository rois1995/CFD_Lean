"""Exact rational gamma=2 proposal controls; not Lean proofs or M4 implementation."""
from collections import defaultdict
from fractions import Fraction as F
from math import isqrt


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def scale(k, a):
    return tuple(k * x for x in a)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def state(rho, u, p):
    return (rho, *scale(rho, u), p + rho * dot(u, u) / 2)


def pressure(U):
    return U[4] - dot(U[1:4], U[1:4]) / (2 * U[0])


def physical(U, S):
    mass = dot(U[1:4], S)
    q = mass / U[0]
    return (mass, *add(scale(q, U[1:4]), scale(pressure(U), S)), (U[4] + pressure(U)) * q)


def wall(U, S):
    return (F(0), *scale(pressure(U), S), F(0))


def sqrt_fraction(x):
    a, b = isqrt(x.numerator), isqrt(x.denominator)
    assert a*a == x.numerator and b*b == x.denominator, 'control must have rational square root'
    return F(a, b)


def roe(U, V, S):
    """Independent rational evaluation of the accepted shifted-projector formula."""
    if not any(S):
        return (F(0),)*5
    area = sqrt_fraction(dot(S, S))
    normal = scale(1/area, S)
    rU, rV = sqrt_fraction(U[0]), sqrt_fraction(V[0])
    weight = rU/(rU+rV)
    uU, uV = scale(1/U[0], U[1:4]), scale(1/V[0], V[1:4])
    u = add(scale(weight, uU), scale(1-weight, uV))
    H = weight*(U[4]+pressure(U))/U[0] + (1-weight)*(V[4]+pressure(V))/V[0]
    c = sqrt_fraction(H-dot(u,u)/2)  # gamma=2 for every control
    q = dot(u, normal)
    vb, vp = (F(1), *u, H), (F(0), *normal, q)
    def shift(v):
        b = dot(normal, v[1:4])-q*v[0]
        dp = v[4]-dot(u,v[1:4])+dot(u,u)*v[0]/2
        return add(scale(b, vb), scale(dp, vp))
    jump = sub(V,U)
    B, B2 = shift(jump), shift(shift(jump))
    minus = scale(1/(2*c*c), sub(B2, scale(c,B)))
    plus = scale(1/(2*c*c), add(B2, scale(c,B)))
    zero = sub(jump, scale(1/(c*c),B2))
    D = add(add(scale(abs(q-c),minus),scale(abs(q),zero)),scale(abs(q+c),plus))
    return sub(scale(F(1,2),add(physical(U,S),physical(V,S))),scale(area/2,D))


Z = (F(0),)*3
X = (F(1),F(0),F(0))
rest = state(F(1), Z, F(1))
tangent = state(F(1), (F(1),F(0),F(0)), F(1))
normal_state = state(F(1), (F(0),F(0),F(1)), F(1))
oblique = (F(3),F(4),F(0))
oblique_tangent = state(F(2), (F(4),F(-3),F(1)), F(3))
assert wall(oblique_tangent,oblique) == (0,9,12,0,0) == physical(oblique_tangent,oblique)
assert wall(normal_state, (0,0,F(1))) != physical(normal_state,(0,0,F(1)))
assert wall(rest,Z) == roe(rest,rest,Z) == (0,)*5
assert wall(rest,scale(-1,oblique)) == scale(-1,wall(rest,oblique))
print('Wall controls: exact oblique traction, tangency-qualified physical equality, incompatible normal flow, zero area and reversal pass.')

for speed in [F(3),F(2),F(-3),F(-2)]:
    U = state(F(1),(speed,F(0),F(0)),F(1))
    V = state(F(1),(speed,F(0),F(0)),F(3))
    assert pressure(U)==1 and pressure(V)==3
    assert speed*speed >= 4  # the actual two-state Roe sound speed is c=2
    expected = physical(U if speed>0 else V,X)
    assert roe(U,V,X)==expected
    assert roe(V,U,scale(-1,X))==scale(-1,roe(U,V,X))
    assert roe(U,V,scale(F(2),X))==scale(F(2),roe(U,V,X))
print('Actual rational Roe projector controls: strict/sonic two-state upwind reductions in both directions, swapped reversal and area scaling pass (c=2).')
U = state(F(1),X,F(7,4))
V = state(F(1),scale(-1,X),F(7,4))
assert roe(U,V,X)==(0,F(19,4),0,0,0)
assert wall(U,X)==(0,F(7,4),0,0,0)
assert roe(U,V,X)!=wall(U,X)
assert (6*F(1)+F(2)+F(4))/8==F(3,2)!=F(1)
print('Variant controls: reflected-momentum Roe traction 19/4 differs from direct pressure 7/4; Eq. (8.13) pressure interpolation differs from owner sampling.')
U = state(F(1),Z,F(1))
V = state(F(1),Z,F(3))
assert roe(U,V,X)[0]==F(-1,2)!=physical(U,X)[0]
print('Actual stationary prescribed-exterior Roe mass transfer is -1/2 for a mismatching admissible exterior state; open compatibility is qualified.')

# Accepted standard tetrahedron: face vectors and local interface closed forms.
face = [(F(1,2),F(1,2),F(1,2)), (F(-1,2),0,0), (0,F(-1,2),0), (0,0,F(-1,2))]
edges = {(i,j):scale(F(1,12),sub(face[i],face[j])) for i in range(4) for j in range(i+1,4)}
patches = {(f,i):scale(F(1,3),face[f]) for f in range(4) for i in range(4) if i!=f}


def assembled(U, wall_faces, V):
    residual = defaultdict(lambda:(F(0),)*5)
    boundary = (F(0),)*5
    for (i,j),S in edges.items():
        flux = physical(U,S)  # accepted equal-state Roe identity
        residual[i]=add(residual[i],flux)
        residual[j]=sub(residual[j],flux)
    for (f,i),T in patches.items():
        # Matching exterior state reduces through the accepted Roe consistency identity;
        # arbitrary T may have irrational Euclidean area, so no rational sqrt is asserted here.
        assert V==U
        flux = wall(U,T) if f in wall_faces else physical(U,T)
        residual[i]=add(residual[i],flux)
        boundary=add(boundary,flux)
    total=(F(0),)*5
    for r in residual.values(): total=add(total,r)
    assert total==boundary
    return residual

assert all(r==(0,)*5 for r in assembled(tangent,{3},tangent).values())
assert all(r==(0,)*5 for r in assembled(rest,set(range(4)),rest).values())
r=assembled(normal_state,{3},normal_state)
assert r[0][0]==r[1][0]==r[2][0]==F(1,6) and r[3][0]==0
assert {f for f,i in patches if i==0}=={1,2,3}  # same owner, wall and open faces
print('Concrete accepted tetrahedron controls: mixed wall/open tangential common state and all-wall rest residuals vanish; incompatible common normal flow gives owner mass residual 1/6; corner face IDs and global balance pass.')
print('These are exact feasibility controls using accepted geometry/consistency identities, not new Lean proofs, mesh validation, nonreflection or update guarantees.')
