"""Exact small proposal controls; not Lean proofs, mesh validation or M3 implementation."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations

Z = (F(0),) * 3

def add(a, b):
    return tuple(x + y for x, y in zip(a, b))

def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))

def scale(k, a):
    return tuple(k * x for x in a)

def dot(a, b):
    return sum(x * y for x, y in zip(a, b))

def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])

def det(a, b, c):
    return dot(a, cross(b, c))

def center(points):
    return scale(F(1, len(points)), sum_vectors(points))

def sum_vectors(points):
    out = Z
    for p in points:
        out = add(out, p)
    return out

def area(a, b, c):
    return scale(F(1, 2), cross(sub(b, a), sub(c, a)))

def signed_six(points):
    a, b, c, d = points
    return det(sub(b, a), sub(c, a), sub(d, a))

def faces(points):
    a, b, c, d = points
    return [area(b, c, d), scale(-1, area(a, c, d)), area(a, b, d), scale(-1, area(a, b, c))]

def tetra_control(points):
    vol = abs(signed_six(points)) / 6
    assert vol > 0
    c = center(points)
    pieces = defaultdict(list)
    for i, j, k, _ in permutations(range(4)):
        small = [points[i], center([points[i], points[j]]), center([points[i], points[j], points[k]]), c]
        assert abs(signed_six(small)) / 6 == vol / 24
        assert sum_vectors(faces(small)) == Z
        pieces[i].append(abs(signed_six(small)) / 6)
    assert all(len(v) == 6 and sum(v) == vol / 4 for v in pieces.values())
    interfaces = {}
    patches = {}
    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            m = center([points[i], points[j]])
            vectors = []
            for k in set(range(4)) - {i, j}:
                a = area(m, center([points[i], points[j], points[k]]), c)
                if dot(a, sub(points[j], points[i])) < 0:
                    a = scale(-1, a)
                assert dot(a, sub(points[j], points[i])) > 0
                vectors.append(a)
            interfaces[i, j] = sum_vectors(vectors)
        for face in combinations(range(4), 3):
            if i not in face:
                continue
            j, k = sorted(set(face) - {i})
            l = next(iter(set(range(4)) - set(face)))
            f = center([points[v] for v in face])
            aa = [area(points[i], center([points[i], points[j]]), f),
                  area(points[i], f, center([points[i], points[k]]))]
            if dot(aa[0], sub(points[l], points[i])) > 0:
                aa = [scale(-1, a) for a in aa]
            assert all(dot(a, sub(points[l], points[i])) < 0 for a in aa)
            patches[i, face] = sum_vectors(aa)
        assert add(sum_vectors(v for (a, _), v in interfaces.items() if a == i),
                   sum_vectors(v for (a, _), v in patches.items() if a == i)) == Z
    assert all(interfaces[i, j] == scale(-1, interfaces[j, i]) for i, j in interfaces)
    return vol, interfaces, patches

standard = [(F(0), F(0), F(0)), (F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1))]
v, edges, _ = tetra_control(standard)
assert v == F(1, 6) and v / 4 == F(1, 24)
assert edges[0, 1] == (F(1, 12), F(1, 24), F(1, 24))
print('Standard tetrahedron: 24 flag volumes, four dual closures, paired faces; V_i=1/24 and S_01=(1/12,1/24,1/24).')
oblique = [tuple(map(F, p)) for p in [(2, -1, 1), (4, 0, 1), (3, 2, 2), (2, 1, 4)]]
tetra_control(oblique)
print('Oblique affine tetrahedron: all 24 flag volumes, outward normals and four local closures pass.')

coords = standard + [(F(0), F(0), F(-1))]
mesh = [(0, 1, 2, 3), (0, 1, 2, 4)]
counts = Counter(tuple(sorted(f)) for t in mesh for f in combinations(t, 3))
assembled = defaultdict(lambda: Z)
boundary = defaultdict(lambda: Z)
shared = defaultdict(lambda: Z)
volumes = defaultdict(F)
total = F(0)
for t in mesh:
    vol, ee, pp = tetra_control([coords[i] for i in t])
    total += vol
    for i in range(4):
        volumes[t[i]] += vol / 4
    for (i, j), a in ee.items():
        assembled[t[i]] = add(assembled[t[i]], a)
    for (i, f), a in pp.items():
        primal = tuple(sorted(t[k] for k in f))
        target = boundary if counts[primal] == 1 else shared
        target[t[i]] = add(target[t[i]], a)
assert all(a == Z for a in shared.values())
assert all(add(assembled[i], boundary[i]) == Z for i in range(5))
assert all(v > 0 for v in volumes.values()) and sum(volumes.values()) == total
print('Two tetrahedra: shared-face vertex patches cancel; all five assembled duals close; positive volumes sum to primal volume.')

edge_data = [(0, 1, (1, 2, 3, 4, 5)), (1, 2, (2, -1, 4, 0, 3)), (2, 0, (-3, 2, 1, 5, -1))]
bc = [(2, (1, 0, 0, 0, 0))]
def residual(es):
    r = [[0] * 5 for _ in range(3)]
    for i, j, f in es:
        for k in range(5):
            r[i][k] += f[k]
            r[j][k] -= f[k]
    for i, f in bc:
        for k in range(5):
            r[i][k] += f[k]
    return r
rr = residual(edge_data)
assert [sum(r[k] for r in rr) for k in range(5)] == [1, 0, 0, 0, 0]
flipped = [(j, i, tuple(-x for x in f)) for i, j, f in reversed(edge_data)]
assert residual(flipped) == rr
assert rr != [[0] * 5 for _ in range(3)]
print('Three-node incidence: global boundary balance and edge-reversal/reindexing pass; incompatible boundary data are not silently zero.')
assert signed_six(standard[:3] + [(F(1), F(1), F(0))]) == 0
assert max(Counter(tuple(sorted(f)) for t in mesh + [mesh[0]] for f in combinations(t, 3)).values()) == 3
print('Excluded inputs: a planar zero-volume tetrahedron and three-fold primal-face incidence are detected in the controls.')
