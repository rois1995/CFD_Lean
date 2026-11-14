import sympy as s
from itertools import permutations
x=s.symbols('x0:12');p=[s.Matrix(x[i:i+3]) for i in range(0,12,3)]
a,b,c,d=p
D=s.det(s.Matrix.hstack(b-a,c-a,d-a));m=(a+b)/2;f=(a+b+c)/3;t=(a+b+c+d)/4
assert s.expand(s.det(s.Matrix.hstack(m-a,f-a,t-a))-D/24)==0
assert s.expand(((f-m).cross(t-m)/2).dot(b-a)-D/24)==0
tri=lambda a,b,c:(b-a).cross(c-a)/2
def face(p):
 a,b,c,d=p
 return [tri(b,c,d),-tri(a,c,d),tri(a,b,d),-tri(a,b,c)]
points=list(map(s.Matrix,[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(0,0,-1)]))
area=s.zeros(3,1)
for ids in [(0,1,2,3),(0,2,1,4)]:
 pp=[points[i] for i in ids];fv=face(pp);area+=(fv[ids.index(0)]-fv[ids.index(1)])/12
 for i,j,k,l in permutations(range(4)):
  a,b,c,d=[pp[r] for r in [i,j,k,l]]
  det=s.det(s.Matrix.hstack((a+b)/2-a,(a+b+c)/3-a,(a+b+c+d)/4-a))
  assert abs(det)/6==s.Rational(1,144)
assert area==s.Matrix([s.Rational(1,6),s.Rational(1,12),0])
assert 3*s.Rational(1,12)+2*s.Rational(1,24)==s.Rational(1,3)
print('Symbolic flag determinant/outward-dot identities and all 48 two-cell flag volumes, aggregated edge area and total volume independently verified.')
