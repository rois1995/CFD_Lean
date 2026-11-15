from fractions import Fraction as F
from itertools import combinations

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(s,a):return tuple(s*x for x in a)
def sub(a,b):return add(a,scale(-1,b))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def pressure(U):return U[4]-dot(U[1:4],U[1:4])/(2*U[0])
def physical(U,T):
 q=dot(U[1:4],T)/U[0];p=pressure(U)
 return (dot(U[1:4],T),*add(scale(q,U[1:4]),scale(p,T)),(U[4]+p)*q)
def wall(U,T):return (F(0),*scale(pressure(U),T),F(0))
face=[(F(1,2),)*3,(F(-1,2),0,0),(0,F(-1,2),0),(0,0,F(-1,2))]
rest=(F(1),0,0,0,F(1)); normal=(F(1),0,0,F(1),F(3,2))
def residual(U,mismatch):
 r=[(F(0),)*5 for _ in range(4)];boundary=(F(0),)*5
 for i,j in combinations(range(4),2):
  f=physical(U,scale(F(1,12),sub(face[i],face[j])))
  r[i]=add(r[i],f);r[j]=sub(r[j],f)
 for f in range(4):
  T=scale(F(1,3),face[f])
  for i in range(4):
   if i==f:continue
   if f==3:g=wall(U,T)
   elif mismatch and f==1:
    # rho=1, rest states, p_L=1,p_R=3,cbar=2.
    # Projector formula gives D jump=(1,0,0,0,4).
    area=F(1,6)
    g=sub((F(0),*scale(F(2),T),F(0)),scale(area/2,(F(1),0,0,0,F(4))))
   else:g=physical(U,T)
   r[i]=add(r[i],g);boundary=add(boundary,g)
 assert tuple(sum(v[j] for v in r) for j in range(5))==boundary
 return r
assert residual(normal,False)[0]==(F(1,6),0,0,F(1,6),F(5,12))
assert residual(rest,True)[0]==(F(-1,12),F(-1,6),0,0,F(-1,3))
assert residual(rest,False)==[(F(0),)*5]*4
print('Independent exact standard-tetrahedron edge/patch assembly reproduces compatible zero, wall-incompatible and prescribed-data-incompatible vectors, with global boundary balance.')
