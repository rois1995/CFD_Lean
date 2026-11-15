from fractions import Fraction as F
from itertools import combinations
from random import Random

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def scale(s,a):return tuple(s*x for x in a)
def total(xs):
 s=(F(0),)*5
 for x in xs:s=add(s,x)
 return s

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def p(U):return U[4]-dot(U[1:4],U[1:4])/(2*U[0])
def physical(U,T):
 v=dot(U[1:4],T)/U[0]
 return (dot(U[1:4],T),*add(scale(v,U[1:4]),scale(p(U),T)),(U[4]+p(U))*v)
def wall(U,T):return (F(0),*scale(p(U),T),F(0))
z=(F(0),)*5;face=[(F(1,2),)*3,(F(-1,2),0,0),(0,F(-1,2),0),(0,0,F(-1,2))]
def scatter(U,hot_cold=False):
 R=[z for _ in range(4)];edge={};boundary={}
 for i,j in combinations(range(4),2):
  edge[i,j]=physical(U,scale(F(1,12),sub(face[i],face[j])))
  R[i]=add(R[i],edge[i,j]);R[j]=sub(R[j],edge[i,j])
 for f in range(4):
  T=scale(F(1,3),face[f])
  for i in range(4):
   if i==f:continue
   if hot_cold and f==1:
    # Rest p_L=3,p_R=1: cbar=2; A^2 jump=(-2,0,0,0,-8),
    # hence |A| jump=A^2 jump/2=(-1,0,0,0,-4).
    flux=sub((F(0),*scale(F(2),T),F(0)),scale(F(1,12),(F(-1),0,0,0,F(-4))))
   else:flux=wall(U,T)
   boundary[f,i]=flux;R[i]=add(R[i],flux)
 return R,edge,boundary
U=(F(1),0,0,F(1),F(3,2));R,edge,boundary=scatter(U)
r=(F(1,6),0,0,F(1,6),F(5,12));assert R==[r,z,z,scale(-1,r)]
tau=[F(1,48)]*3+[F(1,24)]
updated=[sub(U,scale(t/F(1,24),res)) for t,res in zip(tau,R)]
assert all(x[0]>0 and p(x)>0 for x in updated)
change=total(scale(F(1,24),sub(x,U)) for x in updated)
assert change==(F(1,288),0,0,F(1,288),F(5,576))
assert change==scale(-1,add(total(scale(tau[i]-tau[j],f) for (i,j),f in edge.items()),total(scale(tau[i],g) for (_,i),g in boundary.items())))
assert total(R)==z
hot=(F(1),0,0,0,F(3));R,_,_=scatter(hot,True)
assert R[0]==(F(1,12),F(1,6),0,0,F(1,3))
assert sub(hot,scale(F(24),R[0]))==(-1,-4,0,0,-5)
print('Independent standard-tetrahedron assembly reproduces both M5 vectors, admissible unequal-step output states, and the hot/cold negative-density update.')

# Supplementary finite-incidence algebra and nonconstant data transport.
rng=Random(15);count=0
for trial in range(300):
 n=6;used=set(range(5));vol=[F(i+1,24) for i in range(5)]+[F(0)]
 steps=[F(rng.randrange(0,9),48) for _ in range(n)]
 states=[tuple(F(rng.randrange(-4,5),3) for _ in range(5)) for _ in range(n)]
 edges={(0,1):tuple(F(rng.randrange(-4,5),3) for _ in range(5)),(1,3):tuple(F(rng.randrange(-4,5),3) for _ in range(5)),(2,4):tuple(F(rng.randrange(-4,5),3) for _ in range(5))}
 borders={(0,0):tuple(F(rng.randrange(-4,5),3) for _ in range(5)),(1,2):tuple(F(rng.randrange(-4,5),3) for _ in range(5))}
 rr=[z]*n
 for (i,j),f in edges.items():rr[i]=add(rr[i],f);rr[j]=sub(rr[j],f)
 for (_,i),g in borders.items():rr[i]=add(rr[i],g)
 def update(v,ts,u,res,mask):return [sub(u[i],scale(ts[i]/v[i],res[i])) if i in mask else u[i] for i in range(n)]
 plus=update(vol,steps,states,rr,used)
 dq=total(scale(vol[i],sub(plus[i],states[i])) for i in range(n))
 rhs=scale(-1,add(total(scale(steps[i]-steps[j],f) for (i,j),f in edges.items()),total(scale(steps[i],g) for (_,i),g in borders.items())))
 assert dq==rhs and plus[5]==states[5]
 perm=[3,5,1,0,4,2]
 def transport(xs):
  ys=[None]*n
  for i in range(n):ys[perm[i]]=xs[i]
  return ys
 assert transport(plus)==update(transport(vol),transport(steps),transport(states),transport(rr),{perm[i] for i in used})
 assert total(scale(vol[i],plus[i]) for i in range(n))==total(scale(vol[i],plus[i]) for i in used)
 count+=1
print(f'{count} exact rational finite-incidence/local-step/unused-node/transport cases pass. These supplement algebraic review and do not prove any proposed Lean contract.')
