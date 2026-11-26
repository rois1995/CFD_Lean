import numpy as np, itertools
rng=np.random.default_rng(1)
# unit cube vertices, index = x + 2y + 4z
V0=np.array([[i&1,(i>>1)&1,(i>>2)&1] for i in range(8)],float)
faces=[(0,1,3,2),(4,5,7,6),(0,1,5,4),(2,3,7,6),(0,2,6,4),(1,3,7,5)]  # cyclic
def splits():
    out=[]
    for v in range(8):
        fs=[f for f in faces if v not in f]
        for ch in itertools.product([0,1],repeat=len(fs)):
            tets=[]
            for f,c in zip(fs,ch):
                a,b,cc,d=f
                tris=[(a,b,cc),(a,cc,d)] if c==0 else [(a,b,d),(b,cc,d)]
                for t in tris: tets.append((v,)+t)
            out.append(tets)
    return out
S=splits()
def vol(X,t):
    v,a,b,c=t; return np.linalg.det(np.array([X[a]-X[v],X[b]-X[v],X[c]-X[v]]))
ref={t:np.sign(vol(V0,t)) for s in S for t in s}
assert all(abs(vol(V0,t))>1e-12 for t in ref)
def trijac(X,n=5):
    m=np.inf
    for u,v,w in itertools.product(np.linspace(0,1,n),repeat=3):
        J=np.zeros((3,3))
        for i in range(8):
            x,y,z=V0[i]
            dx=(1 if x else -1)*(v if y else 1-v)*(w if z else 1-w)
            dy=(u if x else 1-u)*(1 if y else -1)*(w if z else 1-w)
            dz=(u if x else 1-u)*(v if y else 1-v)*(1 if z else -1)
            J+=np.outer(X[i],[dx,dy,dz])
        m=min(m,np.linalg.det(J))
    return m
for amp in [0.1,0.2,0.3,0.4]:
    n_valid=n_bad=0; worst=None
    for trial in range(1500):
        X=V0+amp*rng.uniform(-1,1,(8,3))
        if trijac(X)<=0: continue
        n_valid+=1
        bad=sum(1 for t in ref if np.sign(vol(X,t))!=ref[t] or abs(vol(X,t))<1e-14)
        badsplits=sum(1 for s in S if any(np.sign(vol(X,t))!=ref[t] for t in s))
        if bad: n_bad+=1; worst=max(worst or 0,badsplits)
    print(f"amp {amp}: valid trilinear {n_valid}, with inverted pulling tets {n_bad}, max bad splits {worst}")
print("distinct tets", len(ref))

def nbr(v): return [v^1,v^2,v^4]
def kuhn():
    out=[]
    for v in range(8):
        tets=[]
        for f in faces:
            if v in f: continue
            a,b,c,d=f
            n=[x for x in f if x in nbr(v)]; assert len(n)==1; n=n[0]
            tris=[(a,b,c),(a,c,d)] if n in (a,c) else [(a,b,d),(b,c,d)]
            for t in tris: tets.append((v,)+t)
        out.append(tets)
    return out
K=kuhn()
rng=np.random.default_rng(2)
for amp in [0.2,0.3,0.4]:
    nv=nb=0; ex=None
    for trial in range(1500):
        X=V0+amp*rng.uniform(-1,1,(8,3))
        if trijac(X,7)<=0: continue
        nv+=1
        if any(np.sign(vol(X,t))!=ref[t] for s in K for t in s):
            nb+=1
            if ex is None: ex=X
    print(f"Kuhn subset, amp {amp}: valid trilinear {nv}, with an inverted Kuhn tet {nb}")
np.set_printoptions(precision=3,suppress=True)
print(ex)

print("--- one moved vertex, |p|_1 < 1 (trilinear Jacobian > 0 everywhere)")
kt=set(t for s in K for t in s)
best=[]
from fractions import Fraction
grid=[Fraction(k,10) for k in range(-9,10)]
for j in range(8):
  for px in grid:
    for py in grid:
      for pz in grid:
        if abs(px)+abs(py)+abs(pz)>=1: continue
        X=V0.copy(); X[j]+=np.array([float(px),float(py),float(pz)])
        badK=[t for t in kt if np.sign(vol(X,t))!=ref[t]]
        badP=[t for t in ref if np.sign(vol(X,t))!=ref[t]]
        if badP: best.append((abs(px)+abs(py)+abs(pz),j,(px,py,pz),len(badK),len(badP)))
best.sort()
for b in best[:6]: print(b[0], "vertex",b[1],"p",tuple(str(x) for x in b[2]),"bad Kuhn tets",b[3],"bad pulling tets",b[4])
print("any Kuhn inversion:", [b for b in best if b[3]>0][:3])

print("--- twisted cube: top face rotated by theta about the vertical axis through the centre")
def twist(th):
    X=V0.copy()
    for i in range(4,8):
        x,y=X[i,0]-0.5,X[i,1]-0.5
        X[i,0]=0.5+np.cos(th)*x-np.sin(th)*y; X[i,1]=0.5+np.sin(th)*x+np.cos(th)*y
    return X
for deg in range(5,90,5):
    X=twist(np.radians(deg))
    badK=sum(1 for t in kt if np.sign(vol(X,t))!=ref[t])
    badP=sum(1 for t in ref if np.sign(vol(X,t))!=ref[t])
    badKs=sum(1 for s in K if any(np.sign(vol(X,t))!=ref[t] for t in s))
    print(deg, "minJ %.3f"%trijac(X,9), "bad pulling tets",badP,"bad Kuhn tets",badK,"bad Kuhn splits",badKs)

print("--- facet balance of the one-cell mesh, twisted cube cos=3/5 sin=4/5")
def twistcs(c,s):
    X=V0.copy()
    for i in range(4,8):
        x,y=X[i,0]-0.5,X[i,1]-0.5
        X[i,0]=0.5+c*x-s*y; X[i,1]=0.5+s*x+c*y
    return X
def facetvecs(X,t):
    P=np.array([X[v] for v in t]); E=np.array([P[k]-P[0] for k in (1,2,3)]).T
    vol=abs(np.linalg.det(E))/6; Ei=np.linalg.inv(E)
    g=[-Ei.sum(axis=0)]+[Ei[k] for k in range(3)]
    return {frozenset(x for j,x in enumerate(t) if j!=o): -(3*vol)*g[o] for o in range(4)}
facetris=set()
for f in faces:
    a,b,c,d=f
    for tr in [(a,b,c),(a,c,d),(a,b,d),(b,c,d)]: facetris.add(frozenset(tr))
for name,X in [("cube",V0),("twist 3/5",twistcs(0.6,0.8))]:
    acc={}
    for s in S:
        for t in s:
            for k,v in facetvecs(X,t).items():
                acc[k]=acc.get(k,0)+v/64
    bad={k:v for k,v in acc.items() if k not in facetris and np.linalg.norm(v)>1e-12}
    print(name,"interior triangles",sum(1 for k in acc if k not in facetris),"unbalanced",len(bad))
    for k,v in list(bad.items())[:4]: print(sorted(k),v)
    # Kuhn-only family
    acc={}
    for s in K:
        for t in s:
            for k,v in facetvecs(X,t).items(): acc[k]=acc.get(k,0)+v/8
    print(name,"Kuhn family unbalanced",sum(1 for k,v in acc.items() if k not in facetris and np.linalg.norm(v)>1e-12))
