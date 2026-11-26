from fractions import Fraction as Fr
import itertools, numpy as np
quads=[(0,1,2,3),(4,5,6,7),(0,1,5,4),(1,2,6,5),(2,3,7,6),(3,0,4,7)]
edges=[(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4),(0,4),(1,5),(2,6),(3,7)]
def nbr(v,w): return (v,w) in edges or (w,v) in edges
def qtris(q,d):
    a,b,c,dd=q; return [[a,b,dd],[b,c,dd]] if d else [[a,b,c],[a,c,dd]]
def diag(q,d): return (q[1],q[3]) if d else (q[0],q[2])
def allBools(k):
    if k==0: return [[]]
    return [x for l in allBools(k-1) for x in ([False]+l,[True]+l)]
def pull(v,ch):
    out=[]
    for j,q in enumerate(quads):
        if v in q: continue
        out+=[[v]+t for t in qtris(q,ch[j])]
    return out
splits=[(v,ch) for v in range(8) for ch in allBools(6) if all((v not in q) or (not ch[j]) for j,q in enumerate(quads))]
def fan(s):
    v,ch=s
    for j,q in enumerate(quads):
        if v in q: continue
        ws=[w for w in q if nbr(v,w)]
        if len(ws)==1:
            e=diag(q,ch[j])
            if ws[0] not in e: return False
    return True
fans=[s for s in splits if fan(s)]
print("splits",len(splits),"fan",len(fans))
ref=[(0,0,0),(1,0,0),(1,1,0),(0,1,0),(0,0,1),(1,0,1),(1,1,1),(0,1,1)]
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def crs(u,v): return (u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
def dt(u,v): return sum(x*y for x,y in zip(u,v))
def side(a,b,c,x): return dt(crs(sub(b,a),sub(c,a)),sub(x,a))
def tdet(P,t): return side(P[t[0]],P[t[1]],P[t[2]],P[t[3]])
def cellX(c,s,lam,cx,cy):
    # bottom unit square, top = lam*R(p - (cx,cy)) + (cx,cy)
    X=[]
    for i,(x,y,z) in enumerate(ref):
        if z==0: X.append((Fr(x),Fr(y),Fr(0)))
        else:
            dx,dy=x-cx,y-cy
            X.append((cx+lam*(c*dx-s*dy), cy+lam*(s*dx+c*dy), Fr(1)))
    return X
trip=[(3,4,5),(5,12,13),(8,15,17),(7,24,25),(20,21,29)]
angs=[]
for a,b,h in trip:
    for (c,s) in [(Fr(a,h),Fr(b,h)),(Fr(b,h),Fr(a,h)),(Fr(-a,h),Fr(b,h)),(Fr(-b,h),Fr(a,h))]: angs.append((c,s))
res=[]
for c,s in angs:
  for lam in [Fr(1),Fr(1,2),Fr(2),Fr(3,2),Fr(2,3)]:
    for cx,cy in [(Fr(1,2),Fr(1,2)),(Fr(0),Fr(0)),(Fr(1),Fr(1)),(Fr(0),Fr(1,2))]:
      X=cellX(c,s,lam,cx,cy)
      kt=set(tuple(t) for f in fans for t in pull(*f))
      bad=[t for t in kt if tdet(X,t)*tdet(ref,t)<=0]
      if bad: res.append((float(np.degrees(np.arctan2(float(s),float(c)))),str(c),str(s),str(lam),(str(cx),str(cy)),len(bad),bad[0]))
res.sort()
print(len(res)); [print(r) for r in res[:12]]

print("--- 90 deg, centre (1/2,1/2)")
X=cellX(Fr(0),Fr(1),Fr(1),Fr(1,2),Fr(1,2))
kt=set(tuple(t) for f in fans for t in pull(*f))
print("Kuhn bad",[ (t,tdet(X,t)) for t in kt if tdet(X,t)*tdet(ref,t)<=0][:4])
for c,s in [(Fr(-7,25),Fr(24,25))]:
    X=cellX(c,s,Fr(1),Fr(1,2),Fr(1,2))
    # same-side pair in a fan split
    for f in fans:
        T=pull(*f)
        for t in T:
            for t2 in T:
                if t==t2: continue
                sh=[x for x in t if x in t2]
                if len(sh)==3:
                    o1=[x for x in t if x not in sh][0]; o2=[x for x in t2 if x not in sh][0]
                    a,b,cc=sh
                    p=side(X[a],X[b],X[cc],X[o1])*side(X[a],X[b],X[cc],X[o2])
                    if p>0: print("fan split",f,"tets",t,t2,"shared",sh,"product",p); break
            else: continue
            break
        else: continue
        break
print("--- (b) 2x2x2 block, middle layer turned by theta about (1,1)")
def block(c,s):
    P={}
    for i in range(3):
        for j in range(3):
            for k in range(3):
                x,y=Fr(i),Fr(j)
                if k==1:
                    dx,dy=x-1,y-1; x,y=1+c*dx-s*dy, 1+s*dx+c*dy
                P[(i,j,k)]=(x,y,Fr(k))
    cells=[]
    for i in range(2):
        for j in range(2):
            for k in range(2):
                loc=[(0,0,0),(1,0,0),(1,1,0),(0,1,0),(0,0,1),(1,0,1),(1,1,1),(0,1,1)]
                cells.append([(i+a,j+b,k+d) for a,b,d in loc])
    return P,cells
def facetvec(X,t,o):
    # area vector of facet opposite t[o], outward from the tet: -(1/2) sign(side) cross
    idx=[a for a in range(4) if a!=o]; n=[X[t[a]] for a in idx]
    sd=side(n[0],n[1],n[2],X[t[o]]); cr=crs(sub(n[1],n[0]),sub(n[2],n[0]))
    sg=(sd>0)-(sd<0)
    return tuple(Fr(-sg,2)*x for x in cr)
for c,s in [(Fr(3,5),Fr(4,5)),(Fr(4,5),Fr(3,5)),(Fr(0),Fr(1)),(Fr(-7,25),Fr(24,25))]:
    P,cells=block(c,s)
    O=(1,1,1); tot=[Fr(0)]*3; inv=0
    for cell in cells:
        X=[P[v] for v in cell]
        for sp in splits:
            for t in pull(*sp):
                if tdet(X,t)*tdet(ref,t)<=0: inv+=1
                for o in range(4):
                    nodes=[cell[t[a]] for a in range(4) if a!=o]
                    if O in nodes:
                        fv=facetvec(X,t,o); tot=[x+Fr(1,64)*y for x,y in zip(tot,fv)]
    print("cos",c,"sin",s,"inverted tet instances",inv,"sum of facet vectors at O",[str(x) for x in tot])

print("--- (b) off-centre axis (ax,ay)")
def block2(c,s,ax,ay):
    P={}
    for i in range(3):
        for j in range(3):
            for k in range(3):
                x,y=Fr(i),Fr(j)
                if k==1:
                    dx,dy=x-ax,y-ay; x,y=ax+c*dx-s*dy, ay+s*dx+c*dy
                P[(i,j,k)]=(x,y,Fr(k))
    return P
_,cells=block(Fr(1),Fr(0))
def sumO(P):
    O=(1,1,1); tot=[Fr(0)]*3; inv=0
    for cell in cells:
        X=[P[v] for v in cell]
        for sp in splits:
            for t in pull(*sp):
                if tdet(X,t)*tdet(ref,t)<=0: inv+=1
                for o in range(4):
                    nodes=[cell[t[a]] for a in range(4) if a!=o]
                    if O in nodes:
                        fv=facetvec(X,t,o); tot=[x+Fr(1,64)*y for x,y in zip(tot,fv)]
    return inv,tot
for c,s in [(Fr(3,5),Fr(4,5)),(Fr(0),Fr(1))]:
    for ax,ay in [(Fr(1,2),Fr(1,2)),(Fr(0),Fr(0)),(Fr(1,2),Fr(1)),(Fr(1),Fr(1,2))]:
        inv,tot=sumO(block2(c,s,ax,ay))
        print("cos",c,"axis",(str(ax),str(ay)),"inverted",inv,"sum at O",[str(x) for x in tot])

print("--- (b) layers turned independently")
rots=[(Fr(1),Fr(0)),(Fr(3,5),Fr(4,5)),(Fr(4,5),Fr(3,5)),(Fr(0),Fr(1)),(Fr(3,5),Fr(-4,5)),(Fr(-7,25),Fr(24,25))]
axes=[(Fr(1),Fr(1)),(Fr(0),Fr(0)),(Fr(1,2),Fr(1)),(Fr(2),Fr(0))]
def block3(L):
    P={}
    for i in range(3):
        for j in range(3):
            for k in range(3):
                (c,s),(ax,ay)=L[k]
                dx,dy=Fr(i)-ax,Fr(j)-ay
                P[(i,j,k)]=(ax+c*dx-s*dy, ay+s*dx+c*dy, Fr(k))
    return P
found=[]
for r0 in rots[:1]:
  for r1 in rots:
    for r2 in rots:
      for a1 in axes:
        for a2 in axes[:2]:
          L=[(r0,axes[0]),(r1,a1),(r2,a2)]
          # validity: relative rotation angle between consecutive layers must not be 180 deg: always fine here
          inv,tot=sumO(block3(L))
          if any(x!=0 for x in tot):
              found.append((inv,[str(x) for x in tot],[str(r1),str(a1),str(r2),str(a2)]))
print(len(found)); [print(f) for f in found[:8]]

print("--- (b) chosen: top layer turned (3/5,4/5) about (1,1); conformity check")
L=[((Fr(1),Fr(0)),(Fr(1),Fr(1))),((Fr(1),Fr(0)),(Fr(1),Fr(1))),((Fr(3,5),Fr(4,5)),(Fr(1),Fr(1)))]
P=block3(L)
cen=[tuple(sum(P[v][a] for v in cell)/8 for a in range(3)) for cell in cells]
facetris_loc=[]
for q in quads:
    for d in (False,True): facetris_loc+= [tuple(t) for t in qtris(q,d)]
tri_cells={}
for ci,cell in enumerate(cells):
    for t in facetris_loc:
        S=frozenset(cell[a] for a in t); tri_cells.setdefault(S,set()).add(ci)
ok=True; shared=0
for S,cs in tri_cells.items():
    if len(cs)==2:
        shared+=1; a,b,c=sorted(S); c1,c2=sorted(cs)
        if not side(P[a],P[b],P[c],cen[c1])*side(P[a],P[b],P[c],cen[c2])<0: ok=False; print("bad",S)
    assert len(cs)<=2
print("shared triangles",shared,"conform ok",ok,"boundary triangles",sum(1 for cs in tri_cells.values() if len(cs)==1))
O=(1,1,1); print("O on boundary triangle:",any(O in S for S,cs in tri_cells.items() if len(cs)==1))
print("inverted per cell",[sum(1 for sp in splits for t in pull(*sp) if tdet([P[v] for v in cell],t)*tdet(ref,t)<=0) for cell in cells])

print("--- coordinates")
X=cellX(Fr(-7,25),Fr(24,25),Fr(1),Fr(1,2),Fr(1,2)); print("kuhnX",[tuple(str(v) for v in p) for p in X])
print("block top layer", [ (i,j,tuple(str(v) for v in P[(i,j,2)])) for j in range(3) for i in range(3)])

print("--- replica of Lean defs")
rx=[0,1,1,0,0,1,1,0]; ry=[0,0,1,1,0,0,1,1]; rz=[0,0,0,0,1,1,1,1]
def bpos(g):
    i,j,k=g%3,g//3%3,g//9
    if k==2: return (1+Fr(3,5)*(i-1)-Fr(4,5)*(j-1), 1+Fr(4,5)*(i-1)+Fr(3,5)*(j-1), Fr(2))
    return (Fr(i),Fr(j),Fr(k))
def bidx(c,a): return ((c%2+rx[a])+3*(c//2%2+ry[a])+9*(c//4+rz[a]))%27
cellsL=[[bidx(c,a) for a in range(8)] for c in range(8)]
assert all(len(set(cl))==8 for cl in cellsL)
tri={}
for ci,cl in enumerate(cellsL):
    for t in facetris_loc: tri.setdefault(frozenset(cl[a] for a in t),set()).add(ci)
cenL=[tuple(sum(bpos(g)[d] for g in cl)/8 for d in range(3)) for cl in cellsL]
ok=all(side(*[bpos(x) for x in sorted(S)],cenL[min(cs)])*side(*[bpos(x) for x in sorted(S)],cenL[max(cs)])<0 for S,cs in tri.items() if len(cs)==2)
print("conform",ok,"13 on bd",any(13 in S for S,cs in tri.items() if len(cs)==1))
tot=[Fr(0)]*3
for cl in cellsL:
    X=[bpos(g) for g in cl]
    for sp in splits:
        for t in pull(*sp):
            for o in range(4):
                if 13 in [cl[t[a]] for a in range(4) if a!=o]:
                    tot=[x+Fr(1,64)*y for x,y in zip(tot,facetvec(X,t,o))]
print("beta-part at 13 (sum facet vectors /3 = beta):",[str(x) for x in tot])
# Kuhn check with kuhnX literal
KX=[(Fr(0),Fr(0),Fr(0)),(Fr(1),Fr(0),Fr(0)),(Fr(1),Fr(1),Fr(0)),(Fr(0),Fr(1),Fr(0)),(Fr(28,25),Fr(4,25),Fr(1)),(Fr(21,25),Fr(28,25),Fr(1)),(Fr(-3,25),Fr(21,25),Fr(1)),(Fr(4,25),Fr(-3,25),Fr(1))]
print("kuhnX same-side product", side(KX[0],KX[5],KX[6],KX[4])*side(KX[0],KX[5],KX[6],KX[1]))
