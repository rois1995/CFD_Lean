"""Symbolic cross-check for the parameter maps, inverse and variance."""
import sympy as s
g,r,h=s.symbols('gamma r h',nonzero=True)
w=s.Matrix(s.symbols('w:3')); n=s.Matrix(s.symbols('n:3'))
def vector(a,b,c):return s.Matrix([a,*b,c])
z=vector(r,w,h);q=w.dot(n)
U=vector(r*r,r*w,(r*h+(g-1)*w.dot(w)/2)/g)
p=(g-1)/g*(r*h-w.dot(w)/2)
F=vector(r*q,w*q+p*n,h*q)
B=U.jacobian(z);C=F.jacobian(z)
v=s.Matrix(s.symbols('d:5')); dm=v[1:4,0];dv0=v[0]/(2*r);dv=(dm-w*dv0)/r
inverse=vector(dv0,dv,(g*v[4]-h*dv0-(g-1)*w.dot(dv))/r).jacobian(v)
def check(label,expr):
 assert all(s.factor(x)==0 for x in (expr if isinstance(expr,s.MatrixBase) else [expr])),label
 print(label,'passed')
check('B determinant',B.det()-2*r**5/g)
check('left inverse',inverse*B-s.eye(5));check('right inverse',B*inverse-s.eye(5))
u=w/r;H=h/r;un=u.dot(n);b=dm.dot(n)-un*v[0];dp=(g-1)*(v[4]-u.dot(dm)+u.dot(u)*v[0]/2)
A=vector(dm.dot(n),un*dm+u*b+dp*n,un*(v[4]+dp)+H*b).jacobian(v)
check('A B = C',A*B-C)
for name,f,df in [('state',U,B),('flux',F,C)]:
 shift=lambda k:f.xreplace(dict(zip(z,z+k*v/2)))
 check(name+' midpoint jump',shift(1)-shift(-1)-df*v)
a=s.symbols('theta');v1=s.Matrix(s.symbols('u:3'));v2=s.Matrix(s.symbols('v:3'))
uv=a*v1+(1-a)*v2
check('variance correction',a*v1.dot(v1)+(1-a)*v2.dot(v2)-uv.dot(uv)-a*(1-a)*(v1-v2).dot(v1-v2))
