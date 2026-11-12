"""Independent exact algebra for reviewing the M2 proposal. Run with Python and SymPy."""
import sympy as s
M=s.Matrix
g,r,E,H=s.symbols('g r E H', nonzero=True)
n=M(s.symbols('nx ny nz')); m=M(s.symbols('mx my mz'))
V=M(s.symbols('dr dmx dmy dmz de'))
dm=V[1:4,0]
def join(x,y,z): return M([x,*y,z])
def check(name,x):
    vals=list(x) if isinstance(x,s.MatrixBase) else [x]
    assert all(s.factor(v)==0 for v in vals),name
    print('PASS',name)
def J(u,H,n):
    q=u.dot(n); b=n.dot(dm)-q*V[0]; dp=(g-1)*(V[4]-u.dot(dm)+u.dot(u)*V[0]/2)
    return join(n.dot(dm),q*dm+u*b+dp*n,q*(V[4]+dp)+H*b).jacobian(V)
p=(g-1)*(E-m.dot(m)/(2*r)); u=m/r
F=join(n.dot(m),m*u.dot(n)+p*n,(E+p)*u.dot(n))
check('physical Jacobian, arbitrary normal', F.jacobian(join(r,m,E))-J(u,(E+p)/r,n))
z0,zh=s.symbols('z0 zh',nonzero=True); v=M(s.symbols('zx zy zz')); z=join(z0,v,zh)
U=join(z0**2,z0*v,(z0*zh+(g-1)*v.dot(v)/2)/g)
pz=(g-1)/g*(z0*zh-v.dot(v)/2)
Fz=join(z0*v.dot(n),v*v.dot(n)+pz*n,zh*v.dot(n))
B=U.jacobian(z); C=Fz.jacobian(z)
check('det B',B.det()-2*z0**5/g)
check('Roe matrix times B equals C',J(v/z0,zh/z0,n)*B-C)
for name,f in [('U',U),('F',Fz)]:
    shift=lambda k:f.xreplace(dict(zip(z,z+k*V/2)))
    check(name+' exact midpoint jump',shift(1)-shift(-1)-f.jacobian(z)*V)
c=s.sqrt(3); normal=M([1,0,0]); I=s.eye(5)
N=J(s.zeros(3,1),3,normal).subs(g,2)
Pm=(N**2-c*N)/(2*c**2)
star=M([1,-2,0,0,s.Rational(5,2)])+Pm*M([0,4,0,0,0])
check('receding-state intermediate vector',star-M([1-2/c,0,0,0,s.Rational(5,2)-2*c]))
assert star[0]<0
print('PASS negative intermediate density')
# Oblique rational frame; velocity and sound speed symbolic in two tangential directions.
q,h1,h2,c=s.symbols('q h1 h2 c', nonzero=True)
n=M([3,4,0])/5; t=M([-4,3,0])/5; t2=M([0,0,1])
u=q*n+h1*t+h2*t2; H=c**2/(g-1)+u.dot(u)/2
A=J(u,H,n); I=s.eye(5); N=A-q*I
R=M.hstack(join(1,u-c*n,H-c*q),join(1,u,u.dot(u)/2),
           join(0,t,u.dot(t)),join(0,t2,u.dot(t2)),join(1,u+c*n,H+c*q))
L=s.diag(q-c,q,q,q,q+c)
check('oblique complete eigenframe actions',A*R-R*L)
assert s.factor(R.det())!=0
print('oblique eigenframe determinant:',s.factor(R.det()))
# Test quadratic projectors on a spanning frame, avoiding absolute-value sign assumptions.
K=L-q*I
for name,P,target in [('minus',(K**2-c*K)/(2*c**2),s.diag(1,0,0,0,0)),
                      ('plus',(K**2+c*K)/(2*c**2),s.diag(0,0,0,0,1)),
                      ('convective',I-K**2/c**2,s.diag(0,1,1,1,0))]:
    check(name+' projector in eigenframe',P-target)
check('normal reversal',J(u,H,-n)+A)
