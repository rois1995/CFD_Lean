"""Independently differentiate the five M1 conservative flux components."""
import sympy as s
rho, E, g, dr, de = s.symbols('rho E g dr de')
m=s.Matrix(s.symbols('mx my mz')); n=s.Matrix(s.symbols('nx ny nz')); dm=s.Matrix(s.symbols('dx dy dz'))
u=m/rho; q=u.dot(n); p=(g-1)*(E-m.dot(m)/(2*rho)); H=(E+p)/rho
vec=lambda first,mid,last:s.Matrix([first,*mid,last])
F=vec(m.dot(n),m*q+p*n,(E+p)*q)
dp=(g-1)*(de-u.dot(dm)+u.dot(u)*dr/2); b=n.dot(dm)-q*dr
action=vec(n.dot(dm),q*dm+u*b+n*dp,q*(de+dp)+H*b)
assert all(s.factor(x)==0 for x in F.jacobian(vec(rho,m,E))*vec(dr,dm,de)-action)
print('All five symbolic directional derivatives match at nonzero density, arbitrary gamma and face vector.')
