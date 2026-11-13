import sympy as s
x=s.symbols('x0:12')
p=[s.Matrix(x[a:a+3]) for a in range(0,12,3)]
a,b,c,d=p
m=(a+b)/2
f=(a+b+c)/3
t=(a+b+c+d)/4
D=s.det(s.Matrix.hstack(b-a,c-a,d-a))
assert s.expand(s.det(s.Matrix.hstack(m-a,f-a,t-a))-D/24)==0
assert s.expand(((f-m).cross(t-m)/2).dot(b-a)-D/24)==0
print('General flag determinant ratio 1/24 and signed interface dot product det(T)/24 verified.')
