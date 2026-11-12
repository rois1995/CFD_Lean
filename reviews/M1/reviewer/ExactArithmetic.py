"""Conservative-state flux checked against the Cartesian Euler flux tensor using exact rationals."""
from fractions import Fraction as F
from itertools import product

def tensor_contraction(rho, u, p, g, s):
    e_density = p / (g - 1) + rho * sum(x*x for x in u) / 2
    # Each column is one Cartesian flux F_j. Length is 2 + spatial dimension.
    columns = [(rho*uj, *(rho*ui*uj + (p if i == j else 0) for i,ui in enumerate(u)),
                (e_density+p)*uj) for j,uj in enumerate(u)]
    return tuple(sum((columns[j][i]*s[j] for j in range(len(s))), F(0))
                 for i in range(len(u)+2))

def conservative_formula(rho,m,energy,g,s):
    p = (g-1)*(energy-sum(x*x for x in m)/(2*rho))
    mass = sum((mi*sj for mi,sj in zip(m,s)),F(0))
    q = mass/rho
    return (mass, *(mi*q+p*sj for mi,sj in zip(m,s)), (energy+p)*q)

def check(rho,u,p,g,s):
    m=tuple(rho*ui for ui in u)
    energy=p/(g-1)+rho*sum(ui*ui for ui in u)/2
    result=conservative_formula(rho,m,energy,g,s)
    assert result == tensor_contraction(rho,u,p,g,s)
    return result

if __name__ == '__main__':
    examples=[(2,(3,),5,2,(4,)), (2,(3,-1),5,F(7,5),(2,3)),
              (2,(3,-1),5,F(7,5),(1,3))]
    for rho,u,p,g,s in examples:
        flux=check(F(rho),tuple(map(F,u)),F(p),F(g),tuple(map(F,s)))
        print('rho',rho,'u',u,'p',p,'gamma',g,'S',s,'flux',tuple(map(str,flux)))
    count=0
    for d in range(4):
        for rho,p,g in product(map(F,[1,2]),map(F,[1,5]),[F(7,5),F(5,3),F(2)]):
            for u in product([F(-1),F(0),F(3,2)],repeat=d):
                for s in product([F(-2),F(0),F(3)],repeat=d):
                    check(rho,u,p,g,s)
                    count+=1
    print('Exact componentwise Cartesian contraction:',count,'cases passed; dimensions 0, 1, 2, 3.')
