#!/usr/bin/env python3
"""Exact F8 mode C3/S3 Reynolds donor audit.

Reuses the original DASHI six-permutation finite carrier and the
signed-permutation Reynolds technique, NOT the YM SU(2) physical S^3
measure. F8 d=3,7,11 radial shells explicitly break mode rotations.
"""
from fractions import Fraction as F
from itertools import permutations
import random

rng=random.Random(66840)
checks=0
rotate=lambda x:(x[1],x[2],x[0])
mean=lambda x:sum(x,F(0))/3
S3=tuple(permutations(range(3)))
C3=((0,1,2),(1,2,0),(2,0,1))
def apply(p,x):return tuple(x[p[i]] for i in range(3))
def reynolds(x,G):return tuple(sum((apply(p,x)[i] for p in G),F(0))/len(G) for i in range(3))

for _ in range(300):
    x=tuple(F(rng.randrange(-15,16),rng.randrange(1,11)) for i in range(3))
    assert reynolds(x,C3)==reynolds(x,S3)==(mean(x),)*3;checks+=1
    assert reynolds(reynolds(x,C3),C3)==reynolds(x,C3);checks+=1
    v=-F(rng.randrange(1,10),10)
    invz=F(rng.randrange(1,11),rng.randrange(1,10))
    invdy=F(rng.randrange(1,10),rng.randrange(1,9))
    def normal(state):
        p,m,dp,dm,src=state
        target=((1+v)*p-2*src)/(1-v)
        force=-F(3,2)*invz*(p-m)
        return ((1+v)*dp+force,(v-1)*dm+force+2*(1-v)*invdy*(target-m))
    states=[tuple(F(rng.randrange(-8,9),rng.randrange(1,9)) for _ in range(5)) for i in range(3)]
    for g in S3:
        assert [normal(states[g[i]]) for i in range(3)]==[normal(states[i]) for i in g]
        checks+=1
    a=F(rng.randrange(-9,10),rng.randrange(1,9))
    source=F(rng.randrange(-9,10),rng.randrange(1,9))
    assert reynolds(tuple(a*z+source for z in x),C3)==tuple(a*z+source for z in reynolds(x,C3));checks+=1
    coeff=(F(6),F(14),F(22))
    L=lambda y:tuple(coeff[i]*y[i] for i in range(3))
    comm=tuple(L(rotate(x))[i]-rotate(L(x))[i] for i in range(3))
    assert comm==(-8*x[1],-8*x[2],16*x[0]);checks+=1
    assert mean(L(x))-14*mean(x)==F(8,3)*(x[2]-x[0]);checks+=1
    assert tuple(L(x)[i]-14*x[i] for i in range(3))==(-8*x[0],F(0),8*x[2]);checks+=1

def W(d,j):
    lo=F(max(0,2*j-1),2);hi=F(2*j+1,2)
    return (hi**d-lo**d)/d
def cp(d,j):return F(2*j+1,2)**(d-1)/W(d,j)
def cm(d,j):return F(2*j-1,2)**(d-1)/W(d,j)
for d in (3,7,11):
    assert 2*d=={3:6,7:14,11:22}[d];checks+=1
    assert cp(d,1)=={3:F(27,13),7:F(5103,1093),11:F(649539,88573)}[d];checks+=1
    assert cm(d,1)=={3:F(3,13),7:F(7,1093),11:F(11,88573)}[d];checks+=1

mass=(W(3,0),W(7,0),W(11,0))
assert mass[0]!=mass[1]!=mass[2];checks+=1
x=(F(1),F(0),F(0))
assert sum((mass[i]*x[i]**2 for i in range(3)),F(0))!=sum((mass[i]*rotate(x)[i]**2 for i in range(3)),F(0));checks+=1

# Original full three-channel normal/warp energy, each mode weighted
# with its ACTUAL effective-dimension radial shell volume.
for n in (2,3,5):
    for _ in range(45):
        b=F(rng.randrange(4,15),rng.randrange(11,21))
        h=b*F(rng.randrange(1,10),rng.randrange(10,18))
        v=-F(rng.randrange(1,10),10)
        z=[b+i*h for i in range(n)]
        w=[s**(-3) for s in z]
        nu=[F(1,2) if i in (0,n-1) else F(1) for i in range(n)]
        Eall=F(0);Rall=F(0)
        for ell,d in ((0,3),(2,7),(4,11)):
            j=rng.choice((0,1,2,3));mj=W(d,j)
            p=[F(rng.randrange(-10,11),rng.randrange(1,10)) for i in range(n)]
            m=[F(rng.randrange(-10,11),rng.randrange(1,10)) for i in range(n)]
            def E(x):return h*sum((nu[i]*w[i]*x[i]**2 for i in range(n)),F(0))/2
            def C(x):return sum(((w[i]-w[i+1])*x[i]*x[i+1]/2 for i in range(n-1)),F(0))
            def J(x):return h*sum((nu[i]*w[i]/z[i]*x[i]**2 for i in range(n)),F(0))
            Ep,Em=E(p),E(m);Cp,Cm=C(p),C(m);Jp,Jm=J(p),J(m)
            assert abs(Cp)<=3*Ep/b and abs(Cm)<=3*Em/b;checks+=1
            R=(1+v)*(Cp-F(3,2)*Jp)-(1-v)*(Cm-F(3,2)*Jm)
            assert abs(R)<=12*(Ep+Em)/b;checks+=1
            Eall+=mj*(Ep+Em);Rall+=mj*R
        assert abs(Rall)<=12*Eall/b;checks+=1

print(f"PASS {checks}/{checks} exact C3/S3 Reynolds, radial symmetry breaking and full three-mode weighted normal controls")
print("Native radial origin commutator: (-8*y,-8*z,16*x).")
print("Reynolds common origin operator 14; deviations (-8,0,8).")
