#!/usr/bin/env python3
"""Section44 exact finite source controls; not native/Clay theorem receipts.
YM Bishop 0<=u<=1 all-exponent antitone; NS original R^-2
bound with sqrt radius vs oversized linear schedule; BSD source crossing
symmetry; Hodge all-even-six signed action; PNP adaptive read support.
"""
from fractions import Fraction as Q
from itertools import product
from math import isqrt

C = dict(YM_power=0, NS_sqrt=0, NS_negative=0, BSD_swap=0,
         Hodge_action=0, Hodge_odd=0, PNP_adaptive=0)
for u in (Q(0),Q(1,16),Q(1,4),Q(1,2),Q(1)):
    for n in range(65):
        assert u**(n+1)<=u**n
        C['YM_power']+=1
        for m in range(n,65):
            assert u**m<=u**n
            C['YM_power']+=1

# Exact sqrt: Emax/(2nu eps)=k². Each tuple is an honest special
# case of the universal threshold with rational sqrt, no floats.
for nu in (Q(1,3),Q(1),Q(5,2)):
    for j in range(1,31):
        eps=Q(1,j)
        for k in range(0,21):
            emax=2*nu*eps*k*k
            radius=1+k
            assert radius>0
            assert emax<2*nu*radius*radius*eps
            assert emax/(2*nu*radius*radius)<eps
            assert radius<=1+k*k
            C['NS_sqrt']+=4
            if k>=2:
                assert radius<1+k*k
                C['NS_negative']+=1

def h(a,b,n):
    t=Q(1)
    for k in range(1,n+1):t=a*t+b**k
    return t
for a,b in ((Q(1,2),Q(3,4)),(Q(2),Q(5)),(Q(5),Q(2)),(Q(1,1),Q(7,3))):
    for n in range(1,36):
        m=lambda z:Q(0) if z==0 else (a+b+1)**z
        d1=h(a,b,n)*m(n+2)-h(a,b,n+1)*m(n+1)+(a*b)**(n+1)*m(0)
        d2=h(b,a,n)*m(n+2)-h(b,a,n+1)*m(n+1)+(b*a)**(n+1)*m(0)
        assert d1==d2 and d1>0
        C['BSD_swap']+=2

even=[x for x in product((0,1),repeat=6) if sum(x)%2==0]
assert len(even)==32
zero=(0,)*6
for e in even:
    assert tuple(e[i]^e[i] for i in range(6))==zero
    for f in even:
        ef=tuple(e[i]^f[i] for i in range(6))
        assert ef in even
        for s in even:
            lhs=tuple(ef[i]^s[i] for i in range(6))
            rhs=tuple(e[i]^(f[i]^s[i]) for i in range(6))
            assert lhs==rhs
            C['Hodge_action']+=1
for e in product((0,1),repeat=6):
    if sum(e)%2:
        assert e not in even
        C['Hodge_odd']+=1

# Adaptive two-state machine: the current state chooses physical
# addresses at each step. A terminal split entails some different
# bit read on the first x execution before separation.
for n in range(1,4):
    inputs=list(product((0,1),repeat=n))
    for x,y in product(inputs,repeat=2):
        for b in range(n+1):
            for transition in product((0,1),repeat=4):
                sx=sy=0
                saw_x_different=False
                for j in range(3):
                    ix=tuple((j+sx+i)%n for i in range(b))
                    iy=tuple((j+sy+i)%n for i in range(b))
                    saw_x_different |= any(x[k]!=y[k] for k in ix)
                    ox=sum(x[k] for k in ix)%2
                    oy=sum(y[k] for k in iy)%2
                    sx=transition[2*sx+ox]
                    sy=transition[2*sy+oy]
                    if sx!=sy:
                        assert saw_x_different and b>0
                        C['PNP_adaptive']+=1
print('SECTION44 EXACT FINITE PASS',C,'TOTAL',sum(C.values()))
