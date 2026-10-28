#!/usr/bin/env python3
"""Exact straight C3-covariant basing paths inside the shared central cover.

No global wild-satellite fundamental-group identification is assumed or
proved. This pays the basepoint-path geometry for the future pi1 weld.
Existing DASHI C3 centres and the pointed-cover van Kampen consumer are reused.
"""
from fractions import Fraction as F
import json

X0=(F(20),F(20),F(20))
C=tuple(tuple(F(9) if j==i else F(0) for j in range(3)) for i in range(3))
P=tuple(tuple(F(13) if j==i else F(0) for j in range(3)) for i in range(3))
RMIN,RMAX=F(15,4),F(17,4)

def rotate(x):return (x[2],x[0],x[1])
def segment(i,t):return tuple((1-t)*x+t*y for x,y in zip(X0,P[i]))
def d2(x,y):return sum((a-b)**2 for a,b in zip(x,y))

def certify():
    assert rotate(X0)==X0
    assert all(rotate(C[i])==C[(i+1)%3] for i in range(3))
    assert all(rotate(P[i])==P[(i+1)%3] for i in range(3))
    # For any t in [0,1], the distinguished coordinate of gamma_i
    # is 20-7t >=13. This one inequality dominates all cut-ball
    # separation, central-ball, tube and unit satellite envelopes.
    assert F(13)-F(9)==F(4)>RMIN
    assert F(13)>RMAX and F(13)>F(17,2)
    assert RMIN<F(4)<RMAX
    n=0
    for k in range(101):
        t=F(k,100)
        for i in range(3):
            x=segment(i,t)
            assert x[i]==20-7*t>=13
            assert all(d2(x,c)>RMIN**2 for c in C)
            assert rotate(x)==segment((i+1)%3,t)
            assert segment(i,F(0))==X0 and segment(i,F(1))==P[i]
            n+=1
    return {'status':'PASS','basepoint':'(20,20,20)',
            'terminal_points':['13e_0','13e_1','13e_2'],
            'path':'gamma_i(t)=(1-t)(20,20,20)+t(13e_i)',
            'universal_bound':'gamma_i(t)[i]=20-7t >=13 for t in [0,1]',
            'central_clearance':'distance(gamma_i(t),9e_j)>=4>15/4',
            'rotation':'R gamma_i = gamma_(i+1 mod3)',
            'rational_checks':n,
            'source_satellite_pi1_equivalence':False,
            'lean_kernel_checked':False}

if __name__=='__main__':print(json.dumps(certify(),indent=2))
