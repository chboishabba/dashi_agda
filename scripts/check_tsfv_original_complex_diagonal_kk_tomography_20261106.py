#!/usr/bin/env python3
"""Exact source-selected TSVF finite-diagonal and 5D KK probe controls.

Independent Fraction reference: actual original finite complex source
forward ket (1,1) needs 1/2 normalization; its real diagonal *-algebra
is positive. Full 5D KK bilinear is determined by independent g4,
radius and mixed connection probes. NOT Agda or continuum physics.
"""
from fractions import Fraction as Q
from itertools import product

Z, O, HALF = Q(0), Q(1), Q(1, 2)

def cmul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]

def cadd(a, b):
    return a[0]+b[0], a[1]+b[1]

def cconj(a):
    return a[0], -a[1]

def pair(x, y):
    return cadd(cmul(cconj(x[0]), y[0]), cmul(cconj(x[1]), y[1]))

def diagonal(a, b, x):
    return cmul((a,Z), x[0]), cmul((b,Z), x[1])

def state(a, b):
    psi = ((O,Z),(O,Z))
    assert pair(psi,psi) == (Q(2),Z)
    out = pair(psi,diagonal(a,b,psi))
    assert out == (a+b,Z)
    return HALF*out[0]

def bilinear(g4, A, radius, v, s, w, t):
    return g4(v,w)+radius*(s+A(v))*(t+A(w))

def main():
    values=[Q(-3),Q(-1,2),Z,Q(1,3),O,Q(4)]
    cases=0
    psi=((O,Z),(O,Z))
    for a,b,c,d in product(values,repeat=4):
        assert state(O,O)==O
        assert state(a,b)==HALF*(a+b)
        assert state(a*a,b*b)>=Z
        assert diagonal(O,O,psi)==psi
        assert diagonal(a*c,b*d,psi)==diagonal(a,b,diagonal(c,d,psi))
        x=((a,b),(c,d)); y=((d,a),(b,c))
        assert pair(diagonal(a,b,x),y)==pair(x,diagonal(a,b,y))
        cases+=1
    vectors=[tuple(Q(x) for x in v) for v in product([-1,0,1],repeat=4)]
    g4=lambda v,w:-v[0]*w[0]+sum(v[i]*w[i] for i in range(1,4))
    A=lambda v:Q(2)*v[0]+v[1]-Q(1,3)*v[3]
    B=lambda v:Q(3)*v[0]-v[2]+Q(2,3)*v[3]
    for v,w in product(vectors[::13],repeat=2):
        for radius in [Q(1,2),Q(2),Q(7,3)]:
            assert bilinear(g4,A,radius,v,-A(v),w,-A(w))==g4(v,w)
            assert bilinear(g4,B,radius,v,-B(v),w,-B(w))==g4(v,w)
            assert bilinear(g4,A,radius,v,O-A(v),w,O-A(w))-g4(v,w)==radius
            assert bilinear(g4,A,O,v,Z,w,O)-bilinear(g4,A,O,v,Z,w,Z)==A(v)
            cases+=1
    print(f"PASS {cases} exact Fraction cases: selected TSVF finite complex Hermitian/positive state and KK full probe tomography")
    print("CONTROL ONLY: not original measured four-cone, full complex GNS/OS or Einstein+YM continuum")

if __name__ == "__main__":
    main()
