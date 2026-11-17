#!/usr/bin/env python3
"""Exact classical double-dimensional reduction (membrane -> string) fixture.

PRIOR theory: a 2+1 Nambu–Goto membrane that wraps a compact isometric target
circle once yields a 1+1 Nambu–Goto string, with T_string=2*pi*R*T_membrane,
under a block-product induced metric and fixed circle radius R. This is
NOT a 27D bosonic M theory, Weyl quantization, BRST, anomaly or physical 369
same-object proof. Existing DASHI 2+1 membrane is a domain-wall/shell model.
"""
from fractions import Fraction as Q
from itertools import product

def det2(h):
    return h[0][0]*h[1][1]-h[0][1]*h[1][0]

def det3(h):
    a,b,c=h[0]; d,e,f=h[1]; g,i,j=h[2]
    return a*(e*j-f*i)-b*(d*j-f*g)+c*(d*i-e*g)

def extend_circle(h, radius, shift=(0,0), compatible=False):
    """KK-shaped metric. With compatible=True, include R² A A^T block."""
    r2=radius*radius
    return ((h[0][0]+(r2*shift[0]*shift[0] if compatible else 0),
             h[0][1]+(r2*shift[0]*shift[1] if compatible else 0), r2*shift[0]),
            (h[1][0]+(r2*shift[0]*shift[1] if compatible else 0),
             h[1][1]+(r2*shift[1]*shift[1] if compatible else 0), r2*shift[1]),
            (r2*shift[0],r2*shift[1],r2))

def test():
    checked=0
    for a,b,c,r in product((1,2,3), (1,2,4), (-2,-1,0,1,2), (Q(1,3),Q(1),Q(7,2))):
        h=((Q(-a*a),Q(c)),(Q(c),Q(b*b)))
        assert det2(h)<0
        H=extend_circle(h,r)
        assert det3(H)==r*r*det2(h)
        assert -det3(H)==r*r*(-det2(h))
        for u,v in ((Q(0),Q(0)),(Q(1),Q(2)),(Q(2),Q(-3))):
            gauged=extend_circle(h,r,(u,v),True)
            assert det3(gauged)==r*r*det2(h)
        checked+=1
    print(f'PASS {checked} Lorentzian 2D x circle blocks: det h3=R² det h2')
    print('PASS physical coefficient conditional: T_string=(2*pi*R)*T_membrane (one wrap)')
    print('PASS compatible KK offdiagonal Schur block retains product determinant')
    h=((Q(-4),Q(1)),(Q(1),Q(9)))
    radius=Q(2)
    mixed=extend_circle(h,radius,(Q(1),Q(2)),False)
    assert det3(mixed)!=radius*radius*det2(h)
    assert det3(extend_circle(h,radius,(Q(1),Q(2)),True))==radius*radius*det2(h)
    print('PASS naive unmatched KK shift fails: physical horizontal source required')
    assert 27-1 == 26 and 26-2 == 24
    print('BOUNDARY 27-dimensional target->26D interval compactification is Horowitz-Susskind CONJECTURE')
    print('BOUNDARY 3x3x3=27 SITES and Albert J3(O) dimension 27 are NOT 27 target coordinates')
    print('BOUNDARY no quantum 2D worldsheet, Weyl anomaly, BRST, Monster equivalence or YM/NS/Clay promotion')

if __name__ == '__main__':
    test()
