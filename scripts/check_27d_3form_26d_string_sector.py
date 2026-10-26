#!/usr/bin/env python3
"""Selected 27D Einstein+4form action term -> 26D string H3 term,
under constant-radius product, flat spectators, one circle polarisation.
Source: conventional -F4^2/(2*4!) and -H3^2/12; not full bosonic M theory.
"""
from fractions import Fraction as Q
from itertools import permutations, product
from math import factorial

def parity(t):
    return -1 if sum(t[i]>t[j] for i in range(len(t)) for j in range(i+1,len(t)))%2 else 1

def contraction(indices, inv, component):
    return sum((Q(parity(order)*component)**2 *
                Q(product_list(inv[k] for k in order))
                for order in permutations(indices)), Q(0))

def product_list(xs):
    v=Q(1)
    for x in xs: v*=x
    return v

def test():
    count=0
    for a,b,c,r,h in product((1,2,3),(1,2,4),(1,2),(Q(1,3),Q(1),Q(7,2)),(1,2,3)):
        inv=[Q(-1,a*a),Q(1,b*b),Q(1,c*c)] + [Q(1)]*23 + [Q(1,r*r)]
        assert len(inv)==27
        h3=contraction((0,1,2),inv,Q(h))
        # Chosen circle component of the 27D 3-form potential C_{mu nu y}=r*B_{mu nu}.
        # For constant r, the 4-form field strength satisfies F_{mu nu rho y}=r*H_{mu nu rho}.
        f4=contraction((0,1,2,26),inv,Q(r*h))
        assert f4 == 4*h3
        assert -f4/Q(2*factorial(4)) == -h3/Q(12)
        area26=Q(a*b*c)
        area27=area26*r
        assert area27*(-f4/Q(48)) == r*area26*(-h3/Q(12))
        count+=1
    assert count==3*3*2*3*3
    print('PASS',count,'exact diagonal 27D Lorentzian backgrounds: F4^2=4 H3^2 after C_y=r B')
    print('PASS integrated 27D electric 4-form action equals 2pi*r times 26D -H3²/12 coefficient')
    # WARNING: if r depends on time and B_12 is constant, d(R B)=dR^B != R dB.
    drdt=Q(1); B12=Q(2); H012=Q(0)
    assert drdt*B12 + Q(3)*H012 == 2
    assert Q(3)*H012 == 0
    print('NO-GO varying radion: F012y=2 from dr wedge B but r*H012=0; constant-r rescaling fails')
    print('BOUNDARY exact selected constant-r electric truncation; R27 Ricci and dynamical phi/H coset NOT paid')
    print('BOUNDARY full action 27D gravity+3form -> 26D beta functions, 125/121, K27 and critical string NOT paid')

if __name__=='__main__':
    test()
