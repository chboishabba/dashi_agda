#!/usr/bin/env python3
"""Exact source-selected 27D EH + 4-form -> 26D bosonic string obstruction.
Metric: ds_(d+1)^2 = exp(2a*s)g_d + exp(2b*s)dy^2.
One y index of F4 produces H3; circle fields independent of y; no KK vector.
Integrated by parts; classical two-derivative action (ignores boundary/source).
Prior art: Horowitz-Susskind (2000), Lambert-West (2001), Glennon (2025).
"""
from fractions import Fraction as Q

def reduction(d, a, b):
    a,b = Q(a), Q(b)
    # Curvature prefactor and 4form-with-one-y prefactor in base metric g_d.
    pR = (d-2)*a+b
    pH = (d-6)*a-b
    # Scalar curvature BEFORE integration by parts:
    # R_(d+1) = exp(-2a*s) ( R_d - 2[b+(d-1)a] Box s
    #                         - [2b^2+2(d-2)ab+(d-1)(d-2)a^2] |ds|^2 )
    coeff_box = -2*(b+(d-1)*a)
    coeff_grad = -2*b*b-2*(d-2)*a*b-(d-1)*(d-2)*a*a
    # After IBP ∫ exp(pR*s) coeff_box * Box(s) yields
    # -coeff_box*pR * |ds|².
    kinetic = coeff_grad-coeff_box*pR
    predicted = (d-1)*a*((d-2)*a+2*b)
    assert kinetic == predicted
    return pR,pH,kinetic

def test():
    checks=0
    for d in range(7,41):
        if d==4: continue
        for a in (Q(1),Q(2,3),Q(-7,5)):
            # Requirement of ONE common string-frame dilaton coupling of R and H:
            # pR=pH => (d-2)a+b=(d-6)a-b => b=-2a.
            b=-2*a
            pR,pH,actual = reduction(d,a,b)
            assert pR == pH == (d-4)*a
            # e^(pR*s)=e^(-2Phi) defines Phi=-(d-4)a*s/2.
            # Desired standard string-frame kinetic term 4|dPhi|².
            expected=(d-4)**2*a*a
            assert actual==(d-1)*(d-6)*a*a
            assert actual-expected == (d-10)*a*a
            checks+=1
    print('PASS',checks,'exact common g/B string-frame exponent reductions')
    assert reduction(26,Q(1),Q(-2)) == (Q(22),Q(22),Q(500))
    d=26; a=Q(1)
    actual=Q(500); expected=Q(484)
    assert actual/expected == Q(125,121)
    assert actual-expected == 16
    print('PASS 27D ->26D EH+4form: dilaton kinetic ratio',actual/expected,
          'exact Lambert-West obstruction')
    assert reduction(10,Q(1),Q(-2))==(Q(6),Q(6),Q(36))
    assert Q(36)/Q(36)==1
    print('PASS 11D ->10D version ratio 1 in this gravitational/3form ansatz')
    for b in (Q(-5),Q(0),Q(3,4)):
        pR,pH,_=reduction(26,Q(1),b)
        assert pR!=pH
    print('PASS no alternative b with common metric and 4form coupling except b=-2a')
    print('NO-GO within selected EH+4form ansatz: 26D tree-level R,H,phi couplings cannot ALL match')
    print('BOUNDARY no universal 27D impossibility; added scalar/higher derivative/other K27 action not tested')

if __name__ == '__main__': test()
