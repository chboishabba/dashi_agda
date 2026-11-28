#!/usr/bin/env python3
"""Exact finite original CMP102 A(c-1)/B(c-2) degree-filter acceptance.

No floating point, no substitute analytic series, no assumed missing
B first-row. The actual original factorials a_i=1/(2i+2)! and
b_i=1/(2i+3)! are used at every real signed input test point.

The script checks the universal proof CONSTRUCTION on finite samples,
including the genuine exceptional c=1 and negative X. Not Agda
kernel, not 4D Yang-Mills.
"""
from fractions import Fraction as Q
from math import factorial

q=Q(1,4)
checks={"A_degree":0,"B_degree":0,"A_mass":0,"B_mass":0,
        "A_shifted":0,"B_shifted":0,"c1_B":0,"G_tail":0}
for c in range(1,65):
    a=[Q(1,factorial(2*i+2)) for i in range(c)]
    b=[Q(1,factorial(2*i+3)) for i in range(c)]
    mass_a=sum(a,Q(0))
    mass_b=sum(b,Q(0))
    assert mass_a <= Q(6,11)
    assert mass_b <= Q(10,57)
    checks["A_mass"]+=1
    checks["B_mass"]+=1
    for x in (Q(-1,4),Q(-1,8),Q(0),Q(1,8),Q(1,4)):
        A=Q(0)
        B=Q(0)
        for i in range(c):
            for j in range(c):
                if i+j>=c-1:
                    assert i+j+1>=c
                    assert abs(x)**(i+j+1)<=q**c
                    A+=a[i]*a[j]*x**(i+j)
                    checks["A_degree"]+=2
                if i+j>=max(c-2,0):
                    assert i+j+2>=c
                    assert abs(x)**(i+j+2)<=q**c
                    B+=b[i]*b[j]*x**(i+j)
                    checks["B_degree"]+=2
        assert abs(x*A)<=q**c*mass_a**2<=q**c
        assert abs(x*x*B)<=q**c*mass_b**2<=q**c
        checks["A_shifted"]+=2
        checks["B_shifted"]+=2
        if c==1:
            assert B==b[0]**2
            assert abs(x*x*B)<=q**c
            checks["c1_B"]+=2
        n=c-1
        G=1-2*sum((a[i]*x**i for i in range(c)),Q(0))
        G-=x*sum((a[i]*x**i for i in range(c)),Q(0))**2
        G+=2*x*sum((b[i]*x**i for i in range(c)),Q(0))
        G+=x*x*sum((b[i]*x**i for i in range(c)),Q(0))**2
        last=2*x*b[n]*x**n
        assert G==-x*A+last+x*x*B
        assert abs(last)<=q**c
        assert abs(G)<=3*q**c
        checks["G_tail"]+=3

print("CMP102 SECTION41 ORIGINAL DEGREE FILTER PASS",
      checks, "TOTAL",sum(checks.values()))
