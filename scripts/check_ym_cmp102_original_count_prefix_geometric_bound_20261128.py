#!/usr/bin/env python3
"""Original CMP102/CMP109 Bishop SeriesOf COUNT-index exact source check.

SeriesOf(term,count) sums indexes 0..count-1, confirmed against
DASHI/Foundations/BishopFinSumSeriesBridgeExact.agda.
All coefficients use the original (2j+2)! and (2j+3)! sources.
No random/sampled approximation in assertions. No native Agda admission.
"""
from fractions import Fraction as Q
from math import factorial

def conv(a, b):
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]+=x*y
    return out

def add(out, poly, sign=1, shift=0):
    for i,c in enumerate(poly):
        out[i+shift]+=sign*c

def polyG(count):
    a=[Q(1,factorial(2*j+2)) for j in range(count)]
    b=[Q(1,factorial(2*j+3)) for j in range(count)]
    if not count: return [Q(1)]
    g=[Q(0)]*(2*count+1)
    g[0]=1
    add(g,a,-2)
    add(g,conv(a,a),-1,1)
    add(g,b,2,1)
    add(g,conv(b,b),1,2)
    return g

def evaluate(coeff,x):
    return sum((c*x**i for i,c in enumerate(coeff)),Q(0))

def run(max_count=40):
    checked=0
    for count in range(max_count+1):
        g=polyG(count)
        assert all(g[k]==0 for k in range(count))
        checked+=count
        if count:
            assert g[count]==Q(2,factorial(2*count+2))
            checked+=1
        l1=sum(map(abs,g),Q(0))
        # Original nonnegative coefficients at X=1 have these uniform
        # ratio bounds: A<=6/11<3/5, B<=10/57<1/5.
        a=sum((Q(1,factorial(2*j+2)) for j in range(count)),Q(0))
        b=sum((Q(1,factorial(2*j+3)) for j in range(count)),Q(0))
        assert a<=Q(6,11)<Q(3,5)
        assert b<=Q(10,57)<Q(1,5)
        assert l1<=1+2*a+a*a+2*b+b*b<=3
        checked+=3
        for x in (Q(-1,4),Q(-1,8),Q(0),Q(1,8),Q(1,4)):
            assert abs(evaluate(g,x))<=3*Q(1,4)**count
            checked+=1
    print("CMP102 original finite G_COUNT exact PASS",checked,
          "counts 0..",max_count, "bound 3*4^-COUNT")

if __name__=="__main__":
    run()
