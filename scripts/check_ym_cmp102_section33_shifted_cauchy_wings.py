#!/usr/bin/env python3
"""Exact original Bishop-style shifted Cauchy wing tests (not Agda CI).

Cauchy rectangle-minus-triangle at c, c-1 and c-2, preserving
signed inputs, arbitrary rational coefficients and original endpoints.
"""
from fractions import Fraction as Q

def row(a,b,k):
    return sum((a[i]*b[k-i] for i in range(len(a))
                if 0<=k-i<len(b)),Q())

def triangle(a,b,n):
    return sum((row(a,b,k) for k in range(n)),Q())

checks=0
for c in range(1,65):
    for x in (Q(-1,4),Q(-1,7),Q(0),Q(1,9),Q(1,4)):
        a=[Q(i+2,3*i+7)*x**i for i in range(c)]
        b=[Q((i+1)**2,5*i+11)*x**i for i in range(c)]
        for v in (a,b):
            rect=sum(v,Q())**2
            full=rect-triangle(v,v,c)
            positive=[abs(t) for t in v]
            bound=triangle(positive,positive,2*c)-triangle(positive,positive,c)
            assert abs(full)<=bound;checks+=1
            one=rect-triangle(v,v,c-1)
            assert one==full+row(v,v,c-1);checks+=1
            assert abs(one)<=bound+abs(row(v,v,c-1));checks+=1
            if c>=2:
                two=rect-triangle(v,v,c-2)
                assert two==full+row(v,v,c-1)+row(v,v,c-2);checks+=1
                assert abs(two)<=bound+abs(row(v,v,c-1))+abs(row(v,v,c-2));checks+=1
assert checks==3180
print('CMP102 SHIFTED WING EXACT',checks,'/3180 PASS')
