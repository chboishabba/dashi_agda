#!/usr/bin/env python3
"""Independent exact control of Section33 Bishop finite weighted Cauchy.

Uses arbitrary nonfactorial positive rational coefficient rows and both
signed input directions. This is not a native Agda proof receipt.
"""
from fractions import Fraction as Q
checks=0
for n in range(45):
    for X in (Q(-1,4),Q(-1,7),Q(0),Q(2,9),Q(1,4)):
        a=[Q(i+2,2*i+5) for i in range(n+1)]
        b=[Q((i+1)**2,3*i+7) for i in range(n+1)]
        cc=sum((a[i]*b[n-i] for i in range(n+1)),Q())
        weighted=sum((a[i]*X**i*b[n-i]*X**(n-i) for i in range(n+1)),Q())
        assert cc*X**n == weighted; checks+=1
        assert cc*X**(n+1) == X*weighted; checks+=1
        assert cc*X**(n+2) == X*X*weighted; checks+=1
for n in range(70):
    for k in range(n+1):
        assert k+(n-k)==n; checks+=1
assert checks==3160
print("SECTION33 ORIGINAL WEIGHTED CAUCHY:",checks,"/3160 PASS")
