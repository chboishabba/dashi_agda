#!/usr/bin/env python3
"""Section36 exact original CMP102 three-wing and cross-Clay controls.

All computations use Fraction exact arithmetic. These are finite
negative controls and mathematical regression, NEVER native kernel
verification nor unrestricted Clay-endpoint proof.
"""
from fractions import Fraction as F
from itertools import product
from math import factorial

checks = {"YM_three_wings":0, "YM_missing_B_negative":0,
          "NS_quarter":0, "BSD_floor":0, "PNP_dual_capacity":0}


def conv(xs):
    v = [F(0)] * (2*len(xs)-1)
    for i, a in enumerate(xs):
        for j, b in enumerate(xs):
            v[i+j] += a*b
    return v


for count in range(1, 70):
    a = [F(1, factorial(2*j+2)) for j in range(count)]
    b = [F(1, factorial(2*j+3)) for j in range(count)]
    aa, bb = conv(a), conv(b)
    for X in (F(-1,4), F(-1,8), F(0), F(1,8), F(1,4)):
        A = sum((c*X**j for j,c in enumerate(a)), F(0))
        B = sum((c*X**j for j,c in enumerate(b)), F(0))
        squareA = A*A - sum((aa[j]*X**j for j in range(count-1)), F(0))
        squareB = B*B - sum((bb[j]*X**j for j in range(max(0,count-2))), F(0))
        components = (-X*squareA,
                       2*X*b[-1]*X**(count-1),
                       X*X*squareB)
        G = 1-2*A-X*A*A+2*X*B+X*X*B*B
        assert G == sum(components)
        for term in components:
            assert abs(term) <= F(1,4)**count
            checks["YM_three_wings"] += 1
        assert abs(G) <= 3*F(1,4)**count
        checks["YM_three_wings"] += 1
        assert G != components[0]+components[2]
        checks["YM_missing_B_negative"] += 1

for values in product(range(5), repeat=4):
    E = sum(v*v for v in values)
    D = sum(k*v*v for k,v in zip((1,16,81,256),values))
    Q = sum(k*v*v for k,v in zip((1,2,3,4),values))
    assert Q**4 <= E**3*D
    checks["NS_quarter"] += 1

for a,b in ((F(1,2),F(3,4)),(F(2),F(5)),(F(3,2),F(7,2))):
    h = [F(1)]
    for n in range(42): h.append(a*h[-1]+b**(n+1))
    r = a+b+1
    m = lambda k: F(0) if k==0 else r**k
    for n in range(40):
        assert h[n]*m(n+2)-h[n+1]*m(n+1)>0
        assert a**n*m(2) <= m(n+2)
        checks["BSD_floor"] += 2

for n in range(1,31):
    for C in range(1,9):
        # Actual charged input obligations cannot exceed n*C.
        weights = [min(C, (j%3)+1) for j in range(n)]
        W = sum(weights)
        assert W <= n*C
        # Exact same W may be scheduled in T=n physical slots.
        T=n
        assert W <= T*C
        for B in range(n+1):
            if B*C < W:
                assert B < T
            checks["PNP_dual_capacity"] += 1

print("CLAY36 EXACT REGRESSION PASS",checks,
      "TOTAL",sum(checks.values()))
