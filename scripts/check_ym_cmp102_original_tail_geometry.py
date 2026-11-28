#!/usr/bin/env python3
"""Original CMP102 G_COUNT exact signed Cauchy tail source certificate.

Runs the original rational CMP109 coefficients at every count, including
zero-prefix, endpoint omissions, and both signed quarter-disk endpoints.
The all-degree cancellation is inherited from the finite binomial-parity
identity at every even degree: sum((-1)^k*binomial(2n+2,k))=0.
No Agda/Lean compilation and no universal YM theorem is claimed.
"""
from fractions import Fraction as F
from math import factorial

A_BOUND = F(6, 11)
B_BOUND = F(10, 57)
UNIVERSAL_WING = A_BOUND*A_BOUND + 2*B_BOUND + B_BOUND*B_BOUND
assert UNIVERSAL_WING == F(267004, 393129) < F(3, 4)


def convolution(a, b):
    out = [F(0)] * (len(a) + len(b) - 1) if a and b else []
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i+j] += ai * bj
    return out


def polynomial(count):
    a = [F(1, factorial(2*j+2)) for j in range(count)]
    b = [F(1, factorial(2*j+3)) for j in range(count)]
    aa, bb = convolution(a,a), convolution(b,b)
    G = [F(0)] * (2*count+1)
    G[0] = 1
    for j, v in enumerate(a): G[j] -= 2*v
    for j, v in enumerate(aa): G[j+1] -= v
    for j, v in enumerate(b): G[j+1] += 2*v
    for j, v in enumerate(bb): G[j+2] += v
    triangle = [F(0)] * len(G)
    for j in range(count):
        even = 2*a[j] + (aa[j-1] if j else 0)
        odd = 1 if j==0 else 2*b[j-1] + (bb[j-2] if j>=2 else 0)
        triangle[j] = odd-even
    tailA = [F(0)] * len(G)
    tailB = [F(0)] * len(G)
    tailLinearB = [F(0)] * len(G)
    if count:
        for j,v in enumerate(aa):
            if j>=count-1: tailA[j+1] -= v
        for j,v in enumerate(bb):
            if j>=count-2: tailB[j+2] += v
        tailLinearB[count] = 2*b[count-1]
    tail = [sum(parts) for parts in zip(tailA, tailLinearB, tailB)]
    return a, b, G, triangle, tail, tailA, tailLinearB, tailB


def evaluate(p,x):
    return sum((v*x**j for j,v in enumerate(p)), F(0))


def main():
    counts = {'count_zero':0, 'source_decomposition':0,
              'vanishing_coefficients':0, 'wing_envelope':0,
              'signed_disk':0, 'omitted_endpoint_negative':0}
    assert polynomial(0)[2]==[F(1)]
    counts['count_zero']+=1
    for c in range(1,65):
        a,b,G,T,W,WA,WL,WB = polynomial(c)
        assert G == [t+w for t,w in zip(T,W)]
        assert all(t==0 for t in T)
        assert G==W
        counts['source_decomposition']+=3
        assert all(v==0 for v in G[:c])
        assert G[c] == F(2,factorial(2*c+2))
        counts['vanishing_coefficients']+=c+1
        asum,bsum = sum(a,F(0)), sum(b,F(0))
        assert asum<=A_BOUND and bsum<=B_BOUND
        assert sum(map(abs,WA),F(0)) <= asum*asum
        assert sum(map(abs,WL),F(0)) <= 2*bsum
        assert sum(map(abs,WB),F(0)) <= bsum*bsum
        assert sum(map(abs,W),F(0)) <= UNIVERSAL_WING
        counts['wing_envelope']+=6
        for x in (F(-1,4),F(-1,6),F(-1,8),F(0),
                  F(1,8),F(1,6),F(1,4)):
            assert abs(evaluate(G,x)) <= UNIVERSAL_WING*abs(x)**c
            assert abs(evaluate(G,x)) <= F(3,4)**(c+1)
            counts['signed_disk']+=2
        if c in (1,2,3,4,5,8,13):
            assert [a+b for a,b in zip(T,[v+w for v,w in zip(WA,WB)])] != G
            counts['omitted_endpoint_negative']+=1
    total=sum(counts.values())
    print('YM CMP102 ORIGINAL SIGNED TAIL PASS',counts,'TOTAL',total)
    print('UNIFORM_WING_EXACT',UNIVERSAL_WING,'LESS_THAN_3/4',UNIVERSAL_WING<F(3,4))


if __name__ == '__main__': main()
