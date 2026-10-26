#!/usr/bin/env python3
"""Source-backed Monster 2A/2B defect traces and exact conditional 27-braid protocol.

2A/2B: Lin--Shao, Duality Defect of the Monster CFT, arXiv:1911.00042.
27A/27B: ATLAS Monster conjugacy classes, both powering to 3B at order three.
Twisted modular covariance: Carnahan, Generalized Moonshine IV.
A modular label transition does NOT by itself prove trace separation.
"""
from math import gcd

J2 = 196884
T2A = 4372
T2B = 276

def eigenspaces(trace):
    assert (J2 + trace) % 2 == (J2 - trace) % 2 == 0
    return (J2 + trace) // 2, (J2 - trace) // 2

assert eigenspaces(T2A) == (100628, 96256)
assert eigenspaces(T2B) == (98580, 98304)
assert T2A != J2 and T2B != J2 and T2A != T2B
assert sum(eigenspaces(T2A)) == sum(eigenspaces(T2B)) == J2
print("PASS published Monster CFT weight-2 Z2A/Z2B twined trace separation")
print("  2A eigen-sectors:", eigenspaces(T2A))
print("  2B eigen-sectors:", eigenspaces(T2B))

M = ((13,-8),(-8,5))
assert M[0][0]*M[1][1] - M[0][1]*M[1][0] == 1
assert tuple(tuple(x%2 for x in row) for row in M) == ((1,0),(0,1))
N = 27

def transform(pair):
    r,s=pair
    # (g^r,g^s) acts by (g^(a*r+c*s),g^(b*r+d*s)).
    return ((M[0][0]*r+M[1][0]*s)%N,
            (M[0][1]*r+M[1][1]*s)%N)

assert transform((1,0)) == (13,19)
assert transform((0,1)) == (19,5)
assert all(transform((r,s)) != (r,s)
           for r in range(N) for s in range(N)
           if (r,s) != (0,0))

# CONDITIONAL: a primitive Z27 charge k of a Monster order-27
# action gives insertion phase zeta_27^(19*k), distinct from 1.
# Neither its population in a specified twisted module nor the
# q-series distinction for the transformed pair is shown here.
assert all((19*k)%N != 0 for k in range(1,N) if gcd(k,N)==1)
assert all(gcd(19*k,N)==1 for k in range(1,N) if gcd(k,N)==1)

print("PASS Monster 27A/B-compatible pair transform: (g,1) -> (g^13,g^19)")
print("PASS all 728 nontrivial Z27^2 twist pairs move; mod2 modular matrix is identity")
print("PASS conditional primitive Z27 charge gives nontrivial g^19 phase")
print("OPEN specific 27A/27B twisted graded trace, modular multiplier, marked torus experiment")
print("OPEN bulk AdS3 symmetry defect or Wilson-loop dual, not inferred from KK pp-wave")


# Independent integer q-series from source ETA QUOTIENT identities,
# rather than just rechecking copied coefficients:
# P(q)=prod (1+q^n)^(-24)
# T_2B=q^-1 P(q)+24, T_2A=T_2B+4096 q/P(q).
from math import comb
LIMIT=6
def conv(a,b):
    return [sum(a[j]*b[n-j] for j in range(n+1)) for n in range(LIMIT+1)]
P=[1]+[0]*LIMIT
Pinverse=[1]+[0]*LIMIT
for n in range(1,LIMIT+1):
    f=[0]*(LIMIT+1)
    finv=[0]*(LIMIT+1)
    for k in range(LIMIT//n+1):
        f[k*n]=(-1)**k*comb(23+k,k)
        if k<=24:finv[k*n]=comb(24,k)
    P=conv(P,f)
    Pinverse=conv(Pinverse,finv)
assert conv(P,Pinverse)==[1]+[0]*LIMIT
# Series indices i represent powers q^(i-1).
series2B=[P[i]+(24 if i==1 else 0) for i in range(LIMIT+1)]
series2A=[series2B[i]+(4096*Pinverse[i-2] if i>=2 else 0)
          for i in range(LIMIT+1)]
assert series2B[:5]==[1,0,276,-2048,11202]
assert series2A[:5]==[1,0,4372,96256,1240002]
print("PASS independent eta-product derivation of 2A/2B twining q-series")
