#!/usr/bin/env python3
"""P0 same-curve finite evidence. No K1-K5 or native Agda proof claim.

Original E:y^2=x^3-x, conductor 32, f32=eta(4z)^2 eta(8z)^2.
Negative control: distinct j=0 E:y^2=x^3+1, conductor 36.
"""
from sympy import primerange

def ap(p, b):
    character_sum = 0
    for x in range(p):
        z = (x*x*x-x if b == -1 else x*x*x+1) % p
        if z:
            character_sum += 1 if pow(z, (p-1)//2, p) == 1 else -1
    return -character_sum

cap=512
eta=[0] * (cap + 1)
eta[1]=1
for step in (4,8):
    for n in range(step,cap+1,step):
        next_eta=eta[:]
        for i, coefficient in enumerate(eta):
            if i+n <= cap:
                next_eta[i+n] -= 2*coefficient
            if i+2*n <= cap:
                next_eta[i+2*n] += coefficient
        eta=next_eta

primes=list(primerange(5,400))
assert eta[1] == 1
assert eta[2] == eta[3] == 0
assert all(eta[p] == ap(p,-1) for p in primes)
assert ap(5,-1) == -2 and ap(5,1) == 0
print(f"PASS original level32 eta/Frobenius: {len(primes)} good prime rows")
print("PASS source nonidentification a5(E32)=-2 != a5(j0 E36)=0")
print("NOTE: numerical/finite identity only; analytic L, Agda kernel OPEN")
