"""Finite exact regression for signed cocycle algebra only.
This does not compute an elliptic curve H1, Sha, or analytic rank.
"""
from itertools import product
checks = 0
def ck(x):
    global checks
    if not x: raise AssertionError('Kummer representative identity failed')
    checks += 1

# The nontrivial involution tests the actual coboundary sign.
# A finite cyclic module is not divisible: restrict to double targets.
for N in (4,8,16,32):
    for sign in (-1,1):
        delta=lambda q,g: ((sign**g-1)*q)%N
        action=lambda g,x: (sign**g*x)%N
        for q in range(N):
            for g,h in product(range(2),repeat=2):
                ck(delta(q,(g+h)%2)==(delta(q,g)+action(g,delta(q,h)))%N)
            for g in range(2): ck(2*delta(q,g)%N==delta(2*q,g))
            for t in (0,N//2):
                for g in range(2): ck((delta(q+t,g)-delta(q,g))%N==delta(t,g))
        for a in range(N):
            c=[0,a]
            if (a+action(1,a))%N:continue
            for q in range(N):
                p=2*q%N
                if 2*a%N!=delta(p,1):continue
                d=[(c[g]-delta(q,g))%N for g in range(2)]
                ck(all(2*v%N==0 for v in d))
                ck(all(c[g]==(d[g]+delta(q,g))%N for g in range(2)))
                for g,h in product(range(2),repeat=2):
                    ck(d[(g+h)%2]==(d[g]+action(g,d[h]))%N)
            for q in range(N):
                if all(c[g]==delta(q,g) for g in range(2)) and 2*a%N==0:
                    ck(action(1,2*q)==2*q%N)
print(f'{checks}/{checks} signed representative controls PASS')
