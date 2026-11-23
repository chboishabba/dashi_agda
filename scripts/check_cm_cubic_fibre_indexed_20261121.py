#!/usr/bin/env python3
"""Exact cube-fibre/order-3 MulChar regression on F_p, not global Hecke or RH."""
from collections import Counter
from itertools import product

# Cyclotomic integer x=a+b*omega, omega^2=-1-omega.
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def mul(x,y):
    a,b=x;c,d=y
    return (a*c-b*d,a*d+b*c-b*d)
ZERO,ONE,W,W2=(0,0),(1,0),(0,1),(-1,-1)
assert add(add(ONE,W),W2)==ZERO and mul(W,W)==W2 and mul(W,W2)==ONE

def root(p):
    for g in range(2,p):
        if len({pow(g,k,p) for k in range(p-1)})==p-1:return g
    raise AssertionError(p)

def run_prime(p):
    assert p>3 and p%3==1
    g=root(p)
    logs={pow(g,k,p):k for k in range(p-1)}
    assert len(logs)==p-1
    vals=(ONE,W,W2)
    psi=lambda t: ZERO if t==0 else vals[logs[t]%3]
    assert psi(0)==ZERO and psi(1)==ONE and psi(g)!=ONE
    for a,b in product(range(p),repeat=2):
        assert psi(a*b%p)==mul(psi(a),psi(b))
    fibres=Counter(pow(x,3,p) for x in range(p))
    weights={}
    for t in range(p):
        weight=add(add(ONE,psi(t)),mul(psi(t),psi(t)))
        assert weight==(fibres[t],0),(p,t,weight,fibres[t])
        weights[t]=weight
    # Every delta-function gives the source cube-fibre identity.
    for t in range(p):
        assert fibres[t]==weights[t][0]
    # Additional signed test functions f in the original source reindex.
    for offset in range(5):
        def f(t):return (t+offset)**2%17-8
        left=sum(f(pow(x,3,p)) for x in range(p))
        right=sum(weights[t][0]*f(t) for t in range(p))
        assert left==right
    assert [t for t in range(p) if psi(t)==ZERO]==[0]
    return p*p,p

if __name__=='__main__':
    primes=(7,13,19,31,37,43,61,67,73,79)
    results=[run_prime(p) for p in primes]
    assert sum(n for n,p in results)==24538
    assert sum(p for n,p in results)==430
    print('PASS 24538 exact MulChar multiplicativity cases across 10 prime fields')
    print('PASS 430 exact cube-fibre pointwise identities and signed reindex tests')
    print('PASS scalar zero / unity / zeta / zeta-squared remain distinct')
    print('OPEN: global Hecke character, selected CM prime, original IsLift, kernel')
