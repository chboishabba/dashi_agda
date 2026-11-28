#!/usr/bin/env python3
"""Exact finite audit; native Agda kernel acceptance is separate."""
from itertools import product, permutations
from collections import Counter
from math import isqrt, gcd

G = tuple(product(range(3), (1, -1)))
I = (0, 1)
R = (1, 1)
S = (0, -1)


def mul(g, h):
    b, a = g
    d, c = h
    return ((b + a*d) % 3, a*c)


def inverse(g):
    b, a = g
    return ((-a*b) % 3, a)


def value(g, x):
    return (g[1]*x + g[0]) % 3


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))


def act_row(k, mat):
    x, y = (0, 1) if k == 41 else (1, k)
    a, b, c, d = mat
    u, v = (a*x+c*y) % 41, (b*x+d*y) % 41
    assert (u, v) != (0, 0)
    return 41 if not u else v*pow(u, -1, 41) % 41


def exponent(base, h):
    t, a = h
    return (36*a*base + 28*t + (21 if a == -1 else 0)) % 42


def run():
    count = Counter()
    def ck(ok, tag):
        assert ok, tag
        count[tag] += 1
    pairs = {(value(g, 0), value(g, 1)): g for g in G}
    ck(len(pairs) == 6 and all(a != b for a,b in pairs), 'nonary')
    def collapse(x,y):
        return None if x == y else pairs[x,y]
    for g,x,y in product(G,range(3),range(3)):
        z = collapse(x,y)
        ck(collapse(value(g,x), value(g,y)) == (None if z is None else mul(g,z)), 'nonary')
    orbit = [41]
    for _ in range(41): orbit.append(act_row(orbit[-1], (4,3,1,4)))
    ck(len(set(orbit)) == 42 and act_row(orbit[-1], (4,3,1,4)) == 41, 'torus')
    labels = {(b,h): exponent(b,h) for b,h in product(range(7),G)}
    ck(set(labels.values()) == set(range(42)), 'torus')
    for (b,h),e in labels.items():
        u = pow(3,e,43)
        er, es = exponent(b,mul(R,h)), exponent(b,mul(S,h))
        ck(pow(3,er,43) == 6*u%43, 'torus')
        ck(pow(3,es,43)*u%43 == 42 and (es+e)%42 == 21, 'torus')
        ck(act_row(orbit[e], (31,17,33,31)) == orbit[er], 'torus')
        ck(act_row(orbit[e], (0,11,10,0)) == orbit[es], 'torus')
        ck(mul(S,mul(R,mul(S,h))) == mul(inverse(R),h), 'torus')
    for g,k,h in product(G,G,G):
        rel = mul(inverse(h),k)
        ck(mul(h,rel) == k, 'diagonal')
        ck(mul(inverse(mul(g,h)),mul(g,k)) == rel, 'diagonal')
    for p in range(2,74):
        if not prime(p): continue
        if p == 2: continue
        n = p-1
        gen = next(a for a in range(2,p) if len({pow(a,k,p) for k in range(n)}) == n)
        units = set(range(1,p))
        ck({pow(gen,k,p) for k in range(n)} == units, 'prime_units')
        ck(all(u != -u%p for u in units), 'prime_units')
        if n%6: continue
        m = n//6
        z = pow(gen,4*m,p)
        a = p-1 if p%4 == 3 else gen
        ck(pow(z,3,p)==1 and z!=1 and pow(a,n//2,p)==p-1, 'prime_s3')
        data = {(j,t,s): (pow(gen,2*j,p) if s==1 else a*pow(pow(gen,2*j,p),-1,p))*pow(z,t,p)%p for j in range(m) for t,s in G}
        ck(set(data.values()) == units and len(data)==n, 'prime_s3')
        for (j,t,s),u in data.items():
            ck(data[j,(t+1)%3,s]==z*u%p, 'prime_s3')
            ck(data[j,(-t)%3,-s]==a*pow(u,-1,p)%p, 'prime_s3')
            ck(len({data[j,*g] for g in G})==6, 'prime_s3')
    for n in range(1,10):
        if n not in (1,2,3,4,5,9): continue
        counts=Counter()
        for w in product(range(3),repeat=n):
            orb={tuple(value(g,x) for x in w) for g in G}
            counts[len(orb)] += 1
            ck(len(orb)==(3 if len(set(w))==1 else 6), 'hyperfabric')
        ck(counts[3]==3 and counts[6]==3**n-3, 'hyperfabric')
        ck(counts[6]//6==(3**(n-1)-1)//2, 'hyperfabric')
    ck(10*3**9+6*9==196884, 'controls')
    ck(3**9-3==19680, 'controls')
    ck(3*(3-1)*3**2==54, 'controls')
    ck(not prime(1+4+4**2) and not prime(1+7+7**2) and not prime(1+9+9**2), 'controls')
    ck(prime(43) and 43 not in (2,3,5,7,11,13,17,19,23,29,31,41,47,59,71), 'controls')
    ck(gcd(6,(19-1)//6)!=1 and gcd(6,(37-1)//6)!=1, 'controls')
    ck(mul(R,S)!=mul(S,R), 'controls')
    print(dict(count), 'total', sum(count.values()), 'PASS')


if __name__ == '__main__':
    run()
