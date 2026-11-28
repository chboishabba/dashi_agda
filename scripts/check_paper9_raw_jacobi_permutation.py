#!/usr/bin/env python3
"""Independent exact reference for the raw signed shell permutation.
Not an execution of the Agda proof bodies or a universal proof.
"""
from itertools import product
from collections import defaultdict
from math import isqrt

limit = 64
norm = lambda x: sum(v*v for v in x)

def chart(x):
    a,b,c,d=x
    assert sum(x)%2==1
    return (sum(x)-1)//2,b,c,d
def enc(x):
    k,b,c,d=x
    return 2*k+1-b-c-d,k,k-c-d,k-b-d
def dec(x):
    j,u,v,w=x
    return u,u+v+1-j,u+w+1-j,j-v-w-1
def integer(x):
    k,b,c,d=x
    return 2*k+1-b-c-d,b,c,d
def half(x,p=0):
    j,u,v,w=x
    a,b,c=2*u+1,2*v+1,2*w+1
    return a,b,c,4*j+p-a-b-c
def flip(x):
    j,u,v,w=x
    return j-u-1,-u-1,v,w
def unflip(x):
    j,u,v,w=x
    return j-u,-u-1,v,w
def raw(q):
    return tuple((y-1)//2 for y in q)
def forward(e,x):
    q=enc(chart(x))
    return raw(half(flip(q),2) if e else half(q))
def preimage(y):
    q=tuple(2*u+1 for u in y)
    j,p=divmod(sum(q),4)
    assert p in (0,2)
    x=(j,*y[:3])
    return bool(p),integer(dec(unflip(x) if p else x))
def tri(u):
    m=u if u>=0 else -u-1
    return m*(m+1)

ints=defaultdict(set)
odds=defaultdict(set)
for x in product(range(-isqrt(limit),isqrt(limit)+1),repeat=4):
    n=norm(x)
    if n<=limit:
        ints[n].add(x)
for y in product(range(-isqrt(limit)-1,isqrt(limit)+1),repeat=4):
    n=1+sum(map(tri,y))
    if n<=limit:
        odds[n].add(y)

# Independently compute the original literal integer Cauchy histories.
def row(f,g):
    return [sum(f[i]*g[n-i] for i in range(n+1)) for n in range(limit+1)]
def fourth(f):
    q=row(f,f)
    return row(q,q)
f=[1]+[2*sum(j*j==n for j in range(n+1)) for n in range(1,limit+1)]
g=[sum(j*(j+1)==n for j in range(n+1)) for n in range(limit+1)]
B=fourth(f)
C=fourth([(-1)**n*f[n] for n in range(limit+1)])
A=[0]+[16*k for k in fourth(g)[:-1]]
forward_count=reverse_count=0
for n in range(limit+1):
    assert B[n]==len(ints[n])
    assert A[n]==len(odds[n])
    assert B[n]==A[n]+C[n]
    if n%2:
        im=set()
        for x in ints[n]:
            for e in [False,True]:
                y=forward(e,x)
                assert y in odds[n] and y not in im
                im.add(y)
                assert preimage(y)==(e,x)
                forward_count+=1
        assert im==odds[n]
    else:
        assert not odds[n]
    for y in odds[n]:
        e,x=preimage(y)
        assert x in ints[n] and forward(e,x)==y
        reverse_count+=1
print('PASS raw forward/reverse',forward_count,reverse_count,
      '65 shell permutations and 195 coefficient checks; points',
      sum(map(len,ints.values())),sum(map(len,odds.values())))
