"""Exact R236 geometry consumer: shell counts and input-mass moments.
Source: physicalOutputFiber, literal ceil-log shells, strict Round25/63
Bony classifier and R236 criticalRegionTag. No analytic or kernel claim.
"""
from itertools import product
from random import Random
from math import prod
import sympy as s


def shell(m):
    return (max(1, m)-1).bit_length()


def region(jp, jq, jk):
    if jp+3 < jq:
        return 0 if 3*jp <= 2*jq else 2
    if jq+3 < jp:
        return 0 if 3*jq <= 2*jp else 2
    if jk+3 < jp and jk+3 < jq:
        return 1 if 5*jk <= 4*max(jp,jq) else 2
    return 2


def f1(x):
    return x*(x+1)//2


def f2(x):
    return x*(x+1)*(2*x+1)//6


def cumulative(k, a, b):
    if min(a,b)<0:
        return 0,0
    axes=[]
    for h in k:
        lo,hi=max(-a,h-b),min(a,h+b)
        if lo>hi:
            return 0,0
        n=hi-lo+1
        t=f1(hi)-f1(lo-1); u=f2(hi)-f2(lo-1)
        axes.append((n,2*u-2*h*t+h*h*n))
    return prod(n for n,j in axes),sum(j*prod(axes[v][0] for v in range(3) if v!=i) for i,(n,j) in enumerate(axes))


def compressed(N,k):
    out=[[0,0] for _ in range(3)]
    if max(map(abs,k))>N:
        return out
    radii=[-1]+[min(N,2**j) for j in range(shell(N)+1)]
    jk=shell(max(map(abs,k)))
    for i,(a,A) in enumerate(zip(radii,radii[1:])):
        for j,(b,B) in enumerate(zip(radii,radii[1:])):
            uv=cumulative(k,A,B); lv=cumulative(k,a,B)
            ul=cumulative(k,A,b); ll=cumulative(k,a,b)
            n,m=(x-y-z+t for x,y,z,t in zip(uv,lv,ul,ll))
            assert n>=0 and m>=0
            dest=out[region(i,j,jk)]
            dest[0]+=n; dest[1]+=m
    return out


def literal(N,k):
    out=[[0,0] for _ in range(3)]
    if max(map(abs,k))>N:
        return out
    jk=shell(max(map(abs,k)))
    for p in product(range(-N,N+1),repeat=3):
        q=tuple(h-x for h,x in zip(k,p))
        if max(map(abs,q))>N:
            continue
        r=region(shell(max(map(abs,p))),shell(max(map(abs,q))),jk)
        out[r][0]+=1
        out[r][1]+=sum(x*x+y*y for x,y in zip(p,q))
    return out


if __name__=='__main__':
    x,h=s.symbols('x h',integer=True)
    F1=x*(x+1)/2; F2=x*(x+1)*(2*x+1)/6
    assert s.expand(F1-F1.subs(x,x-1)-x)==0
    assert s.expand(F2-F2.subs(x,x-1)-x*x)==0
    F=2*F2-2*h*F1+h*h*x
    assert s.expand(F-F.subs(x,x-1)-(x*x+(h-x)**2))==0
    assert region(0,3,3)==2 and region(0,4,4)==0
    assert shell(0)==shell(1)==0 and shell(8)==3 and shell(9)==4
    cases=[(N,k) for N in range(5) for k in product(range(-N-1,N+2),repeat=3)]
    rng=Random(236)
    for N in (8,9,16,17,32):
        cases.extend((N,k) for k in [(0,0,0),(N,0,0),(N,N,N),(-N,1,0),(1,0,0)]+[tuple(rng.randint(-N,N) for _ in range(3)) for i in range(4)])
    seen=set()
    for N,k in cases:
        got=compressed(N,k)
        assert got==literal(N,k),(N,k,got,literal(N,k))
        if max(map(abs,k))<=N:
            assert tuple(map(sum,zip(*got)))==cumulative(k,N,N)
            assert got==compressed(N,tuple(-x for x in k))
        seen.update(i for i,(n,m) in enumerate(got) if n)
    assert seen=={0,1,2}
    assert compressed(5,(5,0,0))==[[0,0],[0,0],[726,42350]]
    big=compressed(2**20,(5,0,0))
    assert tuple(map(sum,zip(*big)))==cumulative((5,0,0),2**20,2**20)
    print('PASS:',len(cases),'literal fibre comparisons; all regions; signed reflection; strict collar; symbolic antiderivatives')
    print('N=5,k=(5,0,0):',compressed(5,(5,0,0)))
    print('N=2^20,k=(5,0,0):',big,'total:',tuple(map(sum,zip(*big))))
