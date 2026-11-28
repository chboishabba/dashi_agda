#!/usr/bin/env python3
"""Independent exact regression, not native Agda or Lean verification."""
from fractions import Fraction as Q
from random import Random

def add(a,b):
    return a[0]+b[0],a[1]+b[1]

def mul(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]

def powc(a,n):
    r=(Q(1),Q(0))
    for _ in range(n):
        r=mul(r,a)
    return r

def c(x):
    return Q(x),Q(0)

def polynomial(j,cs):
    a=c(0)
    for x in cs:
        a=add(mul(a,j),c(x))
    return a

def homogeneous(q,v,cs):
    if not cs:
        return c(0)
    return add(mul(c(cs[0]),powc(v,len(cs)-1)),mul(q,homogeneous(q,v,cs[1:])))

def main():
    rng=Random(41)
    checks=0
    for d in (0,1,2,3,4,7,42,82):
        for _ in range(5):
            q=tuple(Q(rng.randint(-5,5),7) for i in range(2))
            j=tuple(Q(rng.randint(-5,5),3) for i in range(2))
            cs=[rng.randint(-20,20) for k in range(d+1)]
            assert homogeneous(q,mul(q,j),cs)==mul(powc(q,d),polynomial(j,cs))
            checks+=1
    for k in (0,1,3,20,1722,3362):
        for _ in range(10):
            a=[0]*(k+1)+[rng.randint(-5,5) for _ in range(8)]
            t=Q(1,3)
            v=sum(x*t**i for i,x in enumerate(a))
            tail=sum(x*t**i for i,x in enumerate(a[k+1:]))
            assert v==t**(k+1)*tail
            assert v/t**k==t*tail
            checks+=2
    for _ in range(200):
        w=(Q(rng.randint(-5,5),8),Q(rng.randint(-5,5),8))
        assert sum(x*x for x in w)<=1
        a=(Q(rng.randint(-20,20),3),Q(rng.randint(-20,20),7))
        n=rng.randrange(30)
        b=mul(a,powc(w,n))
        assert max(map(abs,b))<=sum(map(abs,a))
        checks+=1
    print(f'PASS {checks} exact Gaussian-rational homogeneous, tail and disk-majorant checks')

if __name__=='__main__':
    main()
