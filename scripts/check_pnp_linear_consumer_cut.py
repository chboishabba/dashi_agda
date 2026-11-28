"""Exact fixed-read F3 linear-state consumer cut, on Boolean sources.
No extension to arbitrary state encodings or adaptive per-input read sets.
"""
from itertools import product
from random import Random
from collections import Counter
from check_pnp_signed_component_histogram import rref


def apply(A,x):return tuple(sum(a*b for a,b in zip(row,x))%3 for row in A)
def rank(A,n):return len(rref(tuple(tuple(row)+(0,) for row in A),n)[0])
def main():
    C=Counter()
    for i in range(512):
        g=Random(3692844+i);n=1+i%6;A=tuple(tuple(g.randrange(3) for _ in range(n)) for _ in range(i%5));R=tuple(j for j in range(n) if g.randrange(3)==0)
        E=tuple(tuple(int(j==k) for j in range(n)) for k in R);M=A+E
        B=tuple(tuple(g.randrange(3) for _ in range(n)) for _ in range(1+i%4)) if i%2 else tuple(tuple(sum(a*r[j] for a,r in zip(c,M))%3 for j in range(n)) for c in (tuple(g.randrange(3) for _ in M) for _ in range(1+i%4)))
        ok=rank(M+B,n)==rank(M,n);seen={};pair=None
        for x in product(range(2),repeat=n):
            k=apply(M,x);v=apply(B,x)
            if k in seen and seen[k][0]!=v:pair=(x,seen[k][1])
            seen[k]=v,x;C['boolean_points']+=1
        d0=None
        for d in product(range(3),repeat=n):
            if any(apply(M,d)) or not any(apply(B,d)):continue
            x=tuple(int(a==1) for a in d);y=tuple(int(a==2) for a in d)
            assert apply(M,x)==apply(M,y) and apply(B,x)!=apply(B,y)
            d0=d;C['kernel_witnesses']+=1
        assert ok==(pair is None)==(d0 is None)
        if ok:assert rank(B,n)<=rank(A,n)+len(R)
        C['fixtures']+=1;C['sufficient' if ok else 'obstructed']+=1
    assert [x for x in product(range(2),repeat=2) if sum(x)%3==0]==[(0,0)]
    assert rank(((1,1),),2)==1
    print(dict(C,adaptive_firewall=True))
if __name__=='__main__':main()
