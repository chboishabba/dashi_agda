"""Hyperplane packet bundles: exact quadratic normal form and bounded re-expansion."""
from random import Random
from collections import Counter
from itertools import combinations
from check_p0_affine_coface_20261125 import plain,norm,bits,value,add

def batch(H,terms,n):
    # Work in free coordinates of the parent; each child must be codim one.
    Q={}
    for B,P in terms:
        assert len(B)==len(H)+1 and plain(H+B)==B
        a,b=next((a,b) for a,b in B if plain(H+((a,b),))!=H)
        # child indicator, normalized in the parent coordinates
        L=norm(H,(1^b,)+tuple(int(a>>i&1) for i in range(n)))
        P=norm(H,P)
        for i,l in enumerate(L):
            if l:
                for j,p in enumerate(P):
                    if p:
                        k=((1<<(i-1)) if i else 0)|((1<<(j-1)) if j else 0)
                        Q[k]=Q.get(k,0)^p
    # q0 + sum_i y_i (q_i + sum_{j>i} q_ij y_j)
    out={};base=[0]*(n+1)
    for k,p in Q.items():
        if k.bit_count()==0:base[0]^=p
        elif k.bit_count()==1:base[k.bit_length()]^=p
    add(out,H,base)
    for i in range(n):
        P=[0]*(n+1)
        for j in range(i+1,n):P[j+1]=Q.get((1<<i)|(1<<j),0)
        if any(P):
            B=plain(H+((1<<i,1),));assert B is not None;add(out,B,P)
    return out

def main():
    rng=Random(890);stats=Counter()
    for n in range(2,9):
        for _ in range(80):
            H=plain(tuple((rng.randrange(1<<n),0) for _ in range(rng.randrange(n-1))))
            terms=[]
            for j in range(rng.randrange(2,26)):
                a=rng.randrange(1,1<<n);b=rng.randrange(2);B=plain(H+((a,b),))
                if B is not None and len(B)==len(H)+1:
                    terms.append((B,tuple(rng.randrange(1<<(n+1)) for i in range(n+1))))
            T=batch(H,terms,n);assert len(T)<=n-len(H)+1
            for x in range(1<<n):
                u=v=0
                for B,P in terms:u^=value(B,P,x)
                for B,P in T.items():v^=value(B,P,x)
                assert u==v;stats['point_checks']+=1
            stats['bundles']+=1;stats['input_terms']+=len(terms);stats['output_terms']+=len(T)
    S=[(((a,0),),(1,0,0)) for a in (1,2,3)];assert batch((),S,2)=={():(1,0,0)}
    # all seven nonzero linear forms on the 3-dimensional Fano frame
    S=[(((a,0),),(1,0,0,0)) for a in range(1,8)];assert batch((),S,3)=={():(1,0,0,0)}
    print(dict(stats))
if __name__=='__main__':main()
