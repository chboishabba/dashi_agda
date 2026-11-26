"""Min-plus normal-boundary join for signed affine quotient certificates."""
from random import Random
from check_pnp_affine_normal_components import canon, chart, Budget, satisfies
from check_pnp_normal_boundary_join import tree, rows, value
from check_pnp_adaptive_signed_escape import (add, lower, certificate, reopen,
    point, portfolio)


def minimum(M,n,B,width=6):
    """(lower bound, exact flag). Over-width cuts safely relax correlations."""
    const=M.get((),0);F=tuple(sorted(A for A,w in M.items() if A and w))
    if not F:return const,True
    root,boundary,space=tree(n,F,B)
    def run(node):
        mask,A,C=node;D=boundary(mask);T={}
        if A is None:
            G=F[mask.bit_length()-1];w=M[G]
            if len(D)>width:return None,min(0,w)
            B.pay('min_leaf',1<<len(D))
            for p in range(1<<len(D)):
                P=rows(D,p);u,V=chart(n,canon(P));H=canon(P+G)
                if w<0 and H is not None:u=chart(n,H)[0];cost=w
                elif w>0 and not satisfies(u,(),(G,)):
                    v=next((v for v in V if any((a&v).bit_count()%2 for a,b in G)),None)
                    if v is None:cost=w
                    else:u^=v;cost=0
                else:cost=0
                T[p]=(cost,rows(space(mask),value(space(mask),u)))
        else:
            L,l=run(A);R,r=run(C)
            if L is None or R is None or len(D)>width:return None,l+r
            B.pay('min_pairs',len(L)*len(R))
            for a,H in L.values():
                for b,J in R.values():
                    K=canon(H+J)
                    if K is None:continue
                    x=chart(n,K)[0];p=value(D,x);cost=a+b
                    if p not in T or cost<T[p][0]:T[p]=(cost,K)
        assert len(T)==1<<len(D)
        return T,min(c for c,H in T.values())
    T,a=run(root)
    return const+a,T is not None


def envelope(M,n,B):
    return minimum(M,n,B)[0]


def main():
    rng=Random(369);checks=exact=improved=relaxed=0
    for n in range(8):
        for _ in range(45):
            M={():rng.randrange(-4,8)}
            for j in range(rng.randrange(1,9)):
                A=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))
                add(M,A,rng.randrange(-8,9))
            want=min(point(M,x) for x in range(1<<n))
            for w in (0,1,2,n):
                a,done=minimum(M,n,Budget(1000000),w)
                assert lower(M)<=a<=want
                if done:assert a==want;exact+=1
                else:relaxed+=1
                if w==n:assert done
                improved+=a>lower(M);checks+=1
    for n in (8,16,32,64):
        r=min(n,12);A=[((1<<n)-1)^(1<<i) for i in range(r)]
        M={():r+1};M.update({((a,b),):-1 for a in A for b in (0,1)})
        B=Budget(10000000);a,done=minimum(M,n,B,1)
        assert done and a==1 and lower(M)==1-r
        print('dense',n,'rank',r,'independent',lower(M),'correlated',a,'charged',sum(B.stats.values()))
    V=(8,16);F=tuple(canon(tuple((1<<i,y>>i&1) for i in range(3))+((8,y&1),(16,(y>>1)&1))) for y in range(8))
    assert certificate(5,F,V,Budget(1000000)) is None
    B=Budget(1000000);q=certificate(5,F,V,B,envelope=envelope)
    assert q is not None and not q[0] and q[1][-2:]==(3,0)
    for y in range(8):assert satisfies(reopen(q[1],y,B),(),F)
    assert certificate(2,(((1,0),),((3,0),)),(1,),Budget(1000000),envelope=envelope) is None
    fixtures=verified=empty=0
    for n in range(1,7):
        for _ in range(35):
            F=tuple(G for _ in range(rng.randrange(8)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+1)))) is not None)
            P=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            truth=[x for x in range(1<<n) if satisfies(x,P,F)]
            x,done,route,s=portfolio(n,P,F,2000000,envelope=envelope)
            assert done and (x is not None)==bool(truth)
            if x is not None:assert x in truth;verified+=1
            else:empty+=1
            fixtures+=1
    assert not portfolio(3,(),(),0,envelope=envelope)[1]
    print(dict(checks=checks,exact=exact,relaxed=relaxed,improved=improved,fixtures=fixtures,verified=verified,empty=empty,conditional_reopens=8,controls='PASS'))

if __name__=='__main__':main()
