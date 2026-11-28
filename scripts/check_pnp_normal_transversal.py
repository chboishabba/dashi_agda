"""Rado normal transversal and exact deficient-core reopening over F2."""
from collections import deque
from random import Random
from check_pnp_affine_normal_components import (
    canon, chart, restrict, lift, simplify, satisfies, cnf_flats, Budget, Exhausted, bits)
from check_pnp_normal_boundary_join import join


def transversal(F,B):
    """Independent representative rows; maximum deficiency core via exchange reachability."""
    chosen={}
    while True:
        E={}; ids=sorted(chosen)
        for k,j in enumerate(ids):
            a,_=chosen[j]; z=1<<k
            for i in sorted(E,reverse=True):
                if a>>i&1: v,c=E[i];a^=v;z^=c
            assert a;E[a.bit_length()-1]=(a,z)
            B.pay('basis')
        prev={j:None for j in range(len(F)) if j not in chosen}
        Q=deque(prev); terminal=None
        while Q and terminal is None:
            j=Q.popleft()
            for row in F[j]:
                B.pay('exchange');a,z=row[0],0
                for i in sorted(E,reverse=True):
                    if a>>i&1:v,c=E[i];a^=v;z^=c
                if a:terminal=(j,row);break
                for k in bits(z):
                    h=ids[k]
                    if h not in prev:prev[h]=(j,row);Q.append(h)
        if terminal is None:
            R=tuple(sorted(prev));U=canon((a,0) for j in R for a,b in F[j]);
            assert len(U)==sum(j in chosen for j in R)
            assert len(R)-len(U)==len(F)-len(chosen)
            return chosen,R
        j,row=terminal
        while True:
            chosen[j]=row
            if prev[j] is None:break
            j,row=prev[j]
        assert len(canon((a,0) for a,b in chosen.values()))==len(chosen)


def reopen_core(n,F,chosen,R,x):
    """Preserve every core normal; force a complementary normal for each other flat."""
    R=set(R);U=canon((a,0) for j in R for a,b in F[j])
    pins=tuple((a,(a&x).bit_count()%2) for a,b in U)
    extra=tuple((chosen[j][0],chosen[j][1]^1) for j in range(len(F)) if j not in R)
    H=canon(pins+extra);assert H is not None
    y=chart(n,H)[0];assert satisfies(y,(),F)
    return y


def solve(n,required,F,cap):
    B=Budget(cap)
    try:
        B.pay('input',n+len(required)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,required,F,B)
        if q is None:return None,B.stats,True
        u,V,H=q;H=simplify(H,B);d=len(V)
        if () in H:return None,B.stats,True
        chosen,R=transversal(H,B);B.pay('core',len(H)+1)
        core=tuple(H[j] for j in R)
        x,w=join(d,core,B)
        if x is None:return None,B.stats,True
        y=lift(u,V,reopen_core(d,H,chosen,R,x));assert satisfies(y,required,F)
        return y,B.stats,True
    except Exhausted:return None,B.stats,False


def main():
    rng=Random(369);fixtures=verified=empty=deficiency=projection=0
    for n in range(8):
        for _ in range(35):
            required=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            F=tuple(G for _ in range(rng.randrange(7)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(7))]
            for H in (F,cnf_flats(f)):
                chosen,R=transversal(H,Budget(1000000))
                worst=max(mask.bit_count()-len(canon((a,0) for j in bits(mask) for a,b in H[j])) for mask in range(1<<len(H)))
                assert worst==len(H)-len(chosen);deficiency+=1
                for x in range(1<<n):
                    if satisfies(x,(),tuple(H[j] for j in R)):
                        y=reopen_core(n,H,chosen,R,x)
                        assert all((a&(x^y)).bit_count()%2==0 for j in R for a,b in H[j]);projection+=1
                truth=[x for x in range(1<<n) if satisfies(x,required,H)]
                x,s,done=solve(n,required,H,1000000);assert done and (x is not None)==bool(truth)
                if x is not None:assert x in truth;verified+=1
                else:empty+=1
                fixtures+=1
    # Dense normal graph: each flat shares a large common normal subspace and has a private normal.
    for k in (8,16,32,64):
        n=2*k;normal=[((1<<n)-1)^(1<<i) for i in range(n)]
        H=tuple(canon(tuple((a,0) for a in normal[:k])+((normal[k+j],0),)) for j in range(k))
        chosen,R=transversal(H,Budget(1000000));assert not R and len(chosen)==k
        x,s,done=solve(n,(),H,1000000);assert done and x is not None and satisfies(x,(),H)
        assert s['leaf_rows']==0
        print('dense',n,'core',len(R),'charged',sum(s.values()))
    # A true deficient subproblem, with independent outside representatives.
    H=tuple(canon(G) for G in (((1,0),),((1,1),),((2,0),(4,0)),((4,1),(8,0))))
    chosen,R=transversal(H,Budget(10000));assert R==(0,1) and len(chosen)==3
    assert solve(4,(),H,100000)[0] is None
    assert solve(4,(),H,0)[2] is False
    print(dict(fixtures=fixtures,verified=verified,empty=empty,deficiency=deficiency,projection=projection,dense=4,controls='PASS'))

if __name__=='__main__':main()
