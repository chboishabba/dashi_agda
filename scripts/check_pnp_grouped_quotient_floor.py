"""Capped monotone grouped signed floors, with admissible-domain penalties."""
from itertools import combinations
from random import Random
from check_pnp_affine_normal_components import canon, Budget, Exhausted, satisfies
from check_pnp_adaptive_signed_escape import add, lower, point
from check_pnp_signed_quotient_minimum import minimum


def penalized(M,H,B):
    B.pay('penalty_input',1+len(M)+sum(len(A)+1 for A in H))
    Q=dict(M);K=1+sum(abs(w) for w in M.values())
    for A in H:add(Q,A,K)
    return Q


def pair_min(A,C,n,B):
    """Exact two-domain activation cells by rank counting, no tree construction."""
    (X,w),=A.items();(Y,z),=C.items();B.pay('pair_cell')
    N=1<<n;a=1<<(n-len(X));b=1<<(n-len(Y));I=canon(X+Y)
    c=0 if I is None else 1<<(n-len(I))
    return min(v for v,m in ((0,N-a-b+c),(w,a-c),(z,b-c),(w+z,c)) if m)


def grouped(M,n,B,bag=4,width=4,early=True):
    """Retain a partition and sound local floors; no cross-group agreement assumed."""
    groups=[({A:w},min(0,w)) for A,w in sorted(M.items()) if A and w]
    z=M.get((),0)+sum(v for _,v in groups);B.pay('group_input',1+len(groups))
    cache={}
    while len(groups)>1 and (not early or z<=0):
        best=None
        for i,j in combinations(range(len(groups)),2):
            B.pay('group_candidate');A,a=groups[i];C,c=groups[j]
            if len(A)+len(C)>bag:continue
            Q=A|C;k=tuple(sorted(Q))
            if k not in cache:
                cache[k]=pair_min(A,C,n,B) if len(Q)==2 else minimum(Q,n,B,width)[0]
            v=cache[k]
            # Even incomplete local min is sound; retain the previous floor.
            v=max(v,a+c);key=(v-a-c,-len(Q),-i,-j)
            if best is None or key>best[0]:best=(key,i,j,Q,v)
        if best is None:break
        key,i,j,Q,v=best;B.pay('group_merge');z+=key[0]
        groups.pop(j);groups.pop(i);groups.append((Q,v))
    return z


def conditioned(M,n,H,B,bag=4,width=4):
    """A positive result certifies every admissible y; nonpositive is inconclusive."""
    Q=penalized(M,H,B)
    return max(lower(M),grouped(Q,n,B,bag,width))


def main():
    rng=Random(369);checks=improved=empty=exact=0
    for n in range(7):
        for _ in range(35):
            M={():rng.randrange(-5,7)}
            for j in range(rng.randrange(8)):
                A=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))
                add(M,A,rng.randrange(-6,7))
            H=tuple(A for _ in range(rng.randrange(4)) if (A:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            B=Budget(1000000);Q=penalized(M,H,B);vals=[point(M,x) for x in range(1<<n) if satisfies(x,(),H)]
            q=min(point(Q,x) for x in range(1<<n));assert (q>0)==all(v>0 for v in vals)
            assert (not vals) or q<=min(vals)
            for bag in (1,2,4):
                a=grouped(Q,n,B,bag,2,False);assert lower(Q)<=a<=q
                v=conditioned(M,n,H,B,bag,2);assert not vals or v<=min(vals)
                improved+=a>lower(Q);checks+=1
            exact+=minimum(Q,n,B,n)[0]==q;empty+=not vals
    # Guarded negative marginal repaired by the existing min-plus kernel.
    M={():2,((1,0),):-3};H=(((1,0),),);B=Budget(1000)
    assert conditioned(M,1,H,B)==2 and minimum(penalized(M,H,B),1,B)[0]==2
    # No credit for unguarded covered states.
    assert conditioned(M,1,(),Budget(1000))<=0
    # Connected high rank: complementary negative pairs, extra connected
    # nonnegative edges. Width-zero global relaxation misses all pair gains.
    for n in (6,8,10):
        M={():n+1}
        for i in range(n):
            for b in (0,1):M[((1<<i,b),)]=-1
        for i,j in combinations(range(n),2):M[canon(((1<<i,0),(1<<j,0)))]=1
        B=Budget(10000000);old,done=minimum(M,n,B,0);assert old<=0 and not done
        C=Budget(10000000);a=grouped(M,n,C,2,1);assert a==1
        print('connected',n,'terms',len(M)-1,'old',old,'grouped',a,'global_charged',sum(B.stats.values()),'group_charged',sum(C.stats.values()))
    # Original adaptive block integration: guarded y=0 covers all t; y=1 has two lifts.
    from check_pnp_adaptive_signed_escape import certificate,reopen,portfolio
    F=tuple(canon(G) for G in (((1,0),),((1,0),(2,0)),((1,0),(2,1))))
    assert certificate(2,F,(2,),Budget(10000)) is None
    q=certificate(2,F,(2,),Budget(10000),admissible_envelope=conditioned)
    assert q is not None and q[1][-2:]==(2,0) and satisfies(reopen(q[1],1,Budget(1000)),(),F)
    # Actual connected marginal from distinct forbidden slots. Full tree
    # construction exceeds a 20k local cap, whereas one pair merge suffices.
    n=8;k=5;V=tuple(1<<(n+i) for i in range(k));D=[((1<<i,b),) for i in range(n) for b in (0,1)]
    D+=[canon(((1<<i,0),(1<<j,0))) for i,j in list(combinations(range(n),2))[:16]]
    F=tuple(canon(A+tuple((v,s>>i&1) for i,v in enumerate(V))) for s,A in enumerate(D))
    M={():1<<k};M.update({A:-1 for A in D});assert lower(M)==0
    try:minimum(M,n,Budget(20000),4)
    except Exhausted:pass
    else:raise AssertionError('full tree unexpectedly cheap')
    C=Budget(20000);a=conditioned(M,n,(),C);assert a>0
    B=Budget(100000);q=certificate(n+k,F,V,B,admissible_envelope=conditioned)
    assert q is not None and q[1][-1]==0 and q[1][-2]>0
    for y in (0,85,255):assert satisfies(reopen(q[1],y,B),(),F)
    print('connected_slot_control',n,k,'events',len(F),'floor',a,'floor_charged',sum(C.stats.values()),'actual_certificate_and_reopen',sum(B.stats.values()))
    fixtures=verified=unsat=0
    for n in range(1,7):
        for _ in range(25):
            F=tuple(G for _ in range(rng.randrange(8)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+1)))) is not None)
            P=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            S=[x for x in range(1<<n) if satisfies(x,P,F)]
            x,done,_,_=portfolio(n,P,F,2000000,admissible_envelope=conditioned)
            assert done and (x is not None)==bool(S)
            if x is not None:assert x in S;verified+=1
            else:unsat+=1
            fixtures+=1
    assert not portfolio(2,(),(),0,admissible_envelope=conditioned)[1]
    print(dict(checks=checks,strict_improvements=improved,penalty_exact=exact,empty_quotients=empty,fixtures=fixtures,verified=verified,unsat=unsat,controls='PASS'))

if __name__=='__main__':main()
