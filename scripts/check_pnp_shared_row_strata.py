"""Exact bounded affine row strata, shared across roots and incumbent time.
No global completeness claim: capped construction returns UNKNOWN via Exhausted.
Repository adapter uses existing affine normal component chart and budget.
"""
from check_pnp_affine_normal_components import bits, canon, chart, lift, satisfies


def build(n, R, P, B, rank_cap=16):
    """Return (u,V,all_points,strata,word_cost), or None at rank cap.
    Every mask bit denotes exactly one original point; no auxiliary multiplicity.
    Charge logical 64-bit words before allocations, not machine-clock time.
    """
    assert P == canon(P) and canon(P+tuple((r,1) for r in R)) == P
    B.pay('strata_chart', 1+n*(1+len(P)))
    u,V=chart(n,P); d=len(V)
    if d>rank_cap:return None
    N=1<<d; W=(N+63)//64
    B.pay('strata_storage', W*(1+d+n+sum(r.bit_count()+1 for r in R)))
    full=(1<<N)-1
    axes=[]
    for i in range(d):
        step=1<<i; p=((1<<step)-1)<<step; size=2*step
        while size<N:
            B.pay('strata_axis',W);p|=p<<size;size*=2
        axes.append(p)
    cols=[]
    for j in range(n):
        p=full if u>>j&1 else 0
        for i,v in enumerate(V):
            B.pay('strata_column',W)
            if v>>j&1:p^=axes[i]
        cols.append(p)
    S=[]
    for r in R:
        T=[full]
        for j in bits(r):
            B.pay('strata_count', W*(4*len(T)+2));p=cols[j];q=full^p
            U=[0]*(len(T)+1)
            for k,a in enumerate(T):U[k]|=a&q;U[k+1]|=a&p
            T=U
        S.append(tuple(T))
    return n,tuple(R),P,u,tuple(V),full,tuple(S),W,tuple(cols)


def observe(n,R,P,x,C,B):
    """SAT witness, EMPTY exact no-trade, or COVER at incumbent.
    C is keyed by exact original source and carrier.
    Return all-root counts conditional on monotonicity, plus cover count.
    """
    assert satisfies(x,P,())
    n0,R0,P0,u,V,full,S,W,cols=C
    assert (n,tuple(R),P)==(n0,R0,P0)
    M=full;strict=0;cover=full;root=[]
    for r,T in zip(R,S):
        w=(r&x).bit_count();a=0;b=0
        B.pay('strata_observe',W*(w+5))
        for z in T[:w]:a|=z
        b=a|T[w];M&=b;strict|=a;root.append(a);cover&=T[1]
    I=M&strict
    B.pay('strata_counts',W*(2+len(root)))
    counts=tuple((M&a).bit_count() for a in root);num=cover.bit_count()
    if not I:return ('COVER' if all((r&x).bit_count()==1 for r in R) else 'EMPTY'),None,counts,num
    # Prefer a directly available original cover; otherwise any strict improvement.
    Q=I&cover or I
    B.pay('strata_reopen',W+n*(1+len(P))+sum(r.bit_count() for r in R))
    z=(Q&-Q).bit_length()-1;y=lift(u,V,z);v=x^y
    q=tuple((r&x).bit_count()-(r&y).bit_count() for r in R)
    assert satisfies(y,P,()) and all(a>=0 and a%2==0 for a in q) and any(q)
    return 'SAT',v,counts,num


def descent(n,R,P,x,B,rank_cap=16,history=None,k_index=0):
    """None return means rank refusal; otherwise (cover_or_None, decisive).
    Exact strata exclude the original cover, not merely a sampled root.
    No source or K change is permitted during this cached query.
    """
    C=build(n,R,P,B,rank_cap)
    if C is None:return None
    status,v,counts,num=observe(n,R,P,x,C,B)
    if not num:return None,True
    if status=='COVER':return x,True
    assert status=='SAT' and v is not None
    y=x^v;q=tuple((r&x).bit_count()-(r&y).bit_count() for r in R)
    assert all((r&y).bit_count()==1 for r in R)
    if history is not None:history.append((k_index,0,x,v,q,B.left))
    return y,True
