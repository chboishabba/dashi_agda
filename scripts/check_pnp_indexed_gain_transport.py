"""Exact (k,time) transport of homogeneous signed gain charts.
Rank-one keys match check_pnp_x3c_gain_descent.gain_chart.
No universal observation or clock theorem is claimed.
"""
from random import Random
from math import comb


def dot(a,b):
    return (a&b).bit_count()%2


def image(V,z):
    out=0
    for i,v in enumerate(V):
        if z>>i&1:out^=v
    return out


def evaluate(M,z):
    return sum(w*dot(a,z) for ((a,b),),w in M.items())


def transport(M,V,a):
    """Return (old gain at new anchor, new homogeneous gain chart).
    V is the linear part of the coordinate embedding, a its origin.
    """
    N={};offset=0
    for ((s,b),),w in M.items():
        assert s and b==1
        p=dot(s,a);offset+=w*p
        q=sum(dot(s,v)<<i for i,v in enumerate(V))
        if q:
            key=((q,1),);N[key]=N.get(key,0)+(-w if p else w)
    return offset,{A:w for A,w in N.items() if w}


def advance(M,a):
    """Same k, changed incumbent; no signature regrouping required."""
    return evaluate(M,a),{((s,b),):(-w if dot(s,a) else w) for ((s,b),),w in M.items()}


def shift_table(T,D,a,g):
    """Existing min-plus table format: boundary label -> (cost, affine rows)."""
    shift=sum(dot(s,a)<<i for i,s in enumerate(D))
    return {q^shift:(cost-g,tuple((s,b^dot(s,a)) for s,b in H))
            for q,(cost,H) in T.items()}


def shift_moments(mu,g):
    return [sum(comb(j,l)*(-g)**(j-l)*mu[l] for l in range(j+1))
            for j in range(len(mu))]


def source_chart(n,x,V):
    M={}
    for i in range(n):
        s=sum(((v>>i)&1)<<j for j,v in enumerate(V))
        if s:
            A=((s,1),);M[A]=M.get(A,0)+(1 if x>>i&1 else -1)
    return {A:w for A,w in M.items() if w}


def main():
    rng=Random(369);cases=points=squares=receipts=table_checks=moment_checks=0
    for d in range(8):
        for _ in range(50):
            n=d+5;V=tuple((1<<j)|(rng.randrange(32)<<d) for j in range(d));x=rng.randrange(1<<n)
            M=source_chart(n,x,V);a=rng.randrange(1<<d)
            # Any nested chart, including rank zero; shuffled independent basis.
            order=list(range(d));rng.shuffle(order);e=rng.randrange(d+1)
            L=tuple(1<<i for i in order[:e]);c=rng.randrange(1<<e);b=image(L,c)
            h,N=transport(M,L,a);newx=x^image(V,a);newV=tuple(image(V,v) for v in L)
            assert N==source_chart(n,newx,newV)
            g,T=advance(M,b);h2,N2=transport(T,L,a)
            g2,U=advance(N,c);assert U==N2 and g+h2==h+g2;squares+=1
            vals=[evaluate(M,z) for z in range(1<<d)];upper=max(vals)
            for z in range(1<<e):
                want=newx.bit_count()-(newx^image(newV,z)).bit_count()
                assert evaluate(N,z)==want==evaluate(M,a^image(L,z))-h
                assert evaluate(N,z)<=upper-h;points+=1
            # An attained upper bound transports as an exact remaining gain at fixed k.
            g,T=advance(M,a);assert set(T)==set(M)
            assert max(evaluate(T,z) for z in range(1<<d))==upper-g
            assert evaluate(T,0)==0;receipts+=1
            # Existing min-plus boundary table: translate its boundary label,
            # scalar value and attaining coordinate, without rerunning the join.
            D=tuple(1<<i for i in order[:e]);label=lambda z:sum(dot(v,z)<<i for i,v in enumerate(D))
            F={A:w for A,w in M.items() if rng.randrange(2)}
            f,P=advance(F,a);old={};new={}
            for z in range(1<<d):
                for tab,Z in ((old,F),(new,P)):
                    q=label(z);v=evaluate(Z,z)
                    if q not in tab or v<tab[q][0]:tab[q]=(v,z)
            T0={q:(cost,tuple((1<<i,(z>>i)&1) for i in range(d))) for q,(cost,z) in old.items()}
            T1=shift_table(T0,D,a,f)
            for q,(v,z) in new.items():
                cost,H=T1[q];w=sum(b*s for s,b in H)
                assert v==cost==evaluate(P,w) and label(w)==q;table_checks+=1
            # Complete moments can be time-shifted; no new power intersections.
            mu=[sum(v**j for v in vals) for j in range(6)]
            for j,m in enumerate(shift_moments(mu,g)):
                assert m==sum(evaluate(T,z)**j for z in range(1<<d));moment_checks+=1
            # Repeat transport with arbitrary injective dense map.
            K=list(1<<i for i in range(d))
            for j in range(d):
                if d>1:
                    i=(j+1)%d;K[j]^=K[i]
            K=tuple(K[:e]);h,N=transport(M,K,a)
            assert N==source_chart(n,newx,tuple(image(V,v) for v in K))
            cases+=1
    # A cancelled signature is safe for all retained actions, not a changed source action.
    M=source_chart(2,1,(3,));assert M==source_chart(2,2,(3,))=={}
    assert source_chart(2,0,(3,))=={((1,1),):-2}
    assert source_chart(2,3,(3,))=={((1,1),):2}
    # Refining away an old maximizing witness does not preserve its lower bound.
    M={((1,1),):2};h,N=transport(M,(),0);assert h==0 and N=={}
    # Translating a nonpositive chart can expose positive gain at a worse incumbent.
    M={((1,1),):-2};g,T=advance(M,1);assert g==-2 and T=={((1,1),):2}
    print(dict(cases=cases,pointwise=points,commuting_squares=squares,upper_receipts=receipts,table_checks=table_checks,moment_checks=moment_checks,controls='PASS'))


if __name__=='__main__':main()
