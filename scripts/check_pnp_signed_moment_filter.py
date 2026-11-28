"""Adaptive signed Krylov moment witness: exact inertia, capped affine powers."""
from fractions import Fraction
from math import lcm
from random import Random
from check_pnp_affine_normal_components import (canon, chart, lift, restrict,
    simplify, satisfies, Budget, Exhausted)
from check_pnp_adaptive_signed_escape import add, point
from check_pnp_partial_quotient import gated, mass, positive_point, solve as partial


def product(A,C,B,width):
    T={}
    for P,w in A.items():
        for Q,z in C.items():
            B.pay('moment_intersection');add(T,canon(P+Q),w*z)
            if len(T)>width:return None
    return T


def direction(H,B):
    """Exact rational congruence; returns positive direction or nonpositive inertia."""
    A=[[Fraction(x) for x in row] for row in H];history=[]
    while A:
        n=len(A);B.pay('inertia_scan',n*n)
        p=next((i for i in range(n) if A[i][i]>0),None)
        if p is not None:v=[Fraction(i==p) for i in range(n)];break
        pair=next(((i,j) for i in range(n) if A[i][i]==0 for j in range(n) if A[i][j]),None)
        if pair is not None:
            i,j=pair;b=A[i][j];v=[Fraction(0)]*n
            v[j]=1 if b>0 else -1;v[i]=1+abs(A[j][j])/abs(b);break
        p=next((i for i in range(n) if A[i][i]<0),None)
        if p is None:return None
        I=[i for i in range(n) if i!=p];a=A[p][p];r=[A[p][i]/a for i in I]
        history.append((p,r));B.pay('inertia_elimination',n*n)
        A=[[A[i][j]-A[i][p]*r[k] for k,j in enumerate(I)] for i in I]
    else:return None
    for p,r in reversed(history):v.insert(p,-sum(a*b for a,b in zip(r,v)))
    B.pay('inertia_receipt',len(v)**2)
    g=lcm(*(x.denominator for x in v));v=[int(x*g) for x in v]
    assert sum(H[i][j]*a*b for i,a in enumerate(v) for j,b in enumerate(v))>0
    return v


def moment_point(n,M,H,B,width=256,degree=4):
    Q=gated(M,H,B,width)
    if len(Q)>width:return None
    powers=[{():1},Q];mom=[1<<n,mass(n,Q,(),B)]
    for d in range(degree+1):
        B.pay('moment_stage')
        while len(powers)<=2*d+1:
            T=product(powers[-1],Q,B,width)
            if T is None:return None
            powers.append(T);mom.append(mass(n,T,(),B))
        v=direction([[mom[i+j+1] for j in range(d+1)] for i in range(d+1)],B)
        if v is None:continue
        # Keep the polynomial in the moment basis, not an expanded square chart.
        w=[0]*(2*d+2);B.pay('polynomial_product',len(v)**2)
        for i,a in enumerate(v):
            for j,b in enumerate(v):w[i+j+1]+=a*b
        def energy(P):
            return sum(c*mass(n,powers[i],P,B) for i,c in enumerate(w) if c)
        c=sum(a*b for a,b in zip(w,mom));assert c>0
        P=();y=0
        for i in range(n):
            A=canon(P+((1<<i,0),));q=energy(A)
            if q>0:P=A;c=q
            else:P=canon(P+((1<<i,1),));y|=1<<i;c-=q
            assert c>0
        z=point(M,y);assert z>0 and satisfies(y,(),H) and point(Q,y)>0
        B.pay('moment_admission');B.pay('moment_degree',d)
        return y,z,()
    return None


def direct(n,required,F,cap,width=256,degree=4):
    B=Budget(cap)
    try:
        B.pay('input',n+len(required)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,required,F,B)
        if q is None:return None,B.stats,True
        u,V,H=q;H=simplify(H,B)
        if () in H:return None,B.stats,True
        M={():1}
        for A in H:add(M,A,-1)
        q=moment_point(len(V),M,(),B,width,degree)
        if q is None:return None,B.stats,False
        y=lift(u,V,q[0]);assert satisfies(y,required,F)
        return y,B.stats,True
    except (Exhausted,RecursionError):return None,B.stats,False


def solve(n,required,F,cap,width=256,degree=4):
    share=cap//2;x,s,done=direct(n,required,F,share,width,degree)
    if done:return x,s,done
    def consume(n,M,H,B,w):return moment_point(n,M,H,B,min(w,width),degree)
    x,t,done=partial(n,required,F,cap-share,point_solver=consume);s.update(t)
    return x,s,done


def main():
    rng=Random(369);checks=complete=positive=empty=barriers=matrix=0
    # Full degree for small finite level spectra; no support assumptions.
    for n in range(6):
        for _ in range(35):
            M={():rng.randrange(-3,4)}
            for j in range(rng.randrange(7)):
                A=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))
                add(M,A,rng.randrange(-3,4))
            H=tuple(A for _ in range(rng.randrange(3)) if (A:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            B=Budget(1000000);Q=gated(M,H,B,256);levels={point(Q,x) for x in range(1<<n)}-{0}
            q=moment_point(n,M,H,B,4096,max(0,len(levels)-1))
            truth=[x for x in range(1<<n) if point(M,x)>0 and satisfies(x,(),H)]
            assert (q is not None)==bool(truth)
            if q is not None:assert q[0] in truth;positive+=1
            else:empty+=1
            complete+=1
            # Check every lower-degree accepted witness and original signed value.
            for d in (0,1,2):
                r=moment_point(n,M,H,B,4096,d)
                if r is not None:assert r[0] in truth and r[1]==point(M,r[0])
                checks+=1
    # Congruence controls: zero pivot with off-diagonal, negative pivot Schur gain.
    for A,want in (([[0,1],[1,-9]],True),([[-1,2],[2,-1]],True),([[-1,1],[1,-1]],False),([[0,0],[0,0]],False)):
        assert (direction(A,Budget(1000)) is not None)==want;matrix+=1
    # Prior single-domain probe fails on this positive singleton chart.
    for n in (4,6,8):
        M={():1};M.update({((1<<i,0),):-1 for i in range(n)})
        assert positive_point(n,M,(),Budget(100000)) is None
        B=Budget(3000000);q=moment_point(n,M,(),B,4096,n)
        assert q is not None and q[0]==(1<<n)-1
        print('singleton',n,'degree',B.stats['moment_degree'],'charged',sum(B.stats.values()))
    # Low-degree obstruction survives ambient extension; no claim of SAT hardness.
    for n in (6,8,10):
        M={():1};M.update({((1<<i,0),):-2 for i in range(n)})
        assert moment_point(n,M,(),Budget(3000000),4096,1) is None;barriers+=1
    # Actual original block, previously no positive offered quotient restriction.
    from check_pnp_partial_quotient import block_witness
    F=(((9,0),(6,0)),((16,1),(11,0),(7,0)),((19,1),(9,0),(4,0)),
       ((20,0),),((20,1),(8,0),(2,0)),((22,0),),((25,1),(4,0)),
       ((26,0),),((27,0),),((27,0),(7,0)),((30,1),))
    assert block_witness(5,F,(16,),Budget(100000),promotions=0) is None
    B=Budget(1000000);q=block_witness(5,F,(16,),B,promotions=0,point_solver=moment_point)
    assert q is not None and q[1]==0 and satisfies(q[0],(),F) and B.stats['moment_degree']>0
    print('block_control','witness',q[0],'degree',B.stats['moment_degree'],'charged',sum(B.stats.values()))
    # Actual source/quotient integration, with witness-only UNKNOWN firewall.
    fixtures=verified=completed_empty=unknown=0
    for n in range(1,7):
        for _ in range(30):
            F=tuple(A for _ in range(rng.randrange(10)) if (A:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            P=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            S=[x for x in range(1<<n) if satisfies(x,P,F)]
            x,_,done=solve(n,P,F,2000000);fixtures+=1
            if x is not None:assert done and x in S;verified+=1
            elif done:assert not S;completed_empty+=1
            else:unknown+=1
    assert not solve(3,(),(),0)[2]
    M={():1,((1,0),):-3};H=(((1,0),),)
    assert moment_point(1,M,H,Budget(10000),width=2)[:2]==(1,1)
    M={():1};M.update({((1<<i,0),):-1 for i in range(4)})
    assert moment_point(4,M,(),Budget(10000),width=5,degree=4) is None
    print(dict(full_spectrum=complete,positive=positive,no_positive=empty,lower_degree=checks,matrix=matrix,barriers=barriers,fixtures=fixtures,verified=verified,empty=completed_empty,unknown=unknown,controls='PASS'))

if __name__=='__main__':main()
