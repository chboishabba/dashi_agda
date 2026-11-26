"""Charged signed min-plus boundary on projected affine domains, original reopening."""
from random import Random
from check_pnp_affine_normal_components import (canon,chart,lift,restrict,split,
    simplify,satisfies,cnf_flats,Budget,Exhausted)
from check_pnp_normal_boundary_join import tree,rows,value,join
from check_pnp_normal_transversal import transversal,reopen_core
from check_pnp_collective_fibre_escape import coordinates,domain,dot,blocks
from check_pnp_adaptive_signed_escape import (forest,masked,marginal,lower,intersect,
    reopen,point,certificate as old_certificate,portfolio as signed_portfolio)
from check_p0_collective_forest_20261126 import portfolio as direct_portfolio
from check_p0_affine_resolvent_20261126 import valid


def component_min(n,F,B):
    """Factors (flat,weight,hard); hard means its activation is forbidden."""
    if not F:return 0,0
    root,boundary,space=tree(n,tuple(G for G,w,h in F),B);width=0
    def run(node):
        nonlocal width
        mask,A,C=node;D=boundary(mask);width=max(width,len(D));T={}
        if A is None:
            G,w,h=F[mask.bit_length()-1]
            B.pay('min_leaf',1<<len(D))
            for p in range(1<<len(D)):
                P=rows(D,p);u,V=chart(n,canon(P));options=[]
                R=canon(P+G)
                if R is not None and not h:options.append((w,chart(n,R)[0]))
                if satisfies(u,(),(G,)):options.append((0,u))
                else:
                    v=next((v for v in V if any(dot(a,v) for a,b in G)),None)
                    if v is not None:options.append((0,u^v))
                if options:
                    z,x=min(options);T[p]=(z,rows(space(mask),value(space(mask),x)))
            return T
        L=run(A);R=run(C);B.pay('min_pairs',len(L)*len(R))
        for z,l in L.values():
            for w,r in R.values():
                H=canon(l+r)
                if H is None:continue
                x=chart(n,H)[0];p=value(D,x);c=z+w
                if p not in T or c<T[p][0]:T[p]=(c,H)
        return T
    T=run(root)
    return (T[0][0] if 0 in T else None),width


def correlated(n,M,H,B,early=True):
    """Safe lower bound (or exact if early=False); None means no admissible y."""
    H=set(H);B.pay('quotient_input',n+sum(len(G)+1 for G in M)+sum(len(G)+1 for G in H)+1)
    if () in H:return None
    constant=M.get((),0)
    F=tuple((G,0,True) if G in H else (G,M[G],False) for G in sorted((set(M)-{()})|H))
    base=constant+sum(min(0,w) for G,w,h in F)
    if not F or (early and base>0):return base
    basis,parts=split(n,tuple(G for G,w,h in F),B)
    dual=[];owner={i:j for j,(I,_) in enumerate(parts) for i in I}
    for i in range(len(basis)):
        B.pay('min_dual',len(basis)+1);dual.append(chart(n,canon(rows(basis,1<<i)))[0])
    groups=[[] for I,_ in parts]
    for G,w,h in F:
        B.pay('min_transport',len(G)+1)
        R=tuple((value(dual,a),b) for a,b in G)
        j=owner[(R[0][0]&-R[0][0]).bit_length()-1];I=parts[j][0]
        assert all(all(owner[i]==j for i in range(len(basis)) if a>>i&1) for a,b in R)
        P=canon((sum(((a>>i)&1)<<l for l,i in enumerate(I)),b) for a,b in R)
        assert P is not None;groups[j].append((P,w,h))
    # Independent normal-space components: sum of minima is exact, and partial
    # replacement of the crude local floors is a monotone safe lower bound.
    for j in sorted(range(len(groups)),key=lambda j:(len(groups[j]),len(parts[j][0]),j)):
        G=groups[j];old=sum(min(0,w) for A,w,h in G)
        z,_=component_min(len(parts[j][0]),G,B)
        if z is None:return None
        assert z>=old;base+=z-old
        if early and base>0:return base
    return base


def attempt(n,M,H,B,cap):
    B.pay('quotient_attempt');limit=min(cap,B.left);local=Budget(limit)
    try:a=correlated(n,M,H,local);done=True
    except (Exhausted,RecursionError):a,done=lower(M),False
    B.pay('quotient_work',min(limit,limit-local.left))
    return a,done


def certificate(n,F,V,B,width=256,quotient_cap=20000):
    """Donor masked chart with a charged correlated quotient consumer."""
    k=len(V);assert k;U=coordinates(n,V);d=len(U);H=set();E=[]
    B.pay('chart',n+1)
    for G in F:
        B.pay('scan',1+len(G));A=canon((sum(dot(a,v)<<i for i,v in enumerate(U+list(V))),b) for a,b in G)
        if A is None:continue
        P=domain(A,d)
        if len(A)==len(P):H.add(P)
        else:E.append(A)
    T=forest(E,n,B);R=set(range(len(E)));Q={():1};stages=0
    order=sorted(R,key=lambda i:(len(E[i]),-sum(i in (a,b) for a,b,_ in T),i))
    while True:
        B.pay('checkpoint');L=masked(Q,E,R,T,B);M=marginal(L,d,k,B);a=lower(M)
        if a<=0 and d:
            a,done=attempt(d,M,H,B,quotient_cap)
            if done and a is None:
                # Vacuous on the empty admissible quotient; keep H unchanged.
                a=1;B.pay('empty_quotient')
            if done and a>0:B.pay('correlation_admission')
        if a>0:return tuple(sorted(H)),(tuple(U),tuple(V),tuple(E),L,a,stages)
        if not R:return None
        i=order[stages];P=dict(Q);intersect(Q,E[i],-1,B,P)
        if len(P)>width:return None
        Q=P;R.remove(i);stages+=1;B.pay('promoted')


def solve(n,required,F,cap,width=256,quotient_cap=20000):
    B=Budget(cap)
    try:
        B.pay('input',n+len(required)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,required,F,B)
        if q is None:return None,B.stats,True
        u,V,H=q;H=simplify(H,B);d=len(V)
        if () in H:return None,B.stats,True
        M,R=transversal(H,B);G=tuple(H[j] for j in R);k=d;history=[]
        while k and G and () not in G:
            for W in blocks(k,G,B):
                B.pay('candidate');q=certificate(k,G,W,B,width,quotient_cap)
                if q is not None:
                    G,r=q;history.append(r);k-=len(W);B.pay('dimensions',len(W));break
            else:break
        x,_=join(k,G,B)
        if x is None:return None,B.stats,True
        for r in reversed(history):x=reopen(r,x,B)
        y=lift(u,V,reopen_core(d,H,M,R,x));assert satisfies(y,required,F)
        return y,B.stats,True
    except (Exhausted,RecursionError):return None,B.stats,False


def portfolio(n,rows,f,cap):
    share=cap//12;F=cnf_flats(f)
    x,_,done=solve(n,rows,F,share)
    if done:
        if x is not None:assert valid(x,n,rows,f)
        return x,True,'correlated-marginal'
    x,done,route,_=signed_portfolio(n,rows,F,share)
    if done:
        if x is not None:assert valid(x,n,rows,f)
        return x,True,'signed-'+route
    return direct_portfolio(n,rows,f,10*share)


def main():
    rng=Random(99);minima=empty_mins=points=certs=opens=fixtures=verified=empty=0
    for n in range(8):
        for _ in range(45):
            M={():rng.randrange(-8,9)}
            for j in range(rng.randrange(9)):
                G=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))
                if G is not None:M[G]=M.get(G,0)+rng.randrange(-8,9)
            H=tuple(G for j in range(rng.randrange(4)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            vals=[point(M,x) for x in range(1<<n) if satisfies(x,(),H)]
            z=correlated(n,M,H,Budget(1000000),False);assert z==min(vals,default=None);minima+=1;empty_mins+=z is None
            a=correlated(n,M,H,Budget(1000000));assert (z is None or a is not None and a<=z)
            if n:
                F=tuple(G for j in range(rng.randrange(9)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+1)))) is not None)
                V=tuple(1<<i for i in rng.sample(range(n),rng.randrange(1,n+1)))
                q=certificate(n,F,V,Budget(1000000))
                if q is not None:
                    G,r=q;U=r[0];certs+=1
                    for y in range(1<<len(U)):
                        truth=any(satisfies(lift(lift(0,U,y),V,t),(),F) for t in range(1<<len(V)))
                        assert truth==satisfies(y,(),G);points+=1
                        if truth:assert satisfies(reopen(r,y,Budget(1000000)),(),F);opens+=1
            P=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for j in range(rng.randrange(8))]
            F=cnf_flats(f);truth=[x for x in range(1<<n) if satisfies(x,P,F)]
            x,done,_=portfolio(n,P,f,1200000);assert done and (x is not None)==bool(truth)
            if x is not None:assert x in truth;verified+=1
            else:empty+=1
            fixtures+=1
    # Two differently oriented half-fibres on complementary quotient domains.
    F=tuple(canon(G) for G in (((1,0),(2,0)),((1,1),(4,0))))
    B=Budget(100000);assert old_certificate(3,F,(2,4),B) is None
    q=certificate(3,F,(2,4),B);assert q is not None and q[1][-2:]==(2,0)
    for y in (0,1):assert satisfies(reopen(q[1],y,B),(),F)
    # Unaffected hard domain makes formerly nonuniform fibre escape exact.
    F=tuple(canon(G) for G in (((1,0),),((1,0),(2,0)),((1,0),(2,1))))
    q=certificate(2,F,(2,),Budget(10000));assert q is not None and q[0]==(((1,0),),)
    assert satisfies(reopen(q[1],1,Budget(1000)),(),F)
    # 2d mutually disjoint t slots; one of each complementary pair active.
    for d in (4,8,16,32,64,128):
        k=(2*d-1).bit_length();V=tuple(1<<(d+i) for i in range(k))
        F=tuple(canon(((1<<j,b),)+tuple((v,(2*j+b)>>i&1) for i,v in enumerate(V))) for j in range(d) for b in (0,1))
        B=Budget(10000000);q=certificate(d+k,F,V,B)
        assert q is not None and 0<q[1][-2]<=d and q[1][-1]==0 and B.stats['correlation_admission']==1
        assert correlated(d,marginal(q[1][3],d,k,B),(),B,False)==d
        for y in (0,(1<<d)-1,((1<<d)-1)//3):assert satisfies(reopen(q[1],y,B),(),F)
        print('conditional_slots',d,k,'lower',q[1][-2],'promotions',q[1][-1],'charged',sum(B.stats.values()))
    # Connected cycle: all event activations jointly impossible, no component split.
    for d in (8,16,32):
        k=(d-1).bit_length();V=tuple(1<<(d+i) for i in range(k))
        F=tuple(canon((((1<<j)^(1<<((j+1)%d)),int(j==d-1)),)+tuple((v,j>>i&1) for i,v in enumerate(V))) for j in range(d))
        B=Budget(10000000);q=certificate(d+k,F,V,B,quotient_cap=2000000)
        assert q is not None and q[1][-2:]==(1,0) and B.stats['correlation_admission']==1
        M=marginal(q[1][3],d,k,B);assert lower(M)==0
        assert correlated(d,M,(),B,False)==1
        for y in (0,(1<<d)-1,((1<<d)-1)//3):assert satisfies(reopen(q[1],y,B),(),F)
        print('connected_cycle',d,'lower',q[1][-2],'charged',sum(B.stats.values()))
    # Nonpositive true minimum, incompatible overlapping orientations, and cap.
    assert certificate(2,(((1,0),),((3,0),)),(1,),Budget(10000)) is None
    assert solve(3,(),(),0)[2] is False
    assert attempt(1,{():0,((1,0),):-1},(),Budget(20),0)==(-1,False)
    print(dict(minima=minima,empty_minima=empty_mins,fixtures=fixtures,verified=verified,empty=empty,certificates=certs,points=points,reopens=opens,large=6,connected=3,controls='PASS'))

if __name__=='__main__':main()
