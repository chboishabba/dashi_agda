"""Adaptive masked-forest lower certificates and collective witness reopening."""
from itertools import combinations
from random import Random
from check_pnp_affine_normal_components import (canon, restrict, lift, simplify,
    satisfies, cnf_flats, Budget, Exhausted)
from check_pnp_normal_transversal import transversal, reopen_core
from check_pnp_collective_fibre_escape import (coordinates, domain, fibre, size,
    dot, blocks, certificate as forest_certificate, solve as previous)
from check_pnp_normal_boundary_join import join


def add(Q,A,w):
    if A is None or not w:return
    v=Q.get(A,0)+w
    if v:Q[A]=v
    else:Q.pop(A,None)


def intersect(Q,A,w,B,T):
    for C,c in Q.items():
        B.pay('intersection');add(T,canon(C+A),w*c)


def forest(E,n,B):
    pairs=[]
    for i,j in combinations(range(len(E)),2):
        B.pay('pair');A=canon(E[i]+E[j])
        if A is not None:pairs.append((1<<(n-len(A)),i,j,A))
    par=list(range(len(E)));T=[]
    def root(i):
        while par[i]!=i:i=par[i]
        return i
    for w,i,j,A in sorted(pairs,reverse=True):
        B.pay('forest');u,v=root(i),root(j)
        if u!=v:par[u]=v;T.append((i,j,A))
    return T


def masked(Q,E,R,T,B):
    L=dict(Q)
    for i in R:intersect(Q,E[i],-1,B,L)
    for i,j,A in T:
        if i in R and j in R:intersect(Q,A,1,B,L)
    return L


def marginal(L,d,k,B):
    M={}
    for A,w in L.items():
        B.pay('marginal');P=domain(A,d);add(M,P,w*(1<<(k-len(A)+len(P))))
    return M


def lower(M):
    # Identical domain terms have already cancelled. Optional positive terms
    # may vanish; optional negative terms may be active. Constant kept exactly.
    return M.get((),0)+sum(w for P,w in M.items() if P and w<0)


def certificate(n,F,V,B,width=256,envelope=None,admissible_envelope=None):
    k=len(V);assert k;U=coordinates(n,V);d=len(U);H=set();E=[]
    B.pay('chart',n+1)
    for G in F:
        B.pay('scan',1+len(G));A=canon((sum(dot(a,v)<<i for i,v in enumerate(U+list(V))),b) for a,b in G)
        if A is None:continue
        P=domain(A,d)
        if len(A)==len(P):H.add(P)
        else:E.append(A)
    T=forest(E,n,B);R=set(range(len(E)));Q={():1};stages=0
    # Large forbidden events and strongly overlapping events first.
    order=sorted(R,key=lambda i:(len(E[i]),-sum(i in (a,b) for a,b,_ in T),i))
    while True:
        B.pay('checkpoint');L=masked(Q,E,R,T,B);M=marginal(L,d,k,B);a=lower(M)
        if a<=0 and envelope is not None:a=max(a,envelope(M,d,B))
        if a<=0 and admissible_envelope is not None:a=max(a,admissible_envelope(M,d,tuple(sorted(H)),B))
        if a>0:return tuple(sorted(H)),(tuple(U),tuple(V),tuple(E),L,a,stages)
        if not R:return None
        i=order[stages];P=dict(Q);intersect(Q,E[i],-1,B,P)
        if len(P)>width:return None
        Q=P;R.remove(i);stages+=1;B.pay('promoted')


def reopen(receipt,y,B):
    U,V,E,L,a,stages=receipt;d=len(U);k=len(V);Q={}
    for A,w in L.items():
        B.pay('specialize');add(Q,fibre(A,d,y),w)
    def mass(P):
        B.pay('mass',1+len(Q));return sum(w*size(A,k,P) for A,w in Q.items())
    P=();z=0;c=mass(P);assert c>=a>0
    for i in range(k):
        P0=P+((1<<i,0),);q=mass(P0)
        if q>0:P=P0;c=q
        else:P+=((1<<i,1),);z|=1<<i;c-=q
        assert c>0
    assert c==1 and all(fibre(A,d,y) is None or satisfies(z,(),(fibre(A,d,y),)) for A in E)
    return lift(lift(0,U,y),V,z)


def adaptive(n,required,F,cap,width=256,envelope=None,admissible_envelope=None,budget=None):
    B=Budget(cap) if budget is None else budget
    try:
        B.pay('input',n+len(required)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,required,F,B)
        if q is None:return None,B.stats,True
        u,V,H=q;H=simplify(H,B);d=len(V)
        if () in H:return None,B.stats,True
        M,R=transversal(H,B);G=tuple(H[j] for j in R);k=d;history=[]
        while k and G and () not in G:
            for W in blocks(k,G,B):
                B.pay('candidate');q=certificate(k,G,W,B,width,envelope,admissible_envelope)
                if q is not None:
                    G,r=q;history.append(r);k-=len(W);B.pay('dimensions',len(W));break
            else:break
        x,_=join(k,G,B)
        if x is None:return None,B.stats,True
        for r in reversed(history):x=reopen(r,x,B)
        y=lift(u,V,reopen_core(d,H,M,R,x));assert satisfies(y,required,F)
        return y,B.stats,True
    except (Exhausted,RecursionError):return None,B.stats,False


def portfolio(n,required,F,cap,width=256,envelope=None,admissible_envelope=None):
    x,s,done=adaptive(n,required,F,cap//2,width,envelope,admissible_envelope)
    if done:return x,done,'adaptive',s
    try:y,t,done=previous(n,required,F,cap-cap//2)
    except RecursionError:return None,False,'unknown',s
    s.update(t)
    if y is not None:assert satisfies(y,required,F)
    return y,done,'previous' if done else 'unknown',s


def point(Q,x):return sum(w for A,w in Q.items() if all(dot(a,x)==b for a,b in A))


def main():
    rng=Random(369);fixtures=verified=empty=points=monotone=certs=reopens=0
    for n in range(1,8):
        for _ in range(30):
            F=tuple(G for _ in range(rng.randrange(8)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+1)))) is not None)
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(8))]
            P=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            for H in (F,cnf_flats(f)):
                B=Budget(1000000);T=forest(H,n,B);R=set(range(len(H)));Q={():1};old=None
                for i in range(len(H)+1):
                    L=masked(Q,H,R,T,B);vals=[point(L,x) for x in range(1<<n)]
                    assert all(v<=int(satisfies(x,(),H)) for x,v in enumerate(vals));points+=len(vals)
                    if old is not None:assert all(a<=b for a,b in zip(old,vals));monotone+=len(vals)
                    old=vals
                    if i<len(H):Z=dict(Q);intersect(Q,H[i],-1,B,Z);Q=Z;R.remove(i)
                assert vals==[int(satisfies(x,(),H)) for x in range(1<<n)]
                k=rng.randrange(1,n+1);V=[];S=()
                while len(V)<k:
                    v=rng.randrange(1,1<<n);A=canon(S+((v,0),))
                    if len(A)>len(S):V.append(v);S=A
                q=certificate(n,H,V,B)
                if q is not None:
                    G,r=q;U=r[0];certs+=1
                    for y in range(1<<len(U)):
                        truth=any(satisfies(lift(lift(0,U,y),V,t),(),H) for t in range(1<<k))
                        assert truth==satisfies(y,(),G)
                        if truth:assert satisfies(reopen(r,y,B),(),H);reopens+=1
                truth=[x for x in range(1<<n) if satisfies(x,P,H)]
                x,done,route,s=portfolio(n,P,H,2000000);assert done and (x is not None)==bool(truth)
                if x is not None:assert x in truth;verified+=1
                else:empty+=1
                fixtures+=1
    # Forest failure even though an admissible witness exists; early stop strictly before full contraction.
    r=Random(83);n=6;V=tuple(1<<i for i in range(n))
    for trial in range(2000):
        H=set()
        while len(H)<10:
            A=canon((r.randrange(1,1<<n),r.randrange(2)) for _ in range(2))
            if A is not None and len(A)==2:H.add(A)
        H=tuple(sorted(H));B=Budget(1000000)
        if simplify(H,B)!=H or len(transversal(H,B)[1])!=len(H) or forest_certificate(n,H,V,B) is not None:continue
        q=certificate(n,H,V,B)
        if q is not None and 0<q[1][-1]<len(H):break
    else:raise AssertionError('no early stop control')
    assert satisfies(reopen(q[1],0,B),(),H)
    print('forest_failure',trial,'events',len(H),'promoted',q[1][-1],'lower',q[1][-2],'chart',len(q[1][3]))
    # Transport the same actual deficient core into dense normals and free dimensions.
    for n2 in (16,32,64,128):
        A=[((1<<n2)-1)^(1<<i) for i in range(n2)]
        G=tuple(canon((lift(0,A[:n],a),b) for a,b in C) for C in H)
        W=tuple(1<<i for i in range(n2));B=Budget(1000000)
        assert forest_certificate(n2,G,W,B) is None
        q=certificate(n2,G,W,B);assert q is not None and 0<q[1][-1]<len(G)
        x,done,route,s=portfolio(n2,(),G,2000000);assert done and x is not None and satisfies(x,(),G)
        print('dense',n2,'promoted',q[1][-1],'lower_fraction',q[1][-2]//(1<<(n2-n)),'route',route,'charged',sum(s.values()))
    # Quotient-dependent overlap cannot certify a covered fibre.
    assert certificate(2,(((1,0),),((3,0),)),(1,),Budget(1000)) is None
    assert portfolio(3,(),(),0)[1] is False
    # Conditional block: every retained bit translates the same hard fibre.
    G=tuple(canon((a|(dot(a,13)<<6),b) for a,b in C) for C in H)
    B=Budget(1000000);assert forest_certificate(7,G,V,B) is None
    q=certificate(7,G,V,B);assert q is not None and 0<q[1][-1]<len(G)
    for y in (0,1):assert satisfies(reopen(q[1],y,B),(),G)
    # Force actual previous route through independent allocated caps.
    r=Random(16);G=set()
    while len(G)<20:
        A=canon((r.getrandbits(16),r.randrange(2)) for _ in range(6))
        if A is not None and len(A)==6:G.add(A)
    G=tuple(sorted(G));x,done,route,s=portfolio(16,(),G,4000)
    assert done and route=='previous' and x is not None and satisfies(x,(),G)
    print('fallback_control',route,'charged',sum(s.values()))
    print(dict(fixtures=fixtures,verified=verified,empty=empty,pointwise=points,monotone=monotone,certificates=certs,reopens=reopens,controls='PASS'))

if __name__=='__main__':main()
