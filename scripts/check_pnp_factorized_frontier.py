"""K/time indexed gain intervals: connected Walsh frontier and conditioned seams."""
from random import Random
from check_pnp_affine_normal_components import (canon, chart, lift, split, reopen,
    satisfies, Budget, Exhausted)
from check_pnp_normal_boundary_join import tree, value, rows
from check_pnp_signed_quotient_minimum import minimum
from check_pnp_signed_moment_filter import direction
from check_pnp_indexed_gain_transport import evaluate, transport, advance, source_chart


def ritz(n,M,threshold,B,limit=32):
    """Strict attained gain > threshold, or no certificate (not absence)."""
    if limit<1:return None
    h={0:sum(M.values())-2*threshold}
    h.update({s:-w for ((s,b),),w in M.items()})
    assert all(b==1 and s for ((s,b),) in M)
    T=[0];S=set(T);support=sorted(s for s,w in h.items() if s and w)
    while True:
        B.pay('ritz_matrix',len(T)**2)
        a=direction([[h.get(u^v,0) for v in T] for u in T],B)
        if a is not None:break
        if len(T)>=limit:return None
        B.pay('ritz_frontier',len(T)*len(support))
        F=sorted({u^s for u in T for s in support}-S)
        if not F:return None
        # Prefer strongest incident coupling; no claim of optimal dictionary.
        B.pay('ritz_order',len(F)*len(T))
        F.sort(key=lambda v:(-sum(abs(h.get(u^v,0)) for u in T),v))
        T.extend(F[:limit-len(T)]);S=set(T)
    # Sparse character convolution for 2(G-threshold)*p^2.
    C={}
    for u,p in zip(T,a):
        for v,q in zip(T,a):
            B.pay('ritz_square');C[u^v]=C.get(u^v,0)+p*q
    E={}
    for u,p in C.items():
        if not p:continue
        for v,q in h.items():
            B.pay('ritz_energy');E[u^v]=E.get(u^v,0)+p*q
    c=E.get(0,0)*(1<<n);assert c>0
    x=0;mask=0
    for i in range(n):
        mask|=1<<i;B.pay('ritz_pin',len(E))
        q=sum(w*(-1 if (s&x).bit_count()%2 else 1) for s,w in E.items() if s&~mask==0)*(1<<(n-i-1))
        if q>0:c=q
        else:x|=1<<i;c-=q
        assert c>0
    assert evaluate(M,x)>threshold
    return x


def factor(n,M,B,width=4,limit=32):
    """Attained lower gain L and sound upper U; never infer from relaxed L."""
    if not M:return 0,0,0
    basis,parts=split(n,tuple(sorted(M)),B);z=low=upper=0
    for I,F in parts:
        normals=[basis[i] for i in I]
        N={A:M[((lift(0,normals,A[0][0]),1),)] for A in F}
        d=len(I);B.pay('component_interval',len(N))
        a,exact,y=minimum({A:-w for A,w in N.items()},d,B,width,with_witness=True)
        u=-a;assert u>=0
        if not exact:
            y=0;g=0
            for j in range(d):
                B.pay('interval_basis',len(N));q=evaluate(N,1<<j)
                if q>g:y=1<<j;g=q
            if g<u:
                v=ritz(d,N,g,B,limit)
                if v is not None:y=v
        l=evaluate(N,y);assert 0<=l<=u
        # Exact parity lattice: xor of all normals with odd coefficient.
        parity=0
        for ((s,b),),w in N.items():
            if w&1:parity^=s
        if not parity:u-=u%2
        assert l<=u
        z|=sum(((y>>j)&1)<<i for j,i in enumerate(I));low+=l;upper+=u
    y=reopen(n,basis,z);assert evaluate(M,y)==low
    return y,low,upper


def seam(n,M,B,width=4,limit=32,cut_width=2):
    """All labels on one retained shared normal separator, then local factors."""
    if not M or cut_width<1:return factor(n,M,B,width,limit)
    root,boundary,_=tree(n,tuple(sorted(M)),B)
    if root[1] is None:return factor(n,M,B,width,limit)
    D=boundary(root[1][0])[:cut_width]
    if not D:return factor(n,M,B,width,limit)
    y=0;low=0;upper=None
    for q in range(1<<len(D)):
        B.pay('seam_label');a,V=chart(n,canon(rows(D,q)))
        B.pay('seam_transport',len(M)*(1+len(V)))
        h,N=transport(M,V,a);z,l,u=factor(len(V),N,B,width,limit)
        v=lift(a,V,z);assert value(D,v)==q and evaluate(M,v)==h+l
        if h+l>low:y=v;low=h+l
        upper=h+u if upper is None else max(upper,h+u)
    assert 0<=low<=upper and evaluate(M,y)==low
    return y,low,upper


def indexed_descent(n,P,x,target,B,width=4,limit=32,cut_width=2,history=None,k=0):
    """Fixed original chart, advancing incumbent time and certified gain ceiling."""
    assert satisfies(x,P,()) and x.bit_count()>=target
    _,V=chart(n,P);B.pay('indexed_chart',n*(1+len(V)))
    M=source_chart(n,x,V);U=sum(max(0,w) for w in M.values());t=0
    while x.bit_count()>target:
        r=x.bit_count()-target
        if U<r:return None,True
        y,l,u=factor(len(V),M,B,width,limit);U=min(U,u)
        if U<r:return None,True
        if l<=0:
            y,l,u=seam(len(V),M,B,width,limit,cut_width);U=min(U,u)
        if U<r:return None,True
        if l<=0:return None,False
        B.pay('indexed_advance',n+len(M));g,N=advance(M,y);v=lift(x,V,y)
        assert g==l>0 and v.bit_count()==x.bit_count()-g and satisfies(v,P,())
        if history is not None:history.append((k,t,x,y,g,r,U,B.left))
        x=v;M=N;U-=g;t+=1
    assert x.bit_count()==target
    return x,True


def main():
    rng=Random(369);ritz_checks=intervals=seams=improvements=fixtures=verified=empty=unknown=0
    for n in range(7):
        for _ in range(35):
            M={((s,1),):w for s in range(1,1<<n) if rng.randrange(4)==0 and (w:=rng.randrange(-5,6))}
            truth=max(evaluate(M,x) for x in range(1<<n));B=Budget(10000000)
            for threshold in (0,max(0,truth-1),truth):
                y=ritz(n,M,threshold,B,1<<n)
                assert (y is not None)==(truth>threshold)
                if y is not None:assert evaluate(M,y)>threshold
                ritz_checks+=1
            for f in (factor,seam):
                y,l,u=f(n,M,B,width=0,limit=8)
                assert evaluate(M,y)==l<=truth<=u
                if f==seam:seams+=1
                else:intervals+=1
    # Shared normal seam: full factor stalls with width zero and one-frequency cap.
    M={((1,1),):3,((2,1),):2,((5,1),):1,((6,1),):-3,((7,1),):-5}
    y,l,u=factor(3,M,Budget(10000),0,1);assert l==0 and u==6
    y,l,u=seam(3,M,Budget(10000),0,1);assert l==u==3 and y==6
    # Original X3C parity carrier; test the actual indexed entry independently of preprocessing.
    for m in (3,6,9):
        for _ in range(60):
            n=rng.randrange(1,12);S=[rng.sample(range(m),3) for i in range(n)]
            R=[sum(1<<j for j,s in enumerate(S) if i in s) for i in range(m)]
            truth=[x for x in range(1<<n) if all((x&a).bit_count()==1 for a in R)]
            P=canon((a,1) for a in R);fixtures+=1
            if P is None:assert not truth;empty+=1;continue
            x,V=chart(n,P);H=[]
            y,done=indexed_descent(n,P,x,m//3,Budget(10000000),n,8,2,H)
            if y is not None:assert done and y in truth;verified+=1
            elif done:assert not truth;empty+=1
            else:unknown+=1
            for j,(k,t,x,a,g,r,U,left) in enumerate(H):
                assert k==0 and t==j and g>=2 and g%2==0 and r>=g and U>=g
                if j:assert left<H[j-1][-1] and r==H[j-1][5]-H[j-1][4]
                improvements+=1
    print(dict(ritz=ritz_checks,intervals=intervals,seams=seams,fixtures=fixtures,verified=verified,empty=empty,unknown=unknown,improvements=improvements,controls='PASS'))

if __name__=='__main__':main()
