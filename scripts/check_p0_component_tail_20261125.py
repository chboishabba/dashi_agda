from itertools import product
from fractions import Fraction as Q
from random import Random
from math import prod
from check_p0_signed_contrast_20261125 import canon, restrict, accepts, matrix, add
from check_p0_seed_action_20261125 import infer, hashval, scale, project, represent
from check_p0_endpoint_frontier_20261125 import decode_singleton

# Original indexed mixed polynomial: constant, Boolean-linear, trit-linear, bilinear.
def components(F,n,k,p):
    P=infer(F,n)
    if P is None:return None
    F=canon(F)
    for i,b in P.items():F=restrict(F,i,b)
    L=n+2*k-1;w=L-len(p);free=[i for i in range(n) if i not in P]
    rows=[];nodes=[('x',i) for i in free]+[('s',j) for j in range(w)]
    parent={v:v for v in nodes}
    def root(a):
        while parent[a]!=a:
            parent[a]=parent[parent[a]];a=parent[a]
        return a
    def join(vs):
        vs=list(vs)
        for v in vs[1:]:parent[root(v)]=root(vs[0])
    def term(t,k):t[k]=(t.get(k,0)+1)%3
    for i in range(k):
        c=0;a={};b={};m={}
        for j in range(n):
            l=n-1+i-j
            if l<len(p):
                if j in P:c+=p[l]*P[j]
                else:a[j]=(a.get(j,0)+p[l])%3
            else:
                if j in P:
                    if P[j]:term(b,l-len(p))
                else:term(m,(j,l-len(p)))
        l=n+k-1+i
        if l<len(p):c+=p[l]
        else:term(b,l-len(p))
        a={j:v for j,v in a.items() if v};b={j:v for j,v in b.items() if v};m={j:v for j,v in m.items() if v}
        vs={('x',j) for j in a}|{('s',j) for j in b}|{('x',j) for j,l in m}|{('s',l) for j,l in m}
        if not vs:
            if c%3:return None
            continue
        join(sorted(vs));rows.append((sorted(vs),(c%3,a,b,m)))
    for clause in F:
        if not clause:return None
        join([('x',abs(l)-1) for l in clause])
    C={}
    for v in nodes:
        d=C.setdefault(root(v),[[],[],[],[]]);d[v[0]=='s'].append(v[1])
    for clause in F:C[root(('x',abs(clause[0])-1))][2].append(clause)
    for vs,row in rows:C[root(vs[0])][3].append(row)
    out=[]
    for X,S,G,R in C.values():
        xi={v:i for i,v in enumerate(X)};si={v:i for i,v in enumerate(S)}
        G=canon(tuple((xi[abs(l)-1]+1)*(1 if l>0 else -1) for l in cl) for cl in G)
        R=[(c,{xi[j]:v for j,v in a.items()},{si[j]:v for j,v in b.items()},{(xi[j],si[l]):v for (j,l),v in m.items()}) for c,a,b,m in R]
        out.append((X,S,G,R))
    return P,out

def chart(C,t):
    X,S,F,R=C;A=[];target=[]
    for c,a,b,m in R:
        row=[a.get(i,0) for i in range(len(X))]
        for (i,j),v in m.items():row[i]=(row[i]+v*t[j])%3
        A.append(row);target.append((-c-sum(v*t[j] for j,v in b.items()))%3)
    return F,len(X),A,tuple(target)

def quotient_local(C):
    X,S,F,R=C;w=len(S);n=len(X)
    cols=[]
    for j in range(w):
        cols.append(tuple(v for c,a,b,m in R for v in (b.get(j,0),*(m.get((i,j),0) for i in range(n)))))
    B={};piv=[];coords=[]
    for j,v in enumerate(cols):
        e=tuple(int(i==j) for i in range(w))
        for i,(u,c) in sorted(B.items()):f=v[i];v=add(v,u,-f);e=add(e,c,-f)
        if any(v):
            i=next(i for i,x in enumerate(v) if x);B[i]=(scale(v,v[i]),scale(e,v[i]));piv.append(j)
    for v in cols:
        c=(0,)*w
        for i,(u,e) in sorted(B.items()):f=v[i];v=add(v,u,-f);c=add(c,e,f)
        assert not any(v);coords.append(tuple(c[i] for i in piv))
    return piv,coords

def valid(F,A,b,x):return accepts(F,x) and tuple(sum(a*z for a,z in zip(r,x))%3 for r in A)==b

def local_counts(C,rank_cap=8,bit_cap=12):
    piv,coords=quotient_local(C);r=len(piv);X,S,F,R=C
    if r>rank_cap or len(X)>bit_cap:return None
    hist={}
    for q in product(range(3),repeat=r):
        t=represent(q,piv,len(S));F,n,A,b=chart(C,t)
        hist[q]=sum(valid(F,A,b,x) for x in product(range(2),repeat=n))
    return hist,piv,coords

def component_decode(F,n,k,p,rank_cap,budget):
    data=components(F,n,k,p)
    if data is None:return None
    P,Cs=data;x=[P.get(i,0) for i in range(n)];t=[0]*(n+2*k-1-len(p));stats=[]
    for C in Cs:
        X,S,G,R=C;piv,coords=quotient_local(C);r=len(piv)
        if r>rank_cap:return None
        tested=0;found=None
        for q in product(range(3),repeat=r):
            s=represent(q,piv,len(S));g,d,A,b=chart(C,s);tested+=1
            y,_=decode_singleton(g,d,A,b,budget)
            if y is not None and valid(g,A,b,y):found=(s,y);break
        if found is None:return None
        s,y=found
        for i,v in zip(X,y):x[i]=v
        for j,v in zip(S,s):t[j]=v
        stats.append((r,tested))
    x=tuple(x);s=tuple(p)+tuple(t)
    if not accepts(F,x) or any(hashval(n,k,s,x)):return None
    return x,s,stats

def main():
    rng=Random(633);cases=0;rejects=0;seed_checks=0;local_checks=0;positive=0;decoded=0;inert=0;moment_checks=0;maxcomp=0;multi=0
    for n in range(1,5):
        for _ in range(20):
            F=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(6)))
            k=rng.randrange(1,4);L=n+2*k-1;w=rng.randrange(1,min(L,4)+1);p=tuple(rng.randrange(3) for _ in range(L-w));S=[x for x in product(range(2),repeat=n) if accepts(F,x)]
            data=components(F,n,k,p)
            ref={t:sum(not any(hashval(n,k,p+t,x)) for x in S) for t in product(range(3),repeat=w)}
            if data is None:assert not any(ref.values());rejects+=1;continue
            P,Cs=data;cases+=1;multi+=len(Cs)>1;maxcomp=max(maxcomp,len(Cs));records=[local_counts(C) for C in Cs];assert all(v is not None for v in records)
            for C,(H,piv,coords) in zip(Cs,records):
                X,T,G,R=C;inert+=len(T)-len(piv)
                for s in product(range(3),repeat=len(T)):
                    g,d,A,b=chart(C,s);q=project(s,coords,len(piv));assert H[q]==sum(valid(g,A,b,x) for x in product(range(2),repeat=d));local_checks+=1
            for t,H in ref.items():
                z=prod(h[project(tuple(t[j] for j in C[1]),co,len(pi))] for C,(h,pi,co) in zip(Cs,records));assert z==H;seed_checks+=1
            mus=[Q(sum(h.values()),len(h)) for h,_,_ in records];ms=[Q(sum(x*x for x in h.values()),len(h)) for h,_,_ in records];V=2*prod(mus)-prod(ms)
            assert prod(mus)==Q(sum(ref.values()),len(ref));assert prod(ms)==Q(sum(h*h for h in ref.values()),len(ref));assert V==Q(sum(h*(2-h) for h in ref.values()),len(ref));moment_checks+=3
            if V>0:
                positive+=1
                assert all(2*a-b>=V for a,b in zip(mus,ms))
                assert all(0<sum(h.values())<2*len(h) for h,_,_ in records)
                got=component_decode(F,n,k,p,4,256);assert got is not None;decoded+=1
    dense=[]
    for k in (4,16,32,64):
        n=2*k;F=canon(((i+1,-(i+k+1)) for i in range(k)))
        p=[0]*(n+k-1);p[n-1]=1;p[n-1-k]=1;p=tuple(p)
        assert matrix(n,k,p)==[[int(j==i or j==i+k) for j in range(n)] for i in range(k)]
        P,Cs=components(F,n,k,p);assert len(Cs)==k and not P
        for C in Cs:
            H,pi,co=local_counts(C);assert len(pi)==1 and set(H.values())=={1}
        x,s,stats=component_decode(F,n,k,p,1,16);assert len(stats)==k;assert all(r==1 for r,_ in stats)
        dense.append(dict(n=n,global_rank=k,components=len(Cs),local_rank=1,charts_tested=sum(t for _,t in stats),global_charts=3**k))
    print(dict(fixtures=80,component_cases=cases,rejected=rejects,multi_component_cases=multi,max_components=maxcomp,global_seed_checks=seed_checks,local_quotient_checks=local_checks,moment_checks=moment_checks,removed_local_seed_dimensions=inert,positive_cases=positive,verified_witnesses=decoded,dense=dense))
if __name__=='__main__':main()
