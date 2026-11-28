"""Condition original mixed factors, then reuse Section 63 local chart decoder."""
from fractions import Fraction as Q
from itertools import product
from math import prod
from random import Random
from check_p0_component_tail_20261125 import components, chart, quotient_local, valid, local_counts
from check_p0_signed_contrast_20261125 import canon, restrict, accepts, matrix
from check_p0_seed_action_20261125 import hashval, represent, project
from check_p0_endpoint_frontier_20261125 import decode_singleton


def condition(C, xp, sp):
    X,S,F,R=C
    # Pins are LOCAL coordinates of this input component; all output labels are original.
    for i,b in xp.items():F=restrict(F,i,b)
    if () in F:return None
    nodes=[('x',i) for i in range(len(X)) if i not in xp]+[('s',j) for j in range(len(S)) if j not in sp]
    parent={v:v for v in nodes}
    def root(a):
        while a!=parent[a]:a=parent[a]
        return a
    def join(vs):
        for v in vs[1:]:parent[root(v)]=root(vs[0])
    rows=[]
    for c,a,b,m in R:
        A={};B={};M={}
        for i,v in a.items():
            if i in xp:c+=v*xp[i]
            else:A[i]=v
        for j,v in b.items():
            if j in sp:c+=v*sp[j]
            else:B[j]=v
        for (i,j),v in m.items():
            if i in xp and j in sp:c+=v*xp[i]*sp[j]
            elif i in xp:B[j]=(B.get(j,0)+v*xp[i])%3
            elif j in sp:A[i]=(A.get(i,0)+v*sp[j])%3
            else:M[i,j]=v
        A={i:v for i,v in A.items() if v};B={j:v for j,v in B.items() if v}
        vs=sorted({('x',i) for i in A}|{('s',j) for j in B}|{('x',i) for i,j in M}|{('s',j) for i,j in M})
        if not vs:
            if c%3:return None
        else:join(vs);rows.append((vs,(c%3,A,B,M)))
    for cl in F:join([('x',abs(l)-1) for l in cl])
    ds={}
    for v in nodes:ds.setdefault(root(v),[[],[],[],[]])[v[0]=='s'].append(v[1])
    for cl in F:ds[root(('x',abs(cl[0])-1))][2].append(cl)
    for vs,r in rows:ds[root(vs[0])][3].append(r)
    out=[]
    for I,J,G,T in ds.values():
        ii={v:i for i,v in enumerate(I)};jj={v:j for j,v in enumerate(J)}
        g=canon(tuple((ii[abs(l)-1]+1)*(1 if l>0 else -1) for l in cl) for cl in G)
        t=[(c,{ii[i]:v for i,v in a.items()},{jj[j]:v for j,v in b.items()},{(ii[i],jj[j]):v for (i,j),v in m.items()}) for c,a,b,m in T]
        out.append(([X[i] for i in I],[S[j] for j in J],g,t))
    return out


def tail(Cs,cap,budget):
    x={};s={};calls=0
    for C in Cs:
        X,S,_,_=C;piv,_=quotient_local(C)
        if len(piv)>cap:return None
        for q in product(range(3),repeat=len(piv)):
            t=represent(q,piv,len(S));F,n,A,b=chart(C,t);calls+=1
            y,_=decode_singleton(F,n,A,b,budget)
            if y is not None and valid(F,A,b,y):break
        else:return None
        x.update(zip(X,y));s.update(zip(S,t))
    return x,s,calls


def one_cut(C,cap,budget):
    got=tail([C],cap,budget)
    if got is not None:return (*got,0)
    X,S,_,_=C
    # One-variable cut portfolio, deterministic, no occupancy information.
    # Sort by worst residual component size, including both Boolean and trit pins.
    options=[]
    for kind,count,dom in [('x',len(X),2),('s',len(S),3)]:
        for i in range(count):
            fs=[condition(C,{i:d} if kind=='x' else {},{i:d} if kind=='s' else {}) for d in range(dom)]
            size=max((len(D[0])+len(D[1]) for f in fs if f is not None for D in f),default=0)
            options.append((size,kind,i,fs))
    tried=0
    for _,kind,i,fs in sorted(options,key=lambda z:z[:3]):
        for d,cs in enumerate(fs):
            tried+=1
            if cs is None:continue
            got=tail(cs,cap,budget)
            if got is None:continue
            x,s,calls=got
            if kind=='x':x[X[i]]=d
            else:s[S[i]]=d
            return x,s,calls,tried
    return None


def decode(F,n,k,p,cap,budget):
    z=components(F,n,k,p)
    if z is None:return None
    P,Cs=z;x=dict(P);s={};calls=tries=0
    for C in Cs:
        got=one_cut(C,cap,budget)
        if got is None:return None
        a,b,c,t=got;x.update(a);s.update(b);calls+=c;tries+=t
    x=tuple(x[i] for i in range(n));s=p+tuple(s[j] for j in range(n+2*k-1-len(p)))
    assert accepts(F,x) and not any(hashval(n,k,s,x))
    return x,s,calls,tries


def count_components(cs,t):
    if cs is None:return 0
    out=1
    for D in cs:
        F,n,A,b=chart(D,tuple(t[j] for j in D[1]));out*=sum(valid(F,A,b,y) for y in product(range(2),repeat=n))
    return out


def main():
    rng=Random(644);checks=moment=positive=solved=cases=0
    for n in range(1,5):
        for _ in range(12):
            F=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(5)))
            k=rng.randrange(1,4);L=n+2*k-1;w=rng.randrange(1,min(L,3)+1);p=tuple(rng.randrange(3) for _ in range(L-w));z=components(F,n,k,p)
            if z is None:continue
            P,Cs=z
            for C in Cs:
                X,S,G,R=C;cases+=1
                for i in range(len(X)+len(S)):
                    isx=i<len(X);j=i if isx else i-len(X);dom=2 if isx else 3
                    fs=[condition(C,{j:d} if isx else {},{j:d} if not isx else {}) for d in range(dom)]
                    vs=[];sums=[0]*dom
                    for t in product(range(3),repeat=len(S)):
                        g,d,A,b=chart(C,t);h=sum(valid(g,A,b,y) for y in product(range(2),repeat=d));vs.append(h*(2-h));T=dict(zip(S,t))
                        hs=[count_components(f,T) for f in fs] if isx else [count_components(fs[t[j]],T)]
                        assert sum(hs)==h;checks+=1
                        if isx:
                            for a,H in enumerate(hs):sums[a]+=H*(2-H)
                        else:sums[t[j]]+=hs[0]*(2-hs[0])
                    assert sum(sums)>=sum(vs) if isx else sum(sums)==sum(vs);moment+=1
                    if sum(vs)>0:assert max(sums)>0;positive+=1
            H=[sum(accepts(F,x) and not any(hashval(n,k,p+t,x)) for x in product(range(2),repeat=n)) for t in product(range(3),repeat=w)]
            if sum(h*(2-h) for h in H)>0:
                assert decode(F,n,k,p,3,128) is not None;solved+=1
    controls=[]
    for k in (4,16,32,64):
        n=2*k+1;rows=k+1;z=k+1
        F=canon([(z,i+1,-(i+k+2)) for i in range(k)]+[(-z,-(i+1),i+k+2) for i in range(k)])
        p=[0]*(n+rows-1);p[n-1]=p[n-1-rows]=1;p=tuple(p)
        assert matrix(n,rows,p)==[[int(j==i or j==i+rows) for j in range(n)] for i in range(rows)]
        P,Cs=components(F,n,rows,p);assert len(Cs)==1 and not P
        C=Cs[0];assert len(quotient_local(C)[0])==rows
        for v in (0,1):
            ds=condition(C,{C[0].index(z-1):v},{})
            assert len(ds)==rows and all(len(quotient_local(D)[0])==1 for D in ds)
            hs=[local_counts(D)[0] for D in ds];assert sorted(sorted(h.values()) for h in hs)==[[0,0,1]]+[[1,1,1]]*k
        ans=decode(F,n,rows,p,1,32);assert ans is not None
        controls.append((n,rows,ans[2],ans[3]))
    print(dict(conditional_components=cases,occupancy_checks=checks,moment_checks=moment,positive_cut_checks=positive,positive_sources_decoded=solved,connected_controls=controls))
if __name__=='__main__':main()
