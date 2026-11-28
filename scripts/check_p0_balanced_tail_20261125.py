"""Section 65: bounded balanced recursion with Boolean-first affine seed reopening."""
from itertools import product
from random import Random
from collections import Counter
from check_p0_component_tail_20261125 import components, chart, quotient_local, valid
from check_p0_separator_tail_20261125 import condition
from check_p0_signed_contrast_20261125 import canon, accepts, matrix, add
from check_p0_seed_action_20261125 import hashval, represent, scale
from check_p0_endpoint_frontier_20261125 import decode_singleton


def seed_lift(C,x):
    X,S,F,R=C;w=len(S)
    if not accepts(F,x):return None
    target=tuple((-c-sum(v*x[i] for i,v in a.items()))%3 for c,a,b,m in R)
    B={}
    for j in range(w):
        v=tuple((b.get(j,0)+sum(z*x[i] for (i,l),z in m.items() if l==j))%3 for c,a,b,m in R)
        e=tuple(int(i==j) for i in range(w))
        for i,(u,h) in sorted(B.items()):f=v[i];v=add(v,u,-f);e=add(e,h,-f)
        if any(v):
            i=next(i for i,z in enumerate(v) if z);B[i]=(scale(v,v[i]),scale(e,v[i]))
    t=(0,)*w
    for i,(u,h) in sorted(B.items()):f=target[i];target=add(target,u,-f);t=add(t,h,f)
    if any(target):return None
    F,n,A,b=chart(C,t);assert valid(F,A,b,x)
    return t


def size(C):return len(C[0])+len(C[1])


def solve(C,bit_cap,rank_cap,budget,stats,depth=0):
    X,S,F,R=C;m=size(C);assert m>0
    stats['nodes']+=1;stats['weight']+=m**4;stats['depth']=max(stats['depth'],depth)
    if len(X)<=bit_cap:
        for x in product(range(2),repeat=len(X)):
            stats['boolean_trials']+=1;t=seed_lift(C,x)
            if t is not None:return dict(zip(X,x)),dict(zip(S,t))
        return None
    piv,_=quotient_local(C)
    if len(piv)<=rank_cap:
        for q in product(range(3),repeat=len(piv)):
            stats['chart_calls']+=1;t=represent(q,piv,len(S));g,n,A,b=chart(C,t)
            x,_=decode_singleton(g,n,A,b,budget)
            if x is not None and valid(g,A,b,x):return dict(zip(X,x)),dict(zip(S,t))
        # A failed budgeted singleton call is not a proof of emptiness.
    best=None
    for kind,labels,dom in [('x',X,2),('s',S,3)]:
        for i in range(len(labels)):
            fs=[]
            for d in range(dom):
                stats['cut_substitutions']+=1
                fs.append(condition(C,{i:d} if kind=='x' else {},{i:d} if kind=='s' else {}))
            largest=max((size(D) for cs in fs if cs is not None for D in cs),default=0)
            if 3*largest>2*m:continue
            key=(largest,kind,i)
            if best is None or key<best[0]:best=(key,fs)
    if best is None:stats['stalls']+=1;return None
    (_,kind,i),fs=best
    assert 9*sum(size(D)**4 for cs in fs if cs is not None for D in cs)<=8*m**4
    for d,cs in enumerate(fs):
        stats['branches']+=1
        if cs is None:stats['failed_branches']+=1;continue
        x={};t={}
        for D in cs:
            out=solve(D,bit_cap,rank_cap,budget,stats,depth+1)
            if out is None:break
            a,b=out;x.update(a);t.update(b)
        else:
            if kind=='x':x[X[i]]=d
            else:t[S[i]]=d
            return x,t
        stats['failed_branches']+=1
    return None


def decode(F,n,k,p,bit_cap,rank_cap,budget):
    stats=Counter();z=components(F,n,k,p)
    if z is None:return None,stats
    P,Cs=z;x=dict(P);t={};bound=9*sum(size(C)**4 for C in Cs)
    for C in Cs:
        out=solve(C,bit_cap,rank_cap,budget,stats)
        if out is None:
            assert stats['weight']<=bound;return None,stats
        a,b=out;x.update(a);t.update(b)
    assert stats['weight']<=bound
    x=tuple(x[i] for i in range(n));s=p+tuple(t[j] for j in range(n+2*k-1-len(p)))
    assert accepts(F,x) and not any(hashval(n,k,s,x))
    return (x,s),stats


def chain(k):
    F=[(1,-(k+1))]
    for i in range(1,k):F.extend(((i,i+1,-(k+i+1)),(-i,-(i+1),k+i+1)))
    p=[0]*(3*k-1);p[2*k-1]=p[k-1]=1
    return canon(F),tuple(p)


def main():
    rng=Random(650);lifts=0;positive=0;solved=0;allstats=Counter();misses=0;wide_solved=0
    for n in range(1,5):
        for _ in range(16):
            F=canon(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(6)))
            k=rng.randrange(1,4);L=n+2*k-1;w=rng.randrange(1,min(L,3)+1);p=tuple(rng.randrange(3) for _ in range(L-w));z=components(F,n,k,p)
            H=[sum(accepts(F,x) and not any(hashval(n,k,p+t,x)) for x in product(range(2),repeat=n)) for t in product(range(3),repeat=w)]
            if z is None:assert not any(H);continue
            for C in z[1]:
                for x in product(range(2),repeat=len(C[0])):
                    t=seed_lift(C,x);ref=any(valid(g,A,b,x) for g,d,A,b in (chart(C,s) for s in product(range(3),repeat=len(C[1]))))
                    assert (t is not None)==ref;lifts+=1
            out,stats=decode(F,n,k,p,2,1,128);allstats.update(stats)
            if sum(h*(2-h) for h in H)>0:
                positive+=1;solved+=out is not None;misses+=out is None
                wide,_=decode(F,n,k,p,4,1,128);assert wide is not None;wide_solved+=1
            if out is not None:assert any(H)
    controls=[]
    for k in (4,8,16,32,64):
        F,p=chain(k);assert matrix(2*k,k,p)==[[int(j in (i,i+k)) for j in range(2*k)] for i in range(k)]
        P,Cs=components(F,2*k,k,p);assert not P and len(Cs)==1 and len(quotient_local(Cs[0])[0])==k
        if k<=4:
            for t in product(range(3),repeat=k):
                assert sum(accepts(F,x) and not any(hashval(2*k,k,p+t,x)) for x in product(range(2),repeat=2*k))==1
        out,stats=decode(F,2*k,k,p,2,0,0);assert out is not None and stats['chart_calls']==0
        controls.append((k,dict(stats)))
    # One Boolean, many independent seed equations: no ternary enumeration.
    w=80;C=([0],list(range(w)),(),[(1,{}, {j:1},{(0,j):1}) for j in range(w)])
    assert len(quotient_local(C)[0])==w
    for b in (0,1):assert seed_lift(C,(b,))==((2 if b==0 else 1),)*w
    # A central Boolean cut forced by an affine row, not CNF preprocessing.
    C=(list(range(9)),[],canon((1,i) for i in range(2,10)),[(2,{0:1},{},{})])
    st=Counter();ans=solve(C,1,0,0,st);assert ans is not None and ans[0][0]==1 and st['failed_branches']==1
    print(dict(fixtures=64,affine_lift_checks=lifts,positive=positive,solved=solved,misses=misses,wide_solved=wide_solved,work=dict(allstats),controls=controls,high_seed_rank=w,failed_branch_control=dict(st)))
if __name__=='__main__':main()
