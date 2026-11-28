"""Exact affine-direction existential projection; bounded witness reopening."""
from itertools import combinations
from random import Random
from collections import Counter
from check_pnp_affine_normal_components import (canon, chart, lift, restrict,
    simplify, satisfies, cnf_flats, Budget, Exhausted)
from check_pnp_normal_boundary_join import join
from check_pnp_normal_transversal import transversal, reopen_core


def dot(a,x): return (a&x).bit_count()%2


def delete(x,p):
    return (x&((1<<p)-1))|((x>>(p+1))<<p)


def insert(y,p):
    return (y&((1<<p)-1))|((y>>p)<<(p+1))


def project(n,F,v,B):
    """x=insert(y,p)+t*v; keep unaffected flats and opposite forced-t overlaps."""
    assert 0<v<1<<n
    p=v.bit_length()-1; H=set(); live=[]
    for G in F:
        B.pay('direction_scan',1+len(G))
        row=next(((a,b) for a,b in G if dot(a,v)),None)
        if row is None:
            R=canon((delete(a,p),b) for a,b in G)
            if R is not None:H.add(R)
        else:
            a,b=row
            R=canon((delete(c^(a if dot(c,v) else 0),p),d^(b if dot(c,v) else 0)) for c,d in G)
            if R is not None:live.append((R,delete(a,p),b))
    for (A,a,b),(C,c,d) in combinations(live,2):
        B.pay('opposite_pair')
        R=canon(A+C+((a^c,b^d^1),))
        if R is not None:H.add(R)
    return tuple(sorted(H)),p


def reopen(F,v,p,y):
    x=insert(y,p)
    if satisfies(x,(),F):return x
    x^=v
    assert satisfies(x,(),F)
    return x


def directions(n,F,B):
    # Repeated normal lines are a source-derived coordinate heuristic.
    # Include all supplied rows and pair sums (polynomial even at high rank).
    counts=Counter()
    for G in F:
        local={a for a,b in G}
        for (a,b),(c,d) in combinations(G,2):
            B.pay('normal_pair');local.add(a^c)
        B.pay('normal_scan',len(G)+1);counts.update(local)
    E=[];S=()
    for a in sorted(counts,key=lambda a:(-counts[a],a)):
        B.pay('dual_basis');T=canon(S+((a,0),))
        if len(T)>len(S):E.append(a);S=T
    seen=set()
    for j in range(len(E)):
        B.pay('dual_section',len(E)+1)
        R=canon((a,int(i==j)) for i,a in enumerate(E));v=chart(n,R)[0]
        if v not in seen:seen.add(v);yield v
    for i in range(n):
        v=1<<i
        if v not in seen:seen.add(v);yield v


def eliminate(n,F,B):
    """Non-growing row-size steps only. No claim every source has such a step."""
    history=[]
    while n and F and () not in F:
        old=sum(len(G)+1 for G in F)
        for v in directions(n,F,B):
            B.pay('candidate');H,p=project(n,F,v,B)
            if sum(len(G)+1 for G in H)>old:continue
            H=simplify(H,B)
            if sum(len(G)+1 for G in H)<=old:
                history.append((F,v,p));F=H;n-=1;B.pay('elimination');break
        else:break
    return n,F,history


def solve(n,required,F,cap):
    B=Budget(cap)
    try:
        B.pay('input',n+len(required)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,required,F,B)
        if q is None:return None,B.stats,True
        u,V,H=q;H=simplify(H,B);d=len(V)
        if () in H:return None,B.stats,True
        M,R=transversal(H,B);C=tuple(H[j] for j in R)
        k,G,history=eliminate(d,C,B)
        x,_=join(k,G,B)
        if x is None:return None,B.stats,True
        for P,v,p in reversed(history):
            B.pay('reopen',1+sum(map(len,P)));x=reopen(P,v,p,x)
        y=lift(u,V,reopen_core(d,H,M,R,x));assert satisfies(y,required,F)
        return y,B.stats,True
    except Exhausted:return None,B.stats,False


def main():
    rng=Random(20261126);fixtures=points=reopened=verified=empty=0
    for n in range(1,8):
        for _ in range(45):
            required=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            F=tuple(G for _ in range(rng.randrange(8)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+1)))) is not None)
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(8))]
            for H in (F,cnf_flats(f)):
                v=rng.randrange(1,1<<n);G,p=project(n,H,v,Budget(1000000))
                for y in range(1<<(n-1)):
                    x=insert(y,p);ok=satisfies(x,(),H) or satisfies(x^v,(),H)
                    assert satisfies(y,(),G)==ok;points+=1
                    if ok:assert satisfies(reopen(H,v,p,y),(),H);reopened+=1
                truth=[x for x in range(1<<n) if satisfies(x,required,H)]
                x,s,done=solve(n,required,H,1000000);assert done and (x is not None)==bool(truth)
                if x is not None:assert x in truth;verified+=1
                else:empty+=1
                fixtures+=1
    # Ordinary resolution: (t OR a) AND (!t OR b) -> (a OR b).
    F=cnf_flats([(1,2),(-1,3)]);G,p=project(3,F,1,Budget(1000))
    assert G==cnf_flats([(1,2)])
    # Opposite orientations covering the whole line produce a forbidden point.
    F=cnf_flats([(1,),(-1,)]);G,p=project(1,F,1,Budget(1000));assert G==((),)
    # Dense complete normal graph; all orientations consistent with a chosen
    # intrinsic gauge (not supplied to solver). m>n, transversal core is full.
    for n in (8,12,16,20):
        A=[((1<<n)-1)^(1<<i) for i in range(n)]
        F=tuple(canon(((A[i],i%2),(A[j],j%2))) for i,j in combinations(range(n),2))
        M,R=transversal(F,Budget(1000000));assert len(R)==len(F) and len(M)==n
        x,s,done=solve(n,(),F,10000000);assert done and x is not None and satisfies(x,(),F)
        print('dense',n,'core',len(R),'eliminations',s['elimination'],'leaf_rows',s['leaf_rows'],'charged',sum(s.values()))
    assert solve(3,(),(),0)[2] is False
    print(dict(fixtures=fixtures,verified=verified,empty=empty,pointwise=points,reopen=reopened,controls='PASS'))

if __name__=='__main__':main()
