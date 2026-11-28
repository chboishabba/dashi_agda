"""Recursive source quotient attachments, with explicit logical reservations.
No physical-bit or universal complexity claim.
"""
from itertools import product, combinations
from collections import Counter
from check_pnp_live_signed_orbit_join import Budget, Refused, accepts, source_group
from check_pnp_mobius_prefix import prefix_portfolio

def act(g,x):
    return {g[i]:b for i,b in x.items()}

def canonical(G,key,B):
    B.pay(len(G)*(1+len(key)))
    return min((tuple(sorted(act(g,dict(key)).items())),g) for g in G)

def frontier_join(F,n,bags,rows,target,generators,B):
    """Exact orbit mass DP. Use a common subgroup preserving every bag.
    This suffices for every cut (including nonconsecutive occurrences).
    A changing subgroup needs explicit orbit refinement; not assumed here.
    """
    bags=tuple(tuple(sorted(set(b))) for b in bags)
    if len(rows)!=len(target) or any(len(row)!=n for row in rows):raise ValueError("shape")
    if any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError("literal")
    B.pay(1+(len(bags)+1)*(n+sum(1+len(c) for c in F)+len(rows)*(n+1)))
    if set().union(*map(set,bags))!=set(range(n)):raise ValueError("cover")
    if not bags:
        ok=accepts(F,()) and all(t%3==0 for t in target)
        return int(ok),() if ok else None,1,()
    G=source_group(F,n,rows,(),generators,B)
    # Intersect stabilizers of ALL bags, preserving owners and suffixes.
    # This is a subgroup, even if the supplied generators fail individually.
    B.pay(len(G)*sum(1+len(b) for b in bags))
    G=tuple(g for g in G if all({g[i] for i in b}==set(b) for b in bags))
    first=[next(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    last=[max(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    owned=[[] for b in bags]
    for c in F:
        V={abs(l)-1 for l in c}
        j=next((j for j,b in enumerate(bags) if V<=set(b)),None)
        if j is None:raise ValueError("uncovered clause")
        owned[j].append(c)
    r=len(rows);D={((),(0,)*r):(1,{})};peak=1;trace=[]
    for j,bag in enumerate(bags):
        fresh=tuple(i for i in bag if first[i]==j);H=owned[j];N={}
        B.pay(len(D)*(1<<len(fresh))*(1+n+r*n+sum(1+len(c) for c in H)))
        for (key,s),(mass,witness) in D.items():
            old=dict(key)
            for bits in product((0,1),repeat=len(fresh)):
                z=dict(zip(fresh,bits));x=old|z
                if not accepts(H,x):continue
                t=tuple((s[k]+sum(rows[k][i]*z[i] for i in fresh))%3 for k in range(r))
                live=tuple(sorted((i,v) for i,v in x.items() if last[i]>j))
                rep,g=canonical(G,live,B)
                # The mass is the total across the source orbit. For each
                # old member, transport extensions to the representative;
                # equivariance makes the histogram of next orbits identical.
                K=(rep,t);m,w=N.get(K,(0,act(g,witness|z)))
                N[K]=(m+mass,w)
        D=N;peak=max(peak,len(D))
        trace.append((sum(first[i]<=j<last[i] for i in range(n)),len(D),len(G)))
    B.pay(1+n+sum(1+len(c) for c in F)+r*(n+1))
    mass,w=D.get(((),tuple(t%3 for t in target)),(0,None))
    if w is None:return 0,None,peak,tuple(trace)
    x=tuple(w[i] for i in range(n))
    assert accepts(F,x) and tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==tuple(t%3 for t in target)
    return mass,x,peak,tuple(trace)

def c1a(F,n,bags,rows,target,generators,cap):
    """One paid allowance, exact frontier then existing prefix portfolio.
    High frontier is diagnostic, never a lower-bound certificate.
    Prefix positive count is not an original witness until lifted.
    """
    B=Budget(cap);trial=cap//2
    B.pay(trial);local=Budget(trial)
    try:
        mass,x,peak,trace=frontier_join(F,n,bags,rows,target,generators,local)
        return dict(status="WITNESS" if mass else "EMPTY",count=mass,witness=x,
                    peak=peak,trace=trace,reserved=B.used)
    except Refused:pass
    # Constant observation label 0: contrast[0] = 2 * original fibre mass.
    # Charge full reservation and input conversion; no partial false EMPTY.
    try:B.pay(1+n*(1+len(rows)))
    except Refused:return dict(status="UNKNOWN",reserved=B.used)
    cols=tuple(tuple(row[i] for row in rows)+(0,) for i in range(n))
    def query(C):
        reserve=min(B.left,max(32,cap//(2*(n+1))))
        if not reserve:return None
        B.pay(reserve)
        return prefix_portfolio(C,cols,target,0,tuple(range(n)),1,work_cap=reserve)
    q=query(F)
    if q is None:return dict(status="UNKNOWN",reserved=B.used)
    lo,hi,_=q
    if hi[0]==0:return dict(status="EMPTY",reserved=B.used)
    if lo[0]<=0:return dict(status="UNKNOWN",reserved=B.used,contrast=(lo,hi))
    # Witness recovery via paid unit-clause self-reduction.
    C=tuple(F);x=[]
    for i in range(n):
        found=False
        for b in (0,1):
            L=C+(((i+1) if b else -(i+1),),)
            q=query(L)
            if q is not None and q[0][0]>0:
                C=L;x.append(b);found=True;break
        if not found:return dict(status="POSITIVE_NO_LIFT",reserved=B.used,contrast=(lo,hi))
    assert accepts(F,x) and tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==tuple(t%3 for t in target)
    return dict(status="WITNESS",witness=tuple(x),reserved=B.used,contrast=(lo,hi))

def orbit_supports(x,y,G,B):
    """Fixed anchor, every transported rival, no orbit-size assumption."""
    B.pay(len(G)*(1+len(x)))
    return frozenset(frozenset(i for i,v in enumerate(x) if v!=act(g,dict(enumerate(y)))[i]) for g in G)

def minimal_hits(supports,n,B):
    if frozenset() in supports:return ()
    hits=[]
    for k in range(n+1):
        for s in combinations(range(n),k):
            B.pay(1+(len(hits)+len(supports))*(1+n))
            S=frozenset(s)
            if not any(h<=S for h in hits) and all(S&d for d in supports):hits.append(S)
    return tuple(hits)

def orbit_epoch(x,domain,G,state,consumer,observe,a,b,B):
    """Consumer invariance and actual reachable rival are independent gates.
    Orbit-transversal supports are diagnostic, not extra paid occurrences.
    """
    if not a<b:raise ValueError("epoch")
    D=set(domain);B.pay(len(D)*len(G)*(1+len(x)))
    for y in D:
        for g in G:
            z=tuple(v for _,v in sorted(act(g,dict(enumerate(y))).items()))
            if z not in D or consumer(y)!=consumer(z):raise ValueError("not consumer invariant")
    for y in sorted(D):
        B.pay(1+b-a)
        if state(x,a)!=state(y,a) or consumer(x)==consumer(y) or state(x,b)==state(y,b):continue
        j=next(j for j in range(a,b) if state(x,j+1)!=state(y,j+1))
        assert state(x,j)==state(y,j) and observe(x,j)!=observe(y,j)
        S=orbit_supports(x,y,G,B)
        H=minimal_hits(S,len(x),B)
        return dict(event=j,rival=y,supports=S,hits=H)
    return None

def main():
    from random import Random
    rng=Random(36943);C=Counter()
    # All three variables exchangeable across every bag; add later spectator.
    F=((1,2),(2,3),(1,3),(4,));bags=((0,1,2),(0,1,2,3))
    G=((1,2,0,3),(0,2,1,3))
    for t in range(3):
        rows=((1,1,1,0),)
        z=frontier_join(F,4,bags,rows,(t,),G,Budget(10**7))
        raw=frontier_join(F,4,bags,rows,(t,),(),Budget(10**7))
        assert z[:2][0]==raw[0] and z[2]<raw[2]
        C["orbit_frontier"]+=1
    for n in range(1,8):
        bags=tuple((i,i+1) for i in range(n-1)) or ((0,),)
        for _ in range(8):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in b) for b in bags)
            rows=(tuple(rng.randrange(3) for i in range(n)),)
            for t in range(3):
                W=[x for x in product((0,1),repeat=n) if accepts(F,x) and sum(a*b for a,b in zip(rows[0],x))%3==t]
                z=frontier_join(F,n,bags,rows,(t,),(),Budget(10**7))
                assert z[0]==len(W) and ((z[1] in W) if W else z[1] is None)
                for cap in (0,64,4096):
                    q=c1a(F,n,bags,rows,(t,),(),cap)
                    assert q["reserved"]<=cap
                    if q["status"]=="EMPTY":assert not W
                    if q["status"]=="WITNESS":assert q["witness"] in W
                    if q["status"]=="POSITIVE_NO_LIFT":assert W
                    C["budget"]+=1
                C["original"]+=1
    x=(0,0,0);D=tuple(product((0,1),repeat=3))
    G=source_group((),3,(),(),((1,2,0),(0,2,1)),Budget(10000))
    # Anchor zero, choose some nonzero rival. Consumer invariant under S3.
    f=lambda x:sum(x)>0
    state=lambda x,t:False if t==0 else f(x)
    q=orbit_epoch(x,D,G,state,f,lambda x,t:f(x),0,1,Budget(100000))
    assert q["event"]==0 and all(all(h&s for s in q["supports"]) for h in q["hits"])
    C["orbit_epoch"]+=1
    print(dict(C))
if __name__=="__main__":main()
