"""Source-derived bag schedules and bounded symmetry discovery.
Classical variable elimination / primal-graph min-fill, not an unrestricted
width theorem. Integrates the existing changing-stabilizer solver.
"""
from collections import Counter
from itertools import combinations, product
from random import Random

class Refused(Exception): pass

class Reservation:
    def __init__(self, cap):
        if cap<0:raise ValueError("cap")
        self.cap=cap;self.left=cap
    def pay(self,k):
        if k<0 or k>self.left:raise Refused()
        self.left-=k

def cover_score(bags,n):
    first=[next(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    last=[max(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    # Charged enumeration width is old live plus genuinely fresh.
    widths=tuple(sum(first[i]<=j<=last[i] for i in range(n)) for j in range(len(bags)))
    return max(widths,default=0),sum(1<<w for w in widths),len(bags)

def source_cover(F,n,B):
    if n<0 or any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError("source")
    B.pay(1+(n+1)**2+sum((1+len(c))**2 for c in F))
    clauses=tuple(tuple(sorted({abs(l)-1 for l in c})) for c in F)
    seen=set().union(*map(set,clauses))
    direct=clauses+tuple((i,) for i in range(n) if i not in seen)
    direct=direct or ((),)
    adj={i:set() for i in range(n)}
    for c in clauses:
        for i in c:adj[i].update(set(c)-{i})
    bags=[];remaining=set(range(n))
    while remaining:
        B.pay(1+len(remaining)*(1+n)**2)
        def score(i):
            V=adj[i]&remaining
            return sum(b not in adj[a] for a,b in combinations(sorted(V),2)),len(V),i
        i=min(remaining,key=score);V=adj[i]&remaining
        bags.append(tuple(sorted(V|{i})))
        for j in V:adj[j].update(V-{j})
        remaining.remove(i)
    bags=tuple(bags) or ((),)
    B.pay(1+(n+1)*(len(direct)+len(bags)+1))
    best=min((direct,tuple(reversed(direct)),bags,tuple(reversed(bags))),key=lambda b:cover_score(b,n))
    assert set().union(*map(set,best))==set(range(n))
    assert all(any(set(c)<=set(b) for b in best) for c in clauses)
    return best,cover_score(best,n)

def twin_generators(F,n,rows,B,max_swaps=3):
    """Find independent transpositions, not an automorphism oracle.
    Limit closure to 2**max_swaps. Source validation is repeated downstream.
    """
    if max_swaps<0 or any(len(r)!=n for r in rows):raise ValueError("shape")
    C=Counter(tuple(sorted(c)) for c in F)
    used=set();G=[]
    for i,j in combinations(range(n),2):
        if len(G)>=max_swaps:break
        B.pay(1+n+len(rows)+sum(1+len(c) for c in F))
        if i in used or j in used or any(r[i]%3!=r[j]%3 for r in rows):continue
        g=list(range(n));g[i],g[j]=j,i
        moved=Counter(tuple(sorted((g[abs(l)-1]+1)*(1 if l>0 else -1) for l in c)) for c in F)
        if moved==C:G.append(tuple(g));used.update((i,j))
    return tuple(G)

def source_solve(F,n,rows,target,cap,max_width=8,pin_width=2,data_clock=None):
    from check_pnp_changing_stabilizer import solve
    if min(max_width,pin_width)<0:raise ValueError('width')
    B=Reservation(cap)
    try:
        reserve=cap//4;B.pay(reserve);P=Reservation(reserve)
        bags,width=source_cover(F,n,P)
        G=twin_generators(F,n,rows,P)
    except Refused:
        # Do not claim anything from a failed planner. The prior solver
        # may still use a single original bag and its prefix fallback.
        bags=(tuple(range(n)),);G=();width=None
    try:
        B.pay(1+n+sum(1+len(c) for c in F)+len(rows)*(n+1))
    except Refused:return dict(status="UNKNOWN",reserved=cap-B.left)
    pins=();force_cut=None
    if width is not None and width[0]>max_width and not G:
        # A measured high-fill diagnostic, NOT a treewidth lower bound.
        # Add an original pin bag, keeping all source clauses covered.
        try:
            B.pay(1+n+sum(1+len(c) for c in F))
        except Refused:return dict(status="UNKNOWN",reserved=cap-B.left,cover_width=width)
        degree=Counter(abs(l)-1 for c in F for l in set(c))
        pins=tuple(sorted(range(n),key=lambda i:(degree[i],i))[:pin_width])
        bags=(pins,)+bags;force_cut=1
    q=solve(F,n,bags,rows,target,G,B.left,force_cut=force_cut,data_clock=data_clock)
    B.pay(q["reserved"])
    if data_clock is not None and q["status"]=="WITNESS":
        from check_pnp_bit_data_schedule import audit,Refused as DataRefused
        try:assert audit(F,rows,tuple(t%3 for t in target),q["witness"],data_clock)
        except DataRefused:q=dict(q,status="WITNESS_DATA_AUDIT_REFUSED")
    return dict(q,reserved=cap-B.left,cover_width=width,generators=len(G),
                high_fill=force_cut is not None,pins=pins)

def count_reference(F,n,bags,rows,target):
    # Independent raw frontier: owner and exact last-use deletion.
    first=[next(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    last=[max(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    owned=[[] for b in bags]
    for c in F:
        owned[next(j for j,b in enumerate(bags) if {abs(l)-1 for l in c}<=set(b))].append(c)
    D={((),(0,)*len(rows)):1}
    for j,b in enumerate(bags):
        fresh=tuple(i for i in b if first[i]==j);N=Counter()
        for (key,s),mass in D.items():
            for bits in product((0,1),repeat=len(fresh)):
                z=dict(zip(fresh,bits));x=dict(key)|z
                if not all(any(x[abs(l)-1]==int(l>0) for l in c) for c in owned[j]):continue
                t=tuple((u+sum(row[i]*z[i] for i in fresh))%3 for u,row in zip(s,rows))
                k=tuple(sorted((i,v) for i,v in x.items() if last[i]>j))
                N[k,t]+=mass
        D=N
    return D.get(((),tuple(v%3 for v in target)),0)

def main():
    rng=Random(36943);checks=0
    for n in range(0,9):
        for k in range(16):
            F=tuple(tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(min(n,4)+1))) for _ in range(k%7))
            rows=(tuple(rng.randrange(3) for i in range(n)),)
            B=Reservation(10**8);bags,width=source_cover(F,n,B)
            G=twin_generators(F,n,rows,B)
            for t in range(3):
                exact=sum(all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)
                    and sum(a*b for a,b in zip(rows[0],x))%3==t
                    for x in product((0,1),repeat=n))
                assert count_reference(F,n,bags,rows,(t,))==exact
                checks+=1
            assert len(G)<=3
    n=32;F=tuple((i,i+1) for i in range(1,n));bags,width=source_cover(F,n,Reservation(10**8))
    assert width[0]<=2
    try:source_cover(F,n,Reservation(0));raise AssertionError("free discovery")
    except Refused:pass
    print(dict(original_fibres=checks,path_width=width[0],planning_refusal=1))

if __name__=="__main__":main()
