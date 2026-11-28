"""Changing-stabilizer frontier, using the existing source action and prefix owner.
Logical reservations only. Original prefix multiplicity is uniform on each
certified cut orbit; explicit refinement is required before advancing.
"""
from itertools import product
from collections import Counter
from check_pnp_recursive_quotient import act, canonical
from check_pnp_live_signed_orbit_join import Budget, Refused, accepts, source_group
from check_pnp_mobius_prefix import prefix_portfolio

def orbit(key,G,B):
    B.pay(len(G)*(1+len(key)))
    return {tuple(sorted(act(g,dict(key)).items())):g for g in G}

def refine(D,G,H,B):
    """H <= G. Split old orbit mass by exact member count, transport witness."""
    if not H or not set(H)<=set(G):raise ValueError("subgroup")
    N={}
    for (key,s),(mass,w) in D.items():
        O=orbit(key,G,B)
        unit,rem=divmod(mass,len(O))
        if rem:raise AssertionError("nonuniform orbit mass")
        todo=set(O)
        while todo:
            B.pay(1+len(todo));x=min(todo)
            P=orbit(x,H,B)
            assert set(P)<=todo
            todo.difference_update(P)
            K=(x,s)
            assert K not in N
            N[K]=(unit*len(P),act(O[x],w))
    assert sum(m for m,w in D.values())==sum(m for m,w in N.values())
    return N

def merge(D,H,B):
    N={}
    for (key,s),(mass,w) in D.items():
        x,g=canonical(H,key,B);K=(x,s)
        old,rep=N.get(K,(0,act(g,w)))
        N[K]=(old+mass,rep)
    return N

def plan(F,n,bags,rows,target,generators,B):
    if n<0 or len(rows)!=len(target) or any(len(row)!=n for row in rows):raise ValueError("shape")
    if any(not 1<=abs(l)<=n for c in F for l in c):raise ValueError("literal")
    bags=tuple(tuple(sorted(set(b))) for b in bags)
    B.pay(1+(len(bags)+1)*(n+sum(1+len(c) for c in F)+len(rows)*(n+1)))
    if set().union(*map(set,bags))!=set(range(n)):raise ValueError("cover")
    if not bags:bags=((),)
    first=[next(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    last=[max(j for j,b in enumerate(bags) if i in b) for i in range(n)]
    owned=[[] for b in bags]
    for c in F:
        V={abs(l)-1 for l in c}
        j=next((j for j,b in enumerate(bags) if V<=set(b)),None)
        if j is None:raise ValueError("uncovered clause")
        owned[j].append(c)
    G=source_group(F,n,rows,(),generators,B)
    prefix=[];groups=[G];assigned=set()
    def moved(g,C):
        return Counter(tuple(sorted((g[abs(l)-1]+1)*(1 if l>0 else -1) for l in c)) for c in C)
    for j,bag in enumerate(bags):
        assigned.update(bag);prefix.extend(owned[j])
        live={i for i in assigned if last[i]>j}
        B.pay(len(G)*(1+n+sum(1+len(c) for c in prefix)))
        C=Counter(tuple(sorted(c)) for c in prefix)
        groups.append(tuple(g for g in G if {g[i] for i in assigned}==assigned
            and {g[i] for i in live}==live and moved(g,prefix)==C))
    return bags,first,last,owned,groups

def advance(D,j,P,rows,B):
    bags,first,last,owned,groups=P
    # Intersection preserves old and new assigned sets, live sets and
    # processed clause multisets; hence fresh variables/current factors.
    G,H=groups[j:j+2];B.pay(len(G)+len(H))
    J=tuple(g for g in G if g in set(H))
    D=refine(D,G,J,B)
    fresh=tuple(i for i in bags[j] if first[i]==j);C=owned[j]
    n=len(first);r=len(rows);N={}
    B.pay(len(D)*(1<<len(fresh))*(1+n+r*n+sum(1+len(c) for c in C)))
    for (key,s),(mass,w) in D.items():
        for bits in product((0,1),repeat=len(fresh)):
            z=dict(zip(fresh,bits));x=dict(key)|z
            if not accepts(C,x):continue
            t=tuple((s[k]+sum(rows[k][i]*z[i] for i in fresh))%3 for k in range(r))
            live=tuple(sorted((i,v) for i,v in x.items() if last[i]>j))
            k,g=canonical(J,live,B);K=(k,t)
            old,rep=N.get(K,(0,act(g,w|z)))
            N[K]=(old+mass,rep)
    # J-orbit masses are disjoint; H preserves the completed prefix.
    return merge(N,H,B)

def residual(P,j,key,s,rows,target):
    """Export the actual unprocessed constraints, not a fresh surrogate."""
    bags,first,last,owned,groups=P
    a=dict(key);R=tuple(i for i,f in enumerate(first) if f>=j);C=[]
    for cs in owned[j:]:
        for c in cs:
            if any(abs(l)-1 in a and a[abs(l)-1]==int(l>0) for l in c):continue
            z=tuple(l for l in c if abs(l)-1 not in a)
            assert all(abs(l)-1 in R for l in z)
            C.append(z)
    t=tuple((v-u)%3 for v,u in zip(target,s))
    return tuple(C),R,t

def finish_residual(D,P,j,F,rows,target,B):
    """Use certified prefix enclosures on each real remaining fibre.
    A positive bound without lift is not promoted to WITNESS.
    """
    n=len(P[1]);B.pay(1+n*(1+len(rows))+len(D))
    cols=tuple(tuple(row[i] for row in rows)+(0,) for i in range(n))
    positive=False;unknown=False
    # Budget both polarities plus the initial query for every retained fibre.
    remaining=sum(f>=j for f in P[1]); overhead=len(D)*(1+n+sum(1+len(c) for c in F))
    per_query=max(0,(B.left-overhead)//max(1,len(D)*(1+2*remaining)))
    for (key,s),(mass,w) in D.items():
        B.pay(1+n+sum(1+len(c) for c in F))
        C,R,t=residual(P,j,key,s,rows,target)
        def query(C):
            reserve=min(B.left,per_query)
            if not reserve:return None
            B.pay(reserve)
            return prefix_portfolio(C,cols,t,0,R,1,work_cap=reserve)
        q=query(C)
        if q is None:unknown=True;continue
        lo,hi,_=q
        if hi[0]==0:continue
        if lo[0]<=0:unknown=True;continue
        positive=True
        from check_pnp_positive_residual import recover
        # Limit recovery to this fibre's fair share of remaining allowance.
        cap=min(B.left,2*len(R)*per_query);B.pay(cap)
        z=recover(C,R,rows,cols,t,n,lo,hi,Budget(cap))
        if z is None:continue
        if len(z)==len(R):
            x=tuple((w|z)[i] for i in range(n))
            assert accepts(F,x) and tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==tuple(t%3 for t in target)
            return dict(status="WITNESS",witness=x,cut=j)
    return dict(status="POSITIVE_NO_LIFT" if positive else "UNKNOWN" if unknown else "EMPTY",cut=j)

def solve(F,n,bags,rows,target,generators,cap,force_cut=None):
    B=Budget(cap)
    try:
        # Reserve a separate fallback portion up front. A failed advance
        # is charged in full and the previous immutable cut survives.
        budget=cap//2;B.pay(budget);A=Budget(budget)
        P=plan(F,n,bags,rows,target,generators,A)
        D={((),(0,)*len(rows)):(1,{})};j=0;trace=[]
        while j<len(P[0]) and (force_cut is None or j<force_cut):
            try:N=advance(D,j,P,rows,A)
            except Refused:break
            D=N;j+=1;trace.append((len(D),len(P[4][j])))
        if j==len(P[0]):
            k,w=D.get(((),tuple(t%3 for t in target)),(0,None))
            x=None if w is None else tuple(w[i] for i in range(n))
            if x is not None:assert accepts(F,x) and tuple(sum(a*b for a,b in zip(row,x))%3 for row in rows)==tuple(t%3 for t in target)
            return dict(status="WITNESS" if k else "EMPTY",count=k,witness=x,trace=trace,reserved=B.used)
        result=finish_residual(D,P,j,F,rows,target,B)
        return dict(result,trace=trace,reserved=B.used)
    except Refused:return dict(status="UNKNOWN",reserved=B.used)

def main():
    # S3 symmetry at the first bag; the next two asymmetric placements
    # split its live orbit, then merge at the terminal cut.
    F=((1,2),(2,3),(1,3));bags=((0,1,2),(0,),(1,2))
    G=((1,2,0),(0,2,1))
    # Additional genuine source orbit: all clauses are first owned.
    for t in range(3):
        rows=((1,1,1),)
        W=[x for x in product((0,1),repeat=3) if accepts(F,x) and sum(x)%3==t]
        q=solve(F,3,bags,rows,(t,),G,1000000)
        assert q["count"]==len(W)
        assert q["trace"][0][1]==6 and q["trace"][1][1]==2 and q["trace"][2][1]==6
        for j in range(3):
            q=solve(F,3,bags,rows,(t,),G,1000000,force_cut=j)
            assert q["status"]=="WITNESS" if W else q["status"]=="EMPTY"
    print("changing subgroup and residual handoff campaign written")

if __name__=="__main__":main()
