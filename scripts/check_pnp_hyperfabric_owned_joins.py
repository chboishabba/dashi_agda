"""Finite hyperfabric attachments; logical budgets, not physical tape clocks."""
from itertools import product
from math import gcd, isqrt, prod
from check_pnp_conditional_autarky import accepts
from check_pnp_source_cluster_planner import planned_cluster_join
from check_pnp_stack_priority_transport import AuditedRunner, audit
from check_pnp_stack_fractran import source_next


class Refused(Exception):
    pass


class Budget:
    def __init__(self, cap):
        if cap < 0: raise ValueError("negative cap")
        self.left = cap
        self.cap = cap

    def pay(self, amount):
        if amount < 0: raise ValueError("negative charge")
        if amount > self.left: raise Refused()
        self.left -= amount

    @property
    def used(self):
        return self.cap - self.left


def extract_disjoint_interiors(F, n, k_max, d_max, budget):
    """Greedy source separator; no global small-separator assertion."""
    if min(n, k_max, d_max) < 0: raise ValueError("bounds")
    budget.pay(1+n+sum((1+len(c))**2 for c in F))
    adj = [set() for _ in range(n)]
    for c in F:
        V = {abs(l)-1 for l in c}
        if not V <= set(range(n)): raise ValueError("literal")
        for i in V: adj[i].update(V-{i})
    S = set()

    def components(S):
        budget.pay(1+n+sum(map(len, adj)))
        unseen = set(range(n))-S
        out = []
        while unseen:
            i = min(unseen); unseen.remove(i); todo=[i]; C={i}
            while todo:
                v=todo.pop(); nxt=adj[v]&unseen
                unseen.difference_update(nxt); C.update(nxt); todo.extend(nxt)
            out.append(tuple(sorted(C)))
        return tuple(out)

    while True:
        D=components(S)
        if max(map(len,D),default=0)<=d_max:
            return tuple(sorted(S)),D
        if len(S)>=k_max: raise Refused()
        candidates=[i for C in D if len(C)>d_max for i in C]
        best=None
        for i in candidates:
            C=components(S|{i})
            score=(max(map(len,C),default=0),sum(len(c)**2 for c in C),i)
            if best is None or score<best: best=score
        S.add(best[-1])


def discover_and_join(F,n,x,rows,target,cap,k_max,d_max):
    """Same cap for discovery and existing fixed-exterior producer."""
    B=Budget(cap)
    try:
        S,D=extract_disjoint_interiors(F,n,k_max,d_max,B)
        out=planned_cluster_join(F,n,S,x,rows,target,B.left,max(k_max,d_max))
        if out is None: return None
        count,witness,used=out; B.pay(used)
        return count,witness,B.used,S,D
    except Refused: return None


def overlapping_join(F,n,bags,rows,target,cap):
    """Exact original factor cover, one owner per clause and variable.
    Keep shared coordinates until final join; no double-counted syndrome.
    Returns count, witness, logical work or None on refusal.
    """
    B=Budget(cap)
    try:
        bags=tuple(tuple(sorted(set(b))) for b in bags)
        B.pay(1+n+sum(map(len,bags))+sum(1+len(c) for c in F)+len(rows)*(n+1))
        if n<0 or len(rows)!=len(target) or any(len(r)!=n for r in rows):
            raise ValueError("source")
        if set().union(*map(set,bags))!=set(range(n)): raise ValueError("cover")
        if any(not 1<=abs(l)<=n for c in F for l in c): raise ValueError("literal")
        if not bags:
            return (int(accepts(F,()) and all(t%3==0 for t in target)),
                    () if accepts(F,()) and all(t%3==0 for t in target) else None,B.used)
        B.pay(1+len(bags)*(n+sum(1+len(c) for c in F)))
        owners=[next(j for j,b in enumerate(bags) if i in b) for i in range(n)]
        clause_owner=[]
        for c in F:
            eligible=[j for j,b in enumerate(bags) if {abs(l)-1 for l in c}<=set(b)]
            if not eligible: raise ValueError("clause not covered")
            clause_owner.append(eligible[0])
        boundary={i for i in range(n) if sum(i in b for b in bags)>1}
        r=len(rows); states={((),(0,)*r):(1,{})}
        for j,bag in enumerate(bags):
            H=[c for c,o in zip(F,clause_owner) if o==j]
            B.pay((1<<len(bag))*(1+n+r*n+sum(1+len(c) for c in H)))
            table={}
            for bits in product((0,1),repeat=len(bag)):
                x=dict(zip(bag,bits))
                if not accepts(H,x): continue
                key=tuple((i,x[i]) for i in bag if i in boundary)
                y=tuple(sum(row[i]*x[i] for i in bag if owners[i]==j)%3 for row in rows)
                d,k=table.get((key,y),(x,0));table[(key,y)]=(d,k+1)
            B.pay(len(states)*len(table)*(1+n+r)**2)
            nxt={}
            for (key,y),(k,x) in states.items():
                for (key2,z),(d,m) in table.items():
                    a=dict(key);b=dict(key2)
                    if any(a[i]!=b[i] for i in a.keys()&b.keys()): continue
                    K=(tuple(sorted((a|b).items())),tuple((u+v)%3 for u,v in zip(y,z)))
                    old,rep=nxt.get(K,(0,x|d));nxt[K]=(old+k*m,rep)
            states=nxt
        B.pay(1+len(states)*(n+r+1)**2)
        count=0; witness=None
        for (_,y),(k,x) in states.items():
            if y==tuple(t%3 for t in target):
                count+=k; witness=tuple(x[i] for i in range(n))
        if witness is not None:
            assert accepts(F,witness)
            assert tuple(sum(a*b for a,b in zip(row,witness))%3 for row in rows)==tuple(t%3 for t in target)
        return count,witness,B.used
    except Refused: return None


def alloc_lane_prime(M):
    """Actual five data lanes plus all actual private/canonical tags."""
    primes=[]; p=2
    while len(primes)<len(M.tags):
        if all(p%q for q in primes if q<=isqrt(p)): primes.append(p)
        p+=1
    assert len(set(M.tags))==len(primes)
    assert all(gcd(a,b)==1 for i,a in enumerate(primes) for b in primes[i+1:])
    return dict(zip(M.tags,primes))


def literal_instruction(M,v,bit_cap,step_cap):
    """Bounded numeric check of actual emitted fractions and endpoint.
    Explicitly refuse large materialized integers; never call it a jump clock.
    """
    if min(bit_cap,step_cap)<0: raise ValueError("bounds")
    audit(M); primes=tuple(alloc_lane_prime(M).values())
    if sum(a*p.bit_length() for a,p in zip(v,primes))>bit_cap: return None
    P=M.fractions(primes)
    for (num,den),f in zip(M.sparse,P):
        assert f.numerator==prod(primes[i]**a for i,a in num.items())
        assert f.denominator==prod(primes[i]**a for i,a in den.items())
    N=prod(p**a for p,a in zip(primes,v))
    q,L,R,halt=M.decode(v)
    if halt: return v,True,0
    Rn=AuditedRunner(M)
    for k in range(step_cap):
        i,u=Rn.first(v)
        j=next((j for j,f in enumerate(P) if N%f.denominator==0),None)
        assert i==j and u is not None
        if sum(a*p.bit_length() for a,p in zip(u,primes))>bit_cap: return None
        N=N//P[j].denominator*P[j].numerator
        assert N==prod(p**a for p,a in zip(primes,u))
        v=u
        tag=M.tags[next(i for i in range(5,len(v)) if v[i])][0]
        if tag in ("q","halt"):
            want=source_next(M,(q,L,R)); got=M.decode(v)
            assert got==((*want,False) if want is not None else (q,L,R,True))
            return v,tag=="halt",k+1
    return None


def reachable_divergences(x,domain,state,consumer,t):
    """Actual valid inputs only; state and consumer are supplied owners."""
    return tuple(y for y in domain if state(y,t)==state(x,t) and consumer(y)!=consumer(x))


def fresh_epoch_events(x,domain,state,consumer,observe,cuts):
    """Anchor actual first-divergence occurrences to disjoint time intervals.
    Counterfactuals may reuse input coordinates; each paid event counted once.
    No lower bound on how many such events must exist.
    """
    if any(a>=b for a,b in zip(cuts,cuts[1:])): raise ValueError("cuts")
    paid=set(); receipts=[]
    for a,b in zip(cuts,cuts[1:]):
        for y in reachable_divergences(x,domain,state,consumer,a):
            if state(x,b)==state(y,b): continue
            j=next(j for j in range(a,b) if state(x,j+1)!=state(y,j+1))
            assert state(x,j)==state(y,j) and observe(x,j)!=observe(y,j)
            if j not in paid:
                paid.add(j); receipts.append((a,b,j,y))
    return tuple(receipts)
