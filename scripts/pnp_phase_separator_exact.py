"""Bounded exact separator selection on the actual pulled-back F3 phase.

Selection sees the FULL monomial graph, including quadratic bridges.
Fixing one axis cannot create edges absent from the graph with that
axis removed. Branching still uses all three exact restrictions.
No claim of bounded separator width on unrestricted inputs.
"""

def choose_separator(P,n,pay):
    active=set();edges=[set() for _ in range(n)];hard=[]
    for m,a in P.items():
        pay(1+len(m)**2)
        if not m or not a%3:continue
        I=set(m);active.update(I)
        for i in I:edges[i].update(I-{i})
        if len(m)>2:hard.append(I)
    hits={i:sum(i in I for I in hard) for i in active}
    pay(1+len(active)*len(hard))
    fallback=min((i for i in active if hits[i]),key=lambda i:(-hits[i],i))
    # Small deterministic bounded portfolio, including quadratic-only
    # bridges. Each probe is charged before graph traversal.
    candidates=sorted(active,key=lambda i:(-len(edges[i]),-hits[i],i))[:32]
    if fallback not in candidates:candidates.append(fallback)
    best=None
    for j in candidates:
        pay(1+len(active)+sum(len(edges[i]) for i in active)+len(hard))
        unseen=active-{j};owner={};sizes=[]
        while unseen:
            start=min(unseen);unseen.remove(start);stack=[start];size=0
            while stack:
                i=stack.pop();owner[i]=len(sizes);size+=1
                nxt=edges[i]&unseen
                unseen.difference_update(nxt);stack.extend(nxt)
            sizes.append(size)
        live={owner[next(iter(I))] for I in hard if j not in I}
        if len(live)<2:continue
        score=(max(sizes[k] for k in live),sum(sizes[k] for k in live),-len(live),-hits[j],j)
        if best is None or score<best[0]:best=(score,j)
    return fallback if best is None else best[1]


def restrict_axis(P,n,j,value,pay):
    """Exact reduced F3 substitution. Separate constant character for
    canonical reuse of residuals differing only by overall phase."""
    pay(1+sum(1+len(m) for m in P))
    Q={}
    for m,a in P.items():
        key=tuple(i-(i>j) for i in m if i!=j)
        coeff=(Q.get(key,0)+a*pow(value,m.count(j),3))%3
        if coeff:Q[key]=coeff
        else:Q.pop(key,None)
    return Q


def phase_key(P,n,pay):
    # Count dictionary traversal and comparison/sorting upper bound in
    # abstract work units; integer size is a separate bit-clock issue.
    pay(1+n+sum(1+len(m) for m in P)+len(P)*max(1,len(P).bit_length()))
    return n,tuple(sorted((m,a%3) for m,a in P.items() if m and a%3))
