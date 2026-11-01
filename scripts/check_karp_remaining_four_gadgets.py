#!/usr/bin/env python3
"""Last four Karp (1972) gadget constructions with independent finite oracles.

Source: R. M. Karp, "Reducibility Among Combinatorial Problems",
DOI 10.1007/978-1-4684-2001-2_9, pp. 98-100, Figure 1.
DASHI source reconstructions; not Agda or polynomial machine proofs.
"""
from itertools import product, combinations
from check_karp_historical_reductions import (
    colouring, exact_cover, vertex_cover, sat
)


def colouring_to_exact_cover(n, edges, k):
    # The colour bound is binary encoded: k >= n is a constant-size YES case.
    # Without this guard, enumerating k colour slots is exponential in log(k).
    if k >= n:
        return (frozenset((0,)),)
    # The historical problem defines the universe as union of the family.
    # Guard impossible small palettes with a fixed no-instance.
    if (n and k == 0) or (edges and k < 2):
        return (frozenset((0,1)), frozenset((1,2)), frozenset((0,2)))
    incident = {v: [] for v in range(n)}
    for e in sorted(edges):
        for v in e: incident[v].append(e)
    universe = set(('vertex', v) for v in range(n)) | set(('edge', e) for e in edges)
    universe |= {('slot', v, e, f) for v in range(n) for e in incident[v] for f in range(k)}
    family = []
    for v in range(n):
        for f in range(k):
            family.append(frozenset({('vertex',v)} |
                                    {('slot',v,e,f) for e in incident[v]}))
    for e in sorted(edges):
        u,v=e
        for f in range(k):
            for g in range(k):
                if f != g:
                    family.append(frozenset({('edge',e)} |
                        {('slot',u,e,h) for h in range(k) if h != f} |
                        {('slot',v,e,h) for h in range(k) if h != g}))
    assert not universe or set().union(*(set(x) for x in family)) == universe
    return tuple(family)


def exact_to_3dm(sets):
    # Karp reduces after a separately justified |S_j| >=2 preprocessing.
    assert all(len(s)>=2 for s in sets)
    t = tuple((u,j) for j,subset in enumerate(sets) for u in sorted(subset))
    if not t:
        return (),0
    elements = sorted(frozenset().union(*sets))
    alpha = {u: next(v for v in t if v[0]==u) for u in elements}
    rest = set(t)-set(alpha.values())
    pi = {}
    for j, subset in enumerate(sets):
        ts = [v for v in t if v[1]==j]
        for k,v in enumerate(ts): pi[v] = ts[(k+1)%len(ts)]
    triples = {(alpha[u], (u,j), (u,j)) for u,j in t}
    triples |= {(beta, sigma, pi[sigma]) for beta in rest for sigma in t}
    return tuple(triples),len(t)


def three_dimensional_matching(triples, size):
    if not size: return True
    first = sorted({a for a,_,_ in triples})
    if len(first) != size: return False
    byfirst = {a: [(b,c) for x,b,c in triples if x==a] for a in first}
    def search(i,used_second,used_third):
        if i == len(first): return True
        return any(search(i+1,used_second|{b},used_third|{c})
                   for b,c in byfirst[first[i]]
                   if b not in used_second and c not in used_third)
    return search(0,set(),set())


def graph_to_directed_hamiltonian(n, edges, k):
    # The historical positive-k gadget assumes nonempty edge incidence.
    # Empty graph and a budget covering all active vertices are fixed YES.
    if not edges or k >= len(set(v for e in edges for v in e)):
        return 3, frozenset({(0,1),(1,2),(2,0)})
    assert k > 0
    ordered=tuple(sorted(edges))
    incident={v: [i for i,e in enumerate(ordered) if v in e] for v in range(n)}
    nodes=[('a',f) for f in range(k)]
    for i,(u,v) in enumerate(ordered):
        for x in (u,v):
            for a in (0,1): nodes.append((x,i,a))
    index={p:i for i,p in enumerate(nodes)}
    arcs=set()
    for i,(u,v) in enumerate(ordered):
        for x in (u,v): arcs.add((index[(x,i,0)],index[(x,i,1)]))
        for a in (0,1):
            arcs.add((index[(u,i,a)],index[(v,i,a)]))
            arcs.add((index[(v,i,a)],index[(u,i,a)]))
    for u,edges_of_u in incident.items():
        if not edges_of_u: continue
        for i,j in zip(edges_of_u,edges_of_u[1:]):
            arcs.add((index[(u,i,1)],index[(u,j,0)]))
        for f in range(k):
            arcs.add((index[(u,edges_of_u[-1],1)],index[('a',f)]))
            arcs.add((index[('a',f)],index[(u,edges_of_u[0],0)]))
    return len(nodes),frozenset(arcs)


def directed_ham_dp(n, arcs):
    # Exponential Held-Karp oracle; independent from the graph constructor.
    if n == 0: return False
    adjacency=[set() for _ in range(n)]
    for u,v in arcs: adjacency[u].add(v)
    dp={(1,0)}
    for _ in range(n-1):
        dp={(mask|(1<<v),v) for mask,u in dp for v in adjacency[u]
            if not (mask>>v&1)}
    return any(mask==(1<<n)-1 and 0 in adjacency[v] for mask,v in dp)


def three_sat_to_colouring(n, clauses):
    # Dense renaming makes the palette linear in actual occurrence count,
    # not in a potentially huge binary-encoded maximum variable identifier.
    ids = sorted({abs(lit) for c in clauses for lit in c})
    assert all(0 < x <= n for x in ids)
    dense = {x:i+1 for i,x in enumerate(ids)}
    clauses = tuple(tuple(dense[abs(lit)] if lit>0 else -dense[-lit]
                          for lit in clause) for clause in clauses)
    n = len(ids)
    # (m+1)-colour construction, pad m>=4 to force an unused variable
    # in each width<=3 clause, hence block the extra colour in a bad clause.
    assert all(len(c) <= 3 for c in clauses)
    m = max(4,n)
    anchors = tuple(range(m))
    pos = {i: m+2*i for i in range(m)}
    neg = {i: m+2*i+1 for i in range(m)}
    edges = set(combinations(anchors,2))
    for i in range(m):
        edges.add(tuple(sorted((pos[i],neg[i]))))
        for j in range(m):
            if i!=j:
                edges.add(tuple(sorted((j,pos[i]))))
                edges.add(tuple(sorted((j,neg[i]))))
    for idx, clause in enumerate(clauses):
        d = 3*m+idx
        lits = set(clause)
        for i in range(m):
            p,nn = i+1,-i-1
            if p in lits and nn in lits:
                raise ValueError('normalize tautological clause first')
            if p in lits:
                edges.add(tuple(sorted((d,pos[i]))))
            elif nn in lits:
                edges.add(tuple(sorted((d,neg[i]))))
            else:
                edges.add(tuple(sorted((d,pos[i]))))
                edges.add(tuple(sorted((d,neg[i]))))
    return 3*m+len(clauses),frozenset(edges),m+1,m


def simplify_cnf(clauses):
    # Remove tautological clauses and deduplicate literals preserving order.
    return tuple(tuple(dict.fromkeys(c)) for c in clauses
                 if not any(-lit in c for lit in c))


def k_graph_colourable(n,edges,k,anchors=0):
    # Generic finite backtracking graph-colourability oracle, with fixed
    # anchor clique colours modulo a global palette permutation.
    if k == 0: return n == 0
    neighbors=[set() for _ in range(n)]
    for u,v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
    assigned={i:i for i in range(anchors)}
    def rec():
        if len(assigned)==n:return True
        v=max((v for v in range(n) if v not in assigned),
              key=lambda v:(len({assigned[u] for u in neighbors[v]
                                 if u in assigned}),len(neighbors[v])))
        forbidden={assigned[u] for u in neighbors[v] if u in assigned}
        for c in range(k):
            if c not in forbidden:
                assigned[v]=c
                if rec():return True
                del assigned[v]
        return False
    return rec()


def main():
    counts=dict(E09=0,E11=0,E13=0,E16=0)
    for n in range(0,4):
        possible=tuple(combinations(range(n),2))
        for flags in product((0,1),repeat=len(possible)):
            edges=frozenset(e for e,f in zip(possible,flags) if f)
            for k in range(0,3):
                assert exact_cover(colouring_to_exact_cover(n,edges,k)) == colouring(n,edges,k)
                counts['E13']+=1
                if edges and 0 < k < n:
                    expected=vertex_cover(n,edges,k)
                    observed=directed_ham_dp(*graph_to_directed_hamiltonian(n,edges,k))
                    assert expected==observed,('E09',n,edges,k)
                    counts['E09']+=1
    subsets=tuple(frozenset(i for i in range(3) if mask>>i&1)
                  for mask in range(8) if mask.bit_count()>=2)
    for m in range(0,3):
        for family in product(subsets,repeat=m):
            assert three_dimensional_matching(*exact_to_3dm(family)) == exact_cover(family)
            counts['E16']+=1
    for n in range(0,3):
        lits=tuple(i for i in range(-n,n+1) if i)
        pool=((),)+tuple((a,) for a in lits)+tuple((a,b) for a in lits for b in lits)+tuple((a,b,c) for a in lits for b in lits for c in lits)
        for length in range(0,3):
            for clauses in product(pool,repeat=length):
                nv,edges,k,anchor=three_sat_to_colouring(n,simplify_cnf(clauses))
                assert sat(n,clauses)==k_graph_colourable(nv,edges,k,anchor)
                counts['E11']+=1
    for n in range(0,4):
        for k in (n, n+1, 2**128):
            assert exact_cover(colouring_to_exact_cover(n,frozenset(),k))
    # Variable indices are binary encoded and need not be dense.
    nv,edge_list,k,anchor = three_sat_to_colouring(10**15, ((10**15,),))
    assert nv == 13 and k == 5 and k_graph_colourable(nv,edge_list,k,anchor)
    print('PASS final four historical edge gadgets:',counts)


if __name__ == '__main__':
    main()
