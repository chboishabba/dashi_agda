#!/usr/bin/env python3
"""Constructive finite regressions for selected Karp 1972 direct reductions.

Source: R. Karp, Reducibility Among Combinatorial Problems (1972),
DOI 10.1007/978-1-4684-2001-2_9, pp. 94-101.
Exhaustive oracles here only test tiny instances; they are not polynomial
decision algorithms, machine-clock proofs, or Agda kernel certificates.
"""
from itertools import product, combinations


def choices(n, k):
    return combinations(range(n), k)


def sat(n, clauses):
    return any(all(any((bits[abs(l)-1] if l > 0 else not bits[-l-1]) for l in clause)
                   for clause in clauses) for bits in product((False, True), repeat=n))


def sat_to_clique(clauses):
    nodes = [(i, l) for i, clause in enumerate(clauses) for l in clause]
    edges = frozenset((u, v) for u in range(len(nodes)) for v in range(u+1, len(nodes))
                      if nodes[u][0] != nodes[v][0] and nodes[u][1] != -nodes[v][1])
    return len(nodes), edges, len(clauses)


def clique(n, edges, k):
    return any(all((u, v) in edges for u, v in combinations(s, 2)) for s in choices(n, k))


def clique_to_packing(n, edges, k):
    nonedges = frozenset((u, v) for u in range(n) for v in range(u+1, n)
                         if (u, v) not in edges)
    sets = tuple(frozenset(e for e in nonedges if v in e) for v in range(n))
    return sets, k  # indexed sets: equal sets are not silently merged


def packing(sets, k):
    return any(all(not (sets[i] & sets[j]) for i, j in combinations(indices, 2))
               for indices in choices(len(sets), k))


def clique_to_cover(n, edges, k):
    if k > n:
        return 3, frozenset({(0, 1), (0, 2), (1, 2)}), 1  # fixed NO
    return n, frozenset((u, v) for u in range(n) for v in range(u+1, n)
                        if (u, v) not in edges), n-k


def vertex_cover(n, edges, k):
    return any(all(u in subset or v in subset for u, v in edges)
               for r in range(max(-1, k)+1) for selected in choices(n, r)
               for subset in (set(selected),))


def cover_to_set_cover(n, edges, k):
    return tuple(frozenset(e for e in edges if v in e) for v in range(n)), k


def set_cover(sets, k):
    universe = frozenset().union(*sets) if sets else frozenset()
    return any(frozenset().union(*(sets[i] for i in selected)) == universe
               for r in range(min(k, len(sets))+1) for selected in choices(len(sets), r))


def colouring(n, edges, k):
    return any(all(bits[u] != bits[v] for u, v in edges)
               for bits in product(range(k), repeat=n))


def colouring_to_clique_cover(n, edges, k):
    return n, frozenset((u, v) for u in range(n) for v in range(u+1, n)
                        if (u, v) not in edges), k


def clique_cover(n, edges, k):
    return any(all(bits[u] != bits[v] or (u, v) in edges for u in range(n)
                   for v in range(u+1, n)) for bits in product(range(k), repeat=n))


def exact_cover(sets):
    universe = frozenset().union(*sets) if sets else frozenset()
    return any(all(sum(e in sets[i] for i in selected) == 1 for e in universe)
               for r in range(len(sets)+1) for selected in choices(len(sets), r))


def exact_to_exact_hitting(sets):
    universe = sorted(frozenset().union(*sets) if sets else frozenset())
    return tuple(frozenset(i for i, s in enumerate(sets) if e in s) for e in universe), len(sets)


def exact_hitting(transposed, n):
    return any(all(len(subset & s) == 1 for s in transposed)
               for r in range(n+1) for selected in choices(n, r)
               for subset in (set(selected),))


def exact_to_knapsack(sets):
    universe = sorted(frozenset().union(*sets) if sets else frozenset())
    base = len(sets) + 1
    numbers = tuple(sum(base**j for j, e in enumerate(universe) if e in s) for s in sets)
    return numbers, sum(base**j for j in range(len(universe)))


def knapsack(numbers, target):
    return any(sum(numbers[i] for i in selected) == target
               for r in range(len(numbers)+1) for selected in choices(len(numbers), r))


def signed_to_positive_knapsack(numbers, target):
    """Digit-guarded reduction requiring one of two choices per source item."""
    n = len(numbers)
    if not n:
        return ((1, 1), 1) if target == 0 else ((2,), 1)
    offset = 1 + sum(map(abs, numbers)) + abs(target)
    base = 4*n*offset + 2*sum(map(abs, numbers)) + 2*abs(target) + 5
    out = tuple(base**(i+1) + offset + delta
                for i, a in enumerate(numbers) for delta in (a, 0))
    goal = sum(base**(i+1) for i in range(n)) + n*offset + target
    assert all(a > 0 for a in out) and 0 <= goal <= sum(out)
    return out, goal


def positive_knapsack_to_partition(numbers, target):
    assert all(a > 0 for a in numbers) and 0 <= target <= sum(numbers)
    return tuple(numbers) + (target + 1, sum(numbers) + 1 - target)


def knapsack_to_partition(numbers, target):
    positive, goal = signed_to_positive_knapsack(numbers, target)
    return positive_knapsack_to_partition(positive, goal)


def partition(numbers):
    total = sum(numbers)
    return any(2 * sum(numbers[i] for i in subset) == total
               for r in range(len(numbers)+1) for subset in choices(len(numbers), r))


def three_sat(n, clauses):
    clauses_new = []
    for clause in clauses:
        if len(clause) <= 3:
            clauses_new.append(tuple(clause))
            continue
        first, rest = tuple(clause[:2]), list(clause[2:])
        n += 1
        new = n
        clauses_new.append(first + (new,))
        while len(rest) > 2:
            previous = new
            n += 1
            new = n
            clauses_new.append((-previous, rest.pop(0), new))
        if rest:
            clauses_new.append((-new, *rest))
    assert all(len(c) <= 3 for c in clauses_new)
    return n, tuple(clauses_new)



def sat_to_binary_ip(n, clauses):
    # Clause truth count >=1, encoded as an equality using binary slack.
    widths = [max(0, (len(clause)-1).bit_length()) for clause in clauses]
    total = n + sum(widths)
    rows, rhs, index = [], [], n
    for clause, width in zip(clauses, widths):
        row = [0]*total
        neg = 0
        for lit in clause:
            row[abs(lit)-1] += 1 if lit > 0 else -1
            neg += lit < 0
        for i in range(width):
            row[index+i] = -(1 << i)
        index += width
        rows.append(tuple(row))
        rhs.append(1-neg)
    return tuple(rows), tuple(rhs), total


def binary_ip(rows, rhs, variables):
    return any(all(sum(c*x for c,x in zip(row, bits)) == target
                   for row, target in zip(rows, rhs))
               for bits in product((0,1), repeat=variables))


def cover_to_feedback_vertex(n, edges, k):
    return n, frozenset((u,v) for a,b in edges for u,v in ((a,b),(b,a))), k


def acyclic(n, arcs):
    reachable = [set() for _ in range(n)]
    for u,v in arcs:
        reachable[u].add(v)
    for k in range(n):
        for i in range(n):
            if k in reachable[i]:
                reachable[i].update(reachable[k])
    return all(i not in reachable[i] for i in range(n))


def feedback_vertex(n, arcs, k):
    return any(acyclic(n, frozenset((u,v) for u,v in arcs if u not in subset and v not in subset))
               for length in range(min(k,n)+1)
               for selected in choices(n,length) for subset in (set(selected),))


def cover_to_feedback_arc(n, edges, k):
    arcs = {(2*u, 2*u+1) for u in range(n)}
    arcs |= {(2*u+1, 2*v) for a,b in edges for u,v in ((a,b),(b,a))}
    return 2*n, frozenset(arcs), k


def feedback_arc(n, arcs, k):
    arcs = tuple(sorted(arcs))
    return any(acyclic(n, frozenset(e for i,e in enumerate(arcs) if i not in deleted))
               for length in range(min(k,len(arcs))+1)
               for selected in choices(len(arcs),length) for deleted in (set(selected),))


def directed_to_undirected_hamiltonian(n, arcs):
    edges = {(3*u, 3*u+1) for u in range(n)} | {(3*u+1, 3*u+2) for u in range(n)}
    edges |= {tuple(sorted((3*u+2, 3*v))) for u,v in arcs}
    return 3*n, frozenset(edges)


def directed_hamiltonian(n, arcs):
    if n == 0:
        return False
    return any(all((path[i],path[(i+1)%n]) in arcs for i in range(n))
               for rest in __import__('itertools').permutations(range(1,n))
               for path in ((0,)+rest,))


def undirected_hamiltonian(n, edges):
    if n < 3:
        return False
    return any(all(tuple(sorted((path[i],path[(i+1)%n]))) in edges for i in range(n))
               for rest in __import__('itertools').permutations(range(1,n))
               for path in ((0,)+rest,))


def check_additional():
    counts = dict(E01=0, E07=0, E08=0, E10=0)
    for n in range(3):
        lits = tuple(i for i in range(-n,n+1) if i)
        pool = ((),)+tuple((lit,) for lit in lits)+tuple((a,b) for a in lits for b in lits)
        for size in range(3):
            for f in product(pool, repeat=size):
                assert binary_ip(*sat_to_binary_ip(n,f)) == sat(n,f)
                counts['E01'] += 1
    for n in range(0,4):
        possible = tuple(combinations(range(n),2))
        for presence in product((0,1), repeat=len(possible)):
            edges = frozenset(e for e,b in zip(possible,presence) if b)
            for k in range(n+1):
                expected = vertex_cover(n, edges, k)
                assert feedback_vertex(*cover_to_feedback_vertex(n, edges, k)) == expected
                assert feedback_arc(*cover_to_feedback_arc(n, edges, k)) == expected
                counts['E07'] += 1; counts['E08'] += 1
    for n in range(1,4):
        arcs = tuple((u,v) for u in range(n) for v in range(n) if u!=v)
        for pres in product((0,1),repeat=len(arcs)):
            source = frozenset(e for e,b in zip(arcs,pres) if b)
            assert undirected_hamiltonian(*directed_to_undirected_hamiltonian(n,source)) == directed_hamiltonian(n,source)
            counts['E10'] += 1
    print('PASS additional direct reduction checks',counts)


def exact_to_steiner(sets):
    elements = sorted(frozenset().union(*sets) if sets else frozenset())
    if not elements:
        return 2, ((0,1,1),), frozenset((0,1)), 1
    n = 1 + len(sets) + len(elements)
    edges = [(0,1+j,len(sets[j])) for j in range(len(sets))]
    edges.extend((1+j,1+len(sets)+i,0) for j, subset in enumerate(sets)
                 for i,e in enumerate(elements) if e in subset)
    required = frozenset((0,)+tuple(range(1+len(sets), n)))
    return n, tuple(edges), required, len(elements)


def steiner_tree(n, edges, required, budget):
    # Exponential independent oracle, not a polynomial decision algorithm.
    for bits in product((0,1), repeat=len(edges)):
        selected = [e for e,b in zip(edges,bits) if b]
        if sum(w for _,_,w in selected) > budget:
            continue
        parent = list(range(n))
        def find(u):
            while parent[u] != u:
                u = parent[u]
            return u
        tree = True
        for u,v,_ in selected:
            a,b = find(u),find(v)
            if a == b:
                tree = False
                break
            parent[a] = b
        if tree and len({find(u) for u in required}) <= 1:
            return True
    return False


def knapsack_to_sequencing(numbers, target):
    positive, goal = signed_to_positive_knapsack(numbers, target)
    budget = sum(positive) - goal
    if budget == 0:
        return (1,), (1,), (1,), 1  # fixed YES with positive budget
    return positive, (goal,)*len(positive), positive, budget


def job_sequencing(times, deadlines, penalties, budget):
    return any(sum(penalties[i] for j,i in enumerate(ordering)
                   if sum(times[v] for v in ordering[:j+1]) > deadlines[i]) <= budget
               for ordering in __import__('itertools').permutations(range(len(times))))


def check_more():
    counters = dict(E15=0,E18=0)
    subsets = tuple(frozenset(i for i in range(2) if mask>>i&1) for mask in range(4))
    for m in range(0,4):
        for family in product(subsets,repeat=m):
            assert exact_cover(family) == steiner_tree(*exact_to_steiner(family))
            counters['E15'] += 1
    for m in range(0,4):
        for nums in product(range(-1,2),repeat=m):
            for b in range(-1,2):
                assert knapsack(nums,b) == job_sequencing(*knapsack_to_sequencing(nums,b))
                counters['E18'] += 1
    print('PASS terminal Steiner/scheduling checks',counters)

def main():
    counts = {k: 0 for k in ('E02', 'E03', 'E04', 'E05', 'E06', 'E12', 'E14', 'E17', 'E19')}
    for n in range(0, 3):
        literals = tuple(i for i in range(-n, n+1) if i)
        pool = ((),) + tuple((l,) for l in literals) + tuple((a,b) for a in literals for b in literals)
        for length in range(0, 4):
            for clauses in product(pool, repeat=length):
                desired = sat(n, clauses)
                assert clique(*sat_to_clique(clauses)) == desired
                counts['E02'] += 1
                n3, c3 = three_sat(n, clauses)
                assert sat(n3, c3) == desired
                counts['E03'] += 1
    for clause in ((1,2,3,4), (1,2,3,4,5), (1,-1,1,-1,1,1), (1,2,3,4,5,6,7)):
        n = max(abs(x) for x in clause)
        assert sat(n,(clause,)) == sat(*three_sat(n,(clause,)))
        counts['E03'] += 1
    for n in range(0, 5):
        possible = tuple(combinations(range(n),2))
        for presence in product((0,1), repeat=len(possible)):
            edges = frozenset(e for e, bit in zip(possible, presence) if bit)
            for k in range(n+2):
                expected = clique(n, edges, k)
                assert packing(*clique_to_packing(n, edges, k)) == expected
                assert vertex_cover(*clique_to_cover(n, edges, k)) == expected
                counts['E04'] += 1; counts['E05'] += 1
                assert set_cover(*cover_to_set_cover(n, edges, k)) == vertex_cover(n, edges, k)
                counts['E06'] += 1
                if k <= n:
                    assert clique_cover(*colouring_to_clique_cover(n, edges, k)) == colouring(n, edges, k)
                    counts['E12'] += 1
    subsets = tuple(frozenset(i for i in range(3) if bit>>i&1) for bit in range(8))
    for m in range(0, 4):
        for family in product(subsets, repeat=m):
            accepted = exact_cover(family)
            assert exact_hitting(*exact_to_exact_hitting(family)) == accepted
            assert knapsack(*exact_to_knapsack(family)) == accepted
            counts['E14'] += 1; counts['E17'] += 1
    for m in range(0, 4):
        for numbers in product(range(-2,3), repeat=m):
            for b in range(-2,3):
                assert partition(knapsack_to_partition(numbers,b)) == knapsack(numbers,b)
                counts['E19'] += 1
    print('PASS exact finite reductions:', counts)
    check_additional()
    check_more()


if __name__ == '__main__':
    main()
