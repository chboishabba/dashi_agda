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


if __name__ == '__main__':
    main()
