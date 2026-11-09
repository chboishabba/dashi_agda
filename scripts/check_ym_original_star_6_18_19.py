#!/usr/bin/env python3
"""Independent finite original 4D Wilson plaquette-star regression.

Checks L=3,4,5 genuine oriented +links, +/- four-bond plaquette support,
six incident plaquettes, <=18 conflicts, symmetric conflict graph and
source-native greedy independence/maximality/19-packing on test lists.
Finite testing is not an Agda kernel proof or physical Wilson estimate.
"""
from itertools import product, combinations

def verify(L):
    V = list(product(range(L), repeat=4))
    def shift(x, a):
        y = list(x)
        y[a] = (y[a] + 1) % L
        return tuple(y)
    def plaquette(x, mu, nu):
        return {(x, mu), (shift(x, mu), nu),
                (shift(x, nu), mu), (x, nu)}
    links = [(x, d) for x in V for d in range(4)]
    incident = {b: set() for b in links}
    supports = []
    for x in V:
        for mu, nu in combinations(range(4), 2):
            p = plaquette(x, mu, nu)
            assert len(p) == 4
            k = len(supports)
            supports.append(p)
            for b in p:
                incident[b].add(k)
    conflict = {b: set() for b in links}
    for p in supports:
        for b in p:
            conflict[b].update(p - {b})
    assert all(len(incident[b]) == 6 for b in links)
    assert all(len(conflict[b]) <= 18 for b in links)
    assert all(all(b in supports[p] for p in incident[b]) for b in links)
    assert all(all(b in conflict[a] for a in conflict[b]) for b in links)
    assert sum(map(len, incident.values())) == 4 * len(supports)
    for seed in range(16):
        marked = links[seed::max(1, len(links) // 67)][:67]
        selected = []
        for b in marked:
            if all(b != a and b not in conflict[a] for a in selected):
                selected.append(b)
        assert 19 * len(selected) >= len(marked)
        for b in marked:
            assert b in selected or any(b in conflict[a] for a in selected)
        for a, b in combinations(selected, 2):
            assert b not in conflict[a]
    return (L, len(links), len(supports),
            max(map(len, conflict.values())))

if __name__ == "__main__":
    for L in (3, 4, 5):
        print("L=%d links=%d plaquettes=%d maxConflictDegree=%d"
              % verify(L))
