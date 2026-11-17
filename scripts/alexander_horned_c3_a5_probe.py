#!/usr/bin/env python3
"""Exact A5 finite test for three C3-permuted binary horn trees.

Not a proof of a geometric embedding or pi_1 presentation.
Sources: Hatcher, Algebraic Topology, Example 2B.2; N. W. Riebe (1968).
"""
from itertools import permutations

ID = tuple(range(5))


def compose(a, b):
    return tuple(a[b[i]] for i in range(5))


def inverse(a):
    return tuple(a.index(i) for i in range(5))


def commutator(a, b):
    return compose(compose(compose(a, b), inverse(a)), inverse(b))


def parity_even(p):
    return sum(p[i] > p[j] for i in range(5)
               for j in range(i + 1, 5)) % 2 == 0


A5 = tuple(p for p in permutations(range(5)) if parity_even(p))


def generated_order(generators):
    moves = tuple(generators) + tuple(inverse(g) for g in generators)
    seen, frontier = {ID}, [ID]
    while frontier:
        x = frontier.pop()
        for g in moves:
            y = compose(x, g)
            if y not in seen:
                seen.add(y)
                frontier.append(y)
    return len(seen)


def permutation_order(g):
    value = ID
    for n in range(1, 61):
        value = compose(value, g)
        if value == ID:
            return n
    raise AssertionError("A5 permutation failed finite-order check")


def build_witnesses():
    witnesses, root = {}, None
    for a in A5:
        for b in A5:
            g = commutator(a, b)
            witnesses.setdefault(g, (a, b))
            if (root is None and permutation_order(g) == 5
                    and generated_order((a, b)) == len(A5)):
                root = (g, a, b)
    assert len(A5) == 60 and len(witnesses) == 60
    assert root is not None
    assert permutation_order(root[0]) == 5
    return witnesses, root


def tree_values(depth, witnesses, root):
    root_g, root_a, root_b = root
    levels = [{(): root_g}]
    for level in range(depth):
        nxt = {}
        for path, g in levels[-1].items():
            a, b = (root_a, root_b) if level == 0 else witnesses[g]
            assert commutator(a, b) == g
            nxt[path + (0,)] = a
            nxt[path + (1,)] = b
        levels.append(nxt)
    return levels


def in_factor(g, i):
    return tuple(g if j == i else ID for j in range(3))


def c3_rotate(t):
    return (t[2], t[0], t[1])


def verify(depth=5):
    witnesses, root = build_witnesses()
    levels = tree_values(depth, witnesses, root)
    assert all(generated_order(level.values()) == 60 for level in levels[1:])
    for level in levels:
        for path, g in level.items():
            for sector in range(3):
                q = in_factor(g, sector)
                assert c3_rotate(q) == in_factor(g, (sector + 1) % 3)
                assert c3_rotate(c3_rotate(c3_rotate(q))) == q
    root_g = root[0]
    assert root_g != ID
    assert permutation_order(root_g) == 5
    assert c3_rotate(in_factor(root_g, 0)) == in_factor(root_g, 1)
    assert in_factor(root_g, 0) != in_factor(root_g, 1)
    print("A5 order: 60; commutator coverage: 60/60; root pair generates A5")
    print(f"Finite levels audited: 0..{depth}; deepest meridians: {2**depth} per sector")
    print("C3-equivariant A5^3 assignment: PASS")
    print("C3 factor rotation non-inner in A5^3: PASS (factor-support argument)")
    print("Geometric embedding / van Kampen equivalence: NOT ESTABLISHED")
    return root, levels


if __name__ == "__main__":
    verify()
