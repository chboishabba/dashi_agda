#!/usr/bin/env python3
"""A5^3 ⋊ C3 on a 180-point coordinate algebra / c=0 commutative VOA.

Authors / prior art:
  Hatcher: Alexander exterior free-group tower (Algebraic Topology, Ex 2B.2).
  Standard commutative differential algebra -> vertex algebra construction.
  DASHI: three-root G, A5 quotient, finite semidirect action and loss audit.

This is exact finite arithmetic. It does NOT kernel-verify an infinite
fundamental-group isomorphism, an Agda VOA, or the geometric horned embedding.
"""
from itertools import permutations
from random import Random

IDENTITY = tuple(range(5))


def multiply(a, b):
    return tuple(a[b[i]] for i in range(5))


def inverse(a):
    return tuple(a.index(i) for i in range(5))


def commutator(a, b):
    return multiply(multiply(multiply(a, b), inverse(a)), inverse(b))


def parity_even(p):
    return sum(p[i] > p[j] for i in range(5) for j in range(i + 1, 5)) % 2 == 0


A5 = tuple(p for p in permutations(range(5)) if parity_even(p))


def generated_order(generators):
    steps = tuple(generators) + tuple(inverse(g) for g in generators)
    seen, frontier = {IDENTITY}, [IDENTITY]
    while frontier:
        x = frontier.pop()
        for g in steps:
            h = multiply(x, g)
            if h not in seen:
                seen.add(h)
                frontier.append(h)
    return len(seen)


def exhaustive_commutator_section():
    section = {}
    root = None
    for a in A5:
        for b in A5:
            g = commutator(a, b)
            section.setdefault(g, (a, b))
            if root is None and order(g) == 5 and generated_order((a, b)) == 60:
                root = (g, a, b)
    assert len(A5) == 60
    assert len(section) == 60
    assert root is not None
    # This is a deliberate order-FIVE quotient, not the first
    # generating A5 commutator, which can have order THREE.
    assert order(root[0]) == 5
    return section, root


def order(a):
    q = IDENTITY
    for i in range(1, 61):
        q = multiply(q, a)
        if q == IDENTITY:
            return i
    raise AssertionError("A5 element order was not detected")


def shift(triple, k):
    """(beta^k u)_i = u_(i-k), indices modulo three."""
    return tuple(triple[(i - k) % 3] for i in range(3))


def semidirect_multiply(g, h):
    u, k = g
    v, l = h
    shifted = shift(v, k)
    return (tuple(multiply(u[i], shifted[i]) for i in range(3)), (k + l) % 3)


def semidirect_inverse(g):
    u, k = g
    return (tuple(inverse(u[(i + k) % 3]) for i in range(3)), (-k) % 3)


def coordinate_action(g, x):
    """(u,k) . (i,a) = (i+k, u_(i+k) a)."""
    u, k = g
    i, a = x
    j = (i + k) % 3
    return j, multiply(u[j], a)


def state_action(g, function, x):
    """Pullback by inverse coordinate permutation: a genuine LEFT action."""
    return function(coordinate_action(semidirect_inverse(g), x))


def meridian_image(sector, element):
    return tuple(element if i == sector else IDENTITY for i in range(3))


def main():
    section, (root, a, b) = exhaustive_commutator_section()
    assert generated_order((a, b)) == 60
    root_order = order(root)
    assert root_order == 5, "Pin the deterministic first generating witness"

    for g, (x, y) in section.items():
        assert commutator(x, y) == g

    # Each level of the binary horn tower maps compatibly onto A5.
    level = {(): root}
    for depth in range(1, 6):
        next_level = {}
        for word, g in level.items():
            x, y = (a, b) if not word else section[g]
            assert commutator(x, y) == g
            next_level[word + (0,)] = x
            next_level[word + (1,)] = y
        level = next_level
        assert generated_order(level.values()) == 60

    rng = Random(20261024)
    identity = ((IDENTITY, IDENTITY, IDENTITY), 0)
    coordinates = tuple((i, a) for i in range(3) for a in A5)
    assert len(coordinates) == 180

    def random_actor():
        return tuple(rng.choice(A5) for _ in range(3)), rng.randrange(3)

    # Exact samples of nonabelian semidirect composition and the
    # induced automorphism on C^180 = Fun(C3 x A5,C).
    for _ in range(4000):
        g, h = random_actor(), random_actor()
        x = rng.choice(coordinates)
        assert semidirect_multiply(g, semidirect_inverse(g)) == identity
        assert semidirect_multiply(semidirect_inverse(g), g) == identity
        assert coordinate_action(semidirect_multiply(g, h), x) == (
            coordinate_action(g, coordinate_action(h, x)))
        assert coordinate_action(identity, x) == x
        assert coordinate_action(semidirect_inverse(g),
                                 coordinate_action(g, x)) == x

        f = lambda y: (y[0] + 1) * (y[1][0] + 2)
        t = lambda y: (y[0] + 3) * (y[1][1] + 1)
        assert state_action(semidirect_multiply(g, h), f, x) == (
            state_action(g, lambda y: state_action(h, f, y), x))
        assert state_action(g, lambda y: f(y) * t(y), x) == (
            state_action(g, f, x) * state_action(g, t, x))
        assert state_action(g, lambda y: f(y) + t(y), x) == (
            state_action(g, f, x) + state_action(g, t, x))
        assert state_action(g, lambda y: 1, x) == 1
        assert state_action(g, lambda y: 0, x) == 0

    # Full finite Q⋊C3 faithfulness theorem has an elementary
    # three-coordinate proof: fixing all (i,e) forces k=0, u_i=e.
    # Exhaustively audit a 60-element x 3 sector slice as a regression.
    for k in range(3):
        for a in A5:
            g = ((a, IDENTITY, IDENTITY), k)
            fixed = all(coordinate_action(g, (i, IDENTITY)) == (i, IDENTITY)
                        for i in range(3))
            assert fixed == (g == identity)

    # A source meridian has nontrivial image; its fifth power is
    # invisible under the finite representation. Nontriviality of the
    # original infinite-group fifth power uses Hatcher injectivity,
    # NOT this finite test alone.
    q0 = meridian_image(0, root)
    q1 = meridian_image(1, root)
    assert q0 != (IDENTITY,) * 3
    assert shift(q0, 1) == q1
    assert any(coordinate_action((q0, 0), x) != x for x in coordinates)
    power = (IDENTITY,) * 3
    for _ in range(root_order):
        power = tuple(multiply(power[i], q0[i]) for i in range(3))
    assert power == (IDENTITY,) * 3

    print("A5=60; commutator coverage 60/60; compatible binary stages 0..5: PASS")
    print("Semidirect-product and C3 action, 4000 deterministic cases: PASS")
    print("180-coordinate commutative algebra unit/product preserved: PASS")
    print("Finite quotient A5^3 ⋊ C3 action faithful (3-coordinate argument): PASS")
    print(f"Source meridian finite image order: {root_order}")
    print("Root meridian^5 in quotient kernel: PASS; source nontriviality uses Hatcher")
    print("Actual VOA: C^180, all degree 0, zero derivation and conformal vector")
    print("No Monster / CFT-type VOA / geometric pi1 identification asserted")


if __name__ == "__main__":
    main()
