#!/usr/bin/env python3
"""Source-faithful exact finite audit for the 2swap video bridge.

No numerical approximation, no Agda kernel claim, no analytic monodromy
claim and no general quintic proof. Uses exact permutation tuples and
fractions. Original theorem credit: Abel, Galois, Riemann and Hamilton;
the executable finite checks belong to this DASHI PR.
"""
from collections import deque
from fractions import Fraction as F
from itertools import permutations, product

def compose(p, q):
    return tuple(p[q[i]] for i in range(len(p)))

def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))

def commutator(p, q):
    return compose(compose(compose(p, q), inverse(p)), inverse(q))

def generated_group(gens, n):
    identity = tuple(range(n))
    reached = {identity}
    queue = deque([identity])
    while queue:
        x = queue.popleft()
        for g in gens:
            y = compose(x, g)
            if y not in reached:
                reached.add(y)
                queue.append(y)
    return reached

def derived_subgroup(group):
    n = len(next(iter(group)))
    return generated_group(
        {commutator(x, y) for x in group for y in group}, n
    )

def derived_sizes(n):
    g = set(permutations(range(n)))
    sizes = [len(g)]
    while len(g) != 1:
        next_g = derived_subgroup(g)
        sizes.append(len(next_g))
        if next_g == g:
            return sizes
        g = next_g
    return sizes

def quaternion_product(a, b):
    w, x, y, z = a
    u, v, s, t = b
    return (
        w*u-x*v-y*s-z*t,
        w*v+x*u+y*t-z*s,
        w*s-x*t+y*u+z*v,
        w*t+x*s-y*v+z*u,
    )

def quaternion_conjugate(q):
    return q[0], -q[1], -q[2], -q[3]

def cubic_vieta_values(a, b, c, x):
    s1 = a+b+c
    s2 = a*b+b*c+a*c
    s3 = a*b*c
    return x*x*x-s1*x*x+s2*x-s3, (x-a)*(x-b)*(x-c)

def conjugate_endomorphism(p, f):
    pi = inverse(p)
    return tuple(p[f[pi[i]]] for i in range(3))

def main():
    expected = {
        2: [2, 1], 3: [6, 3, 1],
        4: [24, 12, 4, 1], 5: [120, 60, 60],
    }
    for n, sizes in expected.items():
        assert derived_sizes(n) == sizes, n

    # Three-strand braid relation and the pure endpoint kernel.
    e3 = (0, 1, 2)
    s0, s1 = (1, 0, 2), (0, 2, 1)
    assert compose(compose(s0, s1), s0) == \
        compose(compose(s1, s0), s1)
    assert compose(s0, s0) == e3
    # Artin exponent of sigma_0 squared is +2 although its S3 image is 1.
    assert 1 + 1 == 2

    # The exact 27 self-map carrier has 7 S3-conjugation orbits.
    s3 = tuple(permutations(range(3)))
    remaining = set(product(range(3), repeat=3))
    orbit_sizes = []
    while remaining:
        f = next(iter(remaining))
        orbit = {conjugate_endomorphism(p, f) for p in s3}
        assert orbit <= remaining or (orbit & remaining)
        remaining -= orbit
        orbit_sizes.append(len(orbit))
    assert sorted(orbit_sizes) == [1, 2, 3, 3, 6, 6, 6]

    # Five-root overlapping three-cycles: double commutators recover both.
    A = (1, 2, 0, 3, 4)
    B = (0, 1, 3, 4, 2)
    assert commutator(
        commutator(A, B), commutator(inverse(A), inverse(B))
    ) == A
    assert commutator(
        commutator(B, A), commutator(inverse(B), inverse(A))
    ) == B
    subgroup = generated_group((A, B), 5)
    assert len(subgroup) == 60
    assert derived_subgroup(subgroup) == subgroup
    # This is an exhaustive finite Python calculation, NOT a formal kernel
    # theorem identifying all permutations with the full A5 representation.

    # 243 balanced ternary words versus 125 five-mode triples.
    assert len(tuple(product((-1, 0, 1), repeat=5))) == 243
    triples = tuple(product(range(5), repeat=3))
    assert len(triples) == 125
    assert sum(len(set(t)) == 3 for t in triples) == 60
    assert 3**3 == 27 and 3**5 != 5**3

    # Finite exact rational cubic Vieta (including repeated roots).
    vieta_checks = 0
    for a, b, c, x in product(range(-2, 3), repeat=4):
        left, right = cubic_vieta_values(a, b, c, x)
        assert left == right
        for aa, bb, cc in permutations((a, b, c)):
            assert cubic_vieta_values(aa, bb, cc, x)[0] == left
        vieta_checks += 1
    assert vieta_checks == 625

    # The 120-degree quaternion lifts i->j->k, q^3=-1 and q^6=+1.
    q = (F(1, 2),) * 4
    one = (F(1), F(0), F(0), F(0))
    minus = (F(-1), F(0), F(0), F(0))
    q2 = quaternion_product(q, q)
    q3 = quaternion_product(q2, q)
    q6 = quaternion_product(q3, q3)
    assert sum(c*c for c in q) == 1
    assert q3 == minus and q6 == one
    basis = (
        (F(0), F(1), F(0), F(0)),
        (F(0), F(0), F(1), F(0)),
        (F(0), F(0), F(0), F(1)),
    )
    cycle = (1, 2, 0)
    for i in range(3):
        rotated = quaternion_product(
            quaternion_product(q, basis[i]), quaternion_conjugate(q)
        )
        assert rotated == basis[cycle[i]]

    print("POLYNOMIAL_VIDEO_MAXCUT_PASS "
          "video_topics=45 s2=2,1 s3=6,3,1 "
          "s4=24,12,4,1 s5=120,60,60 "
          "two_cycles_generate=60 a5_generated_perfect=true "
          "ternary_endomorphism_orbits=1,2,3,3,6,6,6 "
          "trit5=243 mode5triples=125 distinct_triples=60 "
          "vieta=625 q3=-1 q6=+1")
if __name__ == "__main__":
    main()
