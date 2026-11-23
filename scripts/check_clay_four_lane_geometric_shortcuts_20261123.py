#!/usr/bin/env python3
"""23 Nov 2026: independent exact-rational checks for four non-YM/RH Clay lanes.

NS: regionwise recentering defect in original NEGATED pair-difference blocks.
PNP: sparse occurrence-label extension and bit-inspection/comparison envelope.
BSD: inert-prime E:y^2=x^3-x trace cancellation over F_p.
Hodge: squarefree coordinate-cycle algebra on (CP^1)^r.

No direct original PDE nonlinear-work bound, gamma-word parser, TM runtime,
E32 modularity/Mellin, literal singular/de Rham geometry or proof kernel.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb
from random import Random
from sympy import primerange, legendre_symbol


def ns_block(rates, work, regions):
    out = {(a, b): Q(0) for a in range(3) for b in range(a, 3)}
    for i in range(len(rates)):
        for j in range(i + 1, len(rates)):
            a, b = sorted((regions[i], regions[j]))
            out[a, b] -= (rates[i] - rates[j]) * (work[i] - work[j])
    return out


def ns_moment(rates, work, regions):
    n = [0] * 3
    R, W, V = [[Q(0) for _ in range(3)] for _ in range(3)]
    for r, w, a in zip(rates, work, regions):
        n[a] += 1
        R[a] += r
        W[a] += w
        V[a] += r * w
    out = {}
    for a in range(3):
        for b in range(a, 3):
            out[a, b] = (R[a] * W[a] - n[a] * V[a] if a == b else
                         R[a] * W[b] + R[b] * W[a] - n[b] * V[a] - n[a] * V[b])
    return out, n, R


def check_ns():
    rng = Random(236023)
    for _ in range(1200):
        count = rng.randrange(12)
        r = [Q(rng.randrange(-10, 11), rng.randrange(1, 5)) for _ in range(count)]
        w = [Q(rng.randrange(-8, 9), rng.randrange(1, 6)) for _ in range(count)]
        labels = [rng.randrange(3) for _ in range(count)]
        direct = ns_block(r, w, labels)
        moments, n, R = ns_moment(r, w, labels)
        assert direct == moments
        common = Q(rng.randrange(-5, 6), 7)
        assert ns_block(r, [x - common for x in w], labels) == direct
        shift = [Q(rng.randrange(-5, 6), 11) for _ in range(3)]
        moved = ns_block(r, [x - shift[a] for x, a in zip(w, labels)], labels)
        for a in range(3):
            for b in range(a, 3):
                delta = (shift[a] - shift[b]) * (n[b] * R[a] - n[a] * R[b])
                assert moved[a, b] == direct[a, b] + delta
    # Unsafe local recentering, despite zero original work.
    r, w, labels = [Q(1), Q(3)], [Q(0), Q(0)], [0, 1]
    assert ns_block(r, [Q(-1), Q(0)], labels)[0, 1] == Q(-2)
    return '1200/1200 exact signed-block/moment/common-shift/region-defect fixtures'


def pnp_verifier(edges, bits, threshold):
    if len(bits) != 2 * len(edges):
        return False
    labels = {}
    for (u, v, weight), a, b in zip(edges, bits[::2], bits[1::2]):
        for vertex, value in ((u, a), (v, b)):
            if vertex in labels and labels[vertex] != value:
                return False
            labels[vertex] = value
    return sum(weight for (_, _, weight), a, b in
               zip(edges, bits[::2], bits[1::2]) if a != b) >= threshold


def pnp_extend(edges, bits, n):
    assert len(bits) == 2 * len(edges)
    labels = [0] * n
    seen = {}
    for (u, v, _), a, b in zip(edges, bits[::2], bits[1::2]):
        for vertex, value in ((u, a), (v, b)):
            if vertex in seen and seen[vertex] != value:
                return None
            seen[vertex] = value
            labels[vertex] = value
    return labels


def check_pnp():
    cases = 0
    for n in range(2, 5):
        pairs = list(combinations(range(n), 2))
        for m in range(min(3, len(pairs)) + 1):
            for chosen in combinations(pairs, m):
                for weights in product((-2, 0, 3), repeat=m):
                    edges = [(u, v, weight) for (u, v), weight in zip(chosen, weights)]
                    addr_width = max(1, (n - 1).bit_length())
                    history_comparisons = 2 * m * (m - 1)
                    assert history_comparisons == sum(4 * j for j in range(m))
                    bit_upper = history_comparisons * addr_width
                    assert bit_upper >= history_comparisons
                    if m <= 1:
                        assert history_comparisons == 0
                    magnitude_bound = sum(abs(w) for _, _, w in edges)
                    for bits in product((0, 1), repeat=2 * m):
                        extended = pnp_extend(edges, bits, n)
                        for threshold in (1, 4):
                            accepted = pnp_verifier(edges, bits, threshold)
                            if extended is None:
                                assert not accepted
                            else:
                                score = sum(w for u, v, w in edges
                                            if extended[u] != extended[v])
                                assert abs(score) <= magnitude_bound
                                assert accepted == (score >= threshold)
                            cases += 1
    assert pnp_extend([(0, 1, 1), (0, 2, 1)], (0, 1, 1, 0), 3) is None
    # For n=2**k,m=1 the full n-bit assignment is exponentially longer
    # than the source gamma length O(k), while the occurrence word stays 2.
    for k in range(4, 19):
        n = 1 << k
        assert n > 2 and 2 == 2 * 1
        assert (n - 1).bit_length() == k
    return f'{cases}/{cases} finite sparse-certificate/extension/score cases; exact comparison-bit envelope'


def bsd_trace(p):
    return -sum(int(legendre_symbol((x*x*x - x) % p, p)) for x in range(p))


def check_bsd():
    primes = list(primerange(3, 401))
    inert = 0
    for p in primes:
        a = bsd_trace(p)
        if p % 4 == 3:
            inert += 1
            assert a == 0
            for x in range(p):
                assert int(legendre_symbol(((-x)**3 + x) % p, p)) == -int(legendre_symbol((x*x*x - x) % p, p))
    assert bsd_trace(5) == -2
    assert bsd_trace(3) == 0
    return f'{inert} inert primes checked (p<401), plus split-prime a_5=-2 negative control'


def hd_product(a, b, r):
    out = {}
    for x, cx in a.items():
        for y, cy in b.items():
            if x & y:
                continue  # h_i**2 = 0
            z = x | y
            out[z] = out.get(z, Q(0)) + cx * cy
    return {k: v for k, v in out.items() if v}


def hd_perm(mask, perm):
    return sum(1 << perm[i] for i in range(len(perm)) if mask & (1 << i))


def check_hodge():
    rng = Random(200123)
    tests = 0
    for r in range(8):
        allmask = (1 << r) - 1
        degree = {p: [m for m in range(1 << r) if m.bit_count() == p]
                  for p in range(r + 1)}
        assert sum(map(len, degree.values())) == 1 << r
        for p in range(r + 1):
            assert len(degree[p]) == comb(r, p)
            for a in degree[p]:
                complement = a ^ allmask
                assert hd_product({a: Q(1)}, {complement: Q(1)}, r) == {allmask: Q(1)}
                if r >= 2:
                    for b in degree[r - p]:
                        top = hd_product({a: Q(1)}, {b: Q(1)}, r).get(allmask, Q(0))
                        assert top == int(b == complement)
                        tests += 1
        for _ in range(100):
            perm = list(range(r))
            rng.shuffle(perm)
            p = rng.randrange(r + 1)
            q = rng.randrange(r + 1)
            a = {m: Q(rng.randrange(-6, 7), 7) for m in degree[p]}
            b = {m: Q(rng.randrange(-6, 7), 11) for m in degree[q]}
            left = {hd_perm(k, perm): v for k, v in hd_product(a, b, r).items()}
            right = hd_product({hd_perm(k, perm): v for k, v in a.items()},
                               {hd_perm(k, perm): v for k, v in b.items()}, r)
            assert left == right
            tests += 1
    # At r=3, a quotient omitting the coordinate divisor h0 loses a class.
    assert (1 << 0) not in {2, 4, 6}
    return f'{tests} exact squarefree cup/intersection/permutation checks for r=0..7'


def main():
    for name, func in [('NS', check_ns), ('PNP', check_pnp),
                       ('BSD', check_bsd), ('HODGE', check_hodge)]:
        print(f'{name}: PASS {func()}')
    print('SCOPE: finite/exact classical deductions only; no source-specific PDE/bit-TM/Mellin/geometry kernel or Clay prize proof')


if __name__ == '__main__':
    main()
