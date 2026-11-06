#!/usr/bin/env python3
"""Independent finite controls for signed PNF/SSP/Karp/Cheeger distinctions.

The original mathematical owners are separate:
- Karp (1972): signed weighted decision MAX CUT.
- DASHI PNF source: +1 partial, +3 noTypedMeet, -9 contradiction Delta0.
- Kunegis et al. (2010): signed abs-degree Laplacian D_|W| - W.
- Shao/Yang/Zhang (2016; 2025): signless nonlinear 1-Laplacian,
  dual Cheeger and a ternary algorithm, *not* a universal Karp certificate.

This script is finite corroboration only. It never checks an Agda theorem,
a general polynomial machine clock or an approximation-ratio result.
"""
from itertools import combinations, product


def edges_for_partition(values):
    return [(i, j, 4 * values[i] * values[j])
            for i, j in combinations(range(len(values)), 2)]


def cut(edges, labels):
    return sum(w for i, j, w in edges if labels[i] != labels[j])


def pnf_delta(x):
    a, b, c = x
    return (-8*a - b + 9*c, -a + 4*b - 3*c, 9*a - 3*b - 6*c)


def frustration(edges, labels):
    return sum((w if labels[i] != labels[j] else 0)
               if w >= 0 else (-w if labels[i] == labels[j] else 0)
               for i, j, w in edges)


def signed_psd_energy(edges, labels):
    s = tuple(1 if b else -1 for b in labels)
    return sum(abs(w) * (s[i] - (1 if w >= 0 else -1)*s[j])**2
               for i, j, w in edges)


def ternary_edges(edges, labels):
    original = sum(w*(labels[i]-labels[j])**2 for i, j, w in edges)
    induced = sum(w*(labels[i]-labels[j])**2 for i, j, w in edges
                  if labels[i] != 0 and labels[j] != 0)
    bleed = sum(w*(labels[i]-labels[j])**2 for i, j, w in edges
                if (labels[i] == 0) != (labels[j] == 0))
    return original, induced, bleed


def test_pnf():
    pnf = ((0, 1, 1), (1, 2, 3), (2, 0, -9))
    for labels in product((-1, 1), repeat=3):
        delta = pnf_delta(labels)
        q = sum(x*y for x, y in zip(labels, delta))
        assert 4*cut(pnf, labels) == q
    assert pnf_delta((1, 1, 1)) == (0, 0, 0)
    assert sum(x*y for x, y in zip((1, -1, 0), pnf_delta((1, -1, 0)))) == -2
    assert sum(x*y for x, y in zip((0, 1, -1), pnf_delta((0, 1, -1)))) == 4
    # Distinguish literal signed Delta0 from PSD corrected signed matrix.
    assert signed_psd_energy(pnf, (1, -1, 1)) >= 0
    assert signed_psd_energy(pnf, (-1, -1, -1)) == 36


def test_ternary():
    pairs = tuple(product((-1, 0, 1), repeat=2))
    assert { (a-b)**2 for a, b in pairs } == {0, 1, 4}
    assert {(a,b): abs(a+b) for a,b in pairs}[(1,1)] == 2
    assert (1 - 1)**2 == 0 and abs(1+1) == 2
    count = 0
    for w in (-9, -5, -1, 0, 1, 3, 9):
        for a,b in pairs:
            e = ((0,1,w),)
            original, induced, bleed = ternary_edges(e, (a,b))
            assert original == induced + bleed
            assert abs(a+b) in (0, 1, 2)
            if (a == 0) != (b == 0):
                assert original == w
            count += 1
    return count


def test_signed():
    count = 0
    for n in range(5):
        pairs = tuple(combinations(range(n), 2))
        for weights in product((-2,-1,0,1,2), repeat=len(pairs)):
            edges = tuple((i,j,w) for (i,j),w in zip(pairs,weights))
            neg_total = sum(-w for _,_,w in edges if w < 0)
            for bits in product((False, True), repeat=n):
                assert frustration(edges,bits) == cut(edges,bits)+neg_total
                assert signed_psd_energy(edges,bits) == 4*frustration(edges,bits)
                assert signed_psd_energy(edges,bits) >= 0
                count += 1
    assert cut(((0,1,-5),),(True,False)) == -5
    assert frustration(((0,1,-5),),(True,False)) == 0
    return count


def test_e20():
    count = 0
    for n in range(6):
        for values in product((-2,-1,0,1,2), repeat=n):
            edges = edges_for_partition(values)
            assert len(edges) == n*(n-1)//2
            assert len({(i,j) for i,j,_ in edges}) == len(edges)
            positive_threshold = sum(values)**2
            for bits in product((False,True), repeat=n):
                left = sum(v for v,b in zip(values,bits) if b)
                right = sum(values)-left
                score = cut(edges,bits)
                assert score == 4 * left * right
                assert score == positive_threshold - (left-right)**2
                assert (score >= positive_threshold) == (left == right)
                count += 1
            if sum(values) == 0:
                # Historical MAX CUT requires W>0; fixed unit edge YES.
                assert cut(((0,1,1),),(True,False)) >= 1
            else:
                assert positive_threshold > 0
    return count


if __name__ == "__main__":
    test_pnf()
    ternary = test_ternary()
    signed = test_signed()
    e20 = test_e20()
    print(f"PASS PNF 8 signed field vertices; ternary {ternary} pairs; "
          f"signed {signed} weighted graph/label cases; "
          f"E20 {e20} signed Partition/finite complete graph witnesses")
