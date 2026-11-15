#!/usr/bin/env python3
"""Exact root-set audit for E8 -> E6 x A2 and E8 -> E7 x A1.

Executable DASHI evidence only; not an Agda/Lean kernel proof.

The script constructs the standard 240 doubled-coordinate E8 roots and checks:

E6 x A2 root split:
  240 = 72 + 6 + 81 + 81
      = 72 + 6 + (3*27) + (3*27)

E7 x A1 root split:
  240 = 126 + 2 + 56 + 56.

Adding Cartan dimensions reproduces the adjoint branch dimensions:
  248 = 78 + 8 + 81 + 81
  248 = 133 + 3 + 56 + 56.

The 27- and 56-sized fibres are root-set sectors. This audit does not by
itself construct the corresponding E6/E7 representation actions or identify
DASHI's independent Albert/Freudenthal carriers with those representations.
"""

from collections import Counter
from itertools import product


def standard_doubled_e8_roots():
    roots = []
    for i in range(8):
        for j in range(i + 1, 8):
            for si, sj in product((-2, 2), repeat=2):
                x = [0] * 8
                x[i], x[j] = si, sj
                roots.append(tuple(x))
    for signs in product((-1, 1), repeat=8):
        if sum(s < 0 for s in signs) % 2 == 0:
            roots.append(tuple(signs))
    assert len(roots) == len(set(roots)) == 240
    return roots


def e6_a2_split(roots):
    e6 = [r for r in roots if r[5:] in ((-1,-1,-1), (0,0,0), (1,1,1))]
    a2 = [r for r in roots if sorted(r[5:]) == [-2,0,2]]
    mixed = [r for r in roots if r not in e6 and r not in a2]
    positive = [r for r in mixed if sum(r[5:]) > 0]
    negative = [r for r in mixed if sum(r[5:]) < 0]

    pos_patterns = (
        {(-1,1,1), (2,0,0), (0,2,2)},
        {(1,-1,1), (0,2,0), (2,0,2)},
        {(1,1,-1), (0,0,2), (2,2,0)},
    )
    neg_patterns = (
        {(1,-1,-1), (-2,0,0), (0,-2,-2)},
        {(-1,1,-1), (0,-2,0), (-2,0,-2)},
        {(-1,-1,1), (0,0,-2), (-2,-2,0)},
    )

    def fibre(r, patterns):
        hits = [i for i, p in enumerate(patterns) if r[5:] in p]
        assert len(hits) == 1
        return hits[0]

    assert len(e6) == 72
    assert len(a2) == 6
    assert len(positive) == len(negative) == 81
    assert Counter(fibre(r, pos_patterns) for r in positive) == Counter({0:27,1:27,2:27})
    assert Counter(fibre(r, neg_patterns) for r in negative) == Counter({0:27,1:27,2:27})
    assert 72 + 6 + 81 + 81 == 240
    assert (72 + 6) + (6 + 2) + 81 + 81 == 248
    return len(e6), len(a2), len(positive), len(negative)


def e7_a1_split(roots):
    e7 = [r for r in roots if r[6] == r[7]]
    a1 = [r for r in roots if r[6:] in ((2,-2), (-2,2))]
    mixed = [r for r in roots if r not in e7 and r not in a1]
    positive56 = [r for r in mixed if r[6:] in ((0,-2), (1,-1), (2,0))]
    negative56 = [r for r in mixed if r[6:] in ((-2,0), (-1,1), (0,2))]

    assert len(e7) == 126
    assert len(a1) == 2
    assert len(positive56) == len(negative56) == 56
    assert len(e7) + len(a1) + len(positive56) + len(negative56) == 240
    assert (126 + 7) + (2 + 1) + 56 + 56 == 248
    return len(e7), len(a1), len(positive56), len(negative56)


def main():
    roots = standard_doubled_e8_roots()
    e6 = e6_a2_split(roots)
    e7 = e7_a1_split(roots)
    print("E8 roots                 = 240")
    print("E6 x A2 root split       =", e6, "= 72 + 6 + 81 + 81")
    print("E6 mixed fibres          = 3x27 + 3x27")
    print("E7 x A1 root split       =", e7, "= 126 + 2 + 56 + 56")
    print("adjoint dimensions       = 248 = 78+8+81+81 = 133+3+56+56")
    print("RUN_TERMINAL COMPLETE")


if __name__ == "__main__":
    main()
