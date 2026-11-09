#!/usr/bin/env python3
"""Exact original Y443 relator multiset split: 72+8, not a Monster iso.

Original Coxeter source: 12 squares + 11 adjacent cubes + 55 nonadjacent
squares + spider + central f_312 = 80 words, total source length 463.

72 = 8 original node squares + 8 actual edge cubes + all 55
nonadjacent pair squares + spider.
8 = remaining 4 original node squares + remaining 3 actual edge cubes
  + original f_312 central relation.

Separately 80 = 9*8+8, 71+9, 71+10=81. These cardinalities do not
supply a canonical, let alone group-equivariant, map to P1(F9),
SSP15/jCoarseFine, or the selected Monster action.

The Agda owner Y443Original72Plus8RelatorPartitionExact source-proves
the lengths; the present script additionally verifies word multiset
equality in a literal finite reference model.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path

NODES = "a b1 c1 d1 e1 b2 c2 d2 e2 b3 c3 d3".split()
EDGES = [
    ("a", "b1"), ("b1", "c1"), ("c1", "d1"), ("d1", "e1"),
    ("a", "b2"), ("b2", "c2"), ("c2", "d2"), ("d2", "e2"),
    ("a", "b3"), ("b3", "c3"), ("c3", "d3")
]
CORE_NODES = "a b1 c1 d1 e1 b2 c2 d2".split()
CORE_EDGES = [("a", "b1"), ("b1", "c1"), ("c1", "d1"), ("d1", "e1"),
              ("a", "b2"), ("b2", "c2"), ("c2", "d2"), ("a", "b3")]
TAIL_NODES = "e2 b3 c3 d3".split()
TAIL_EDGES = [("d2", "e2"), ("b3", "c3"), ("c3", "d3")]
SPIDER = ("a b1 c1 a b2 c2 a b3 c3".split()) * 10
CENTRAL = ("a b3 c3 d3 b1 c1 b2".split()) * 9


def pair_key(x, y):
    return tuple(sorted((x, y)))


def power(word, n):
    return tuple(word) * n


def main():
    source = Path(__file__).resolve().parents[1] / (
        "DASHI/Moonshine/Y443CoxeterPresentationExact.agda"
    )
    if source.exists():
        text = source.read_text()
        for anchor in ("monsterRelators = doubleMonsterRelators ++",
                       "centralInvolutionRelator = powerWord centralBase 9",
                       "spiderRelator = powerWord spiderBase 10",
                       "coxeterRelatorCount : length coxeterRelators ≡ 78"):
            assert anchor in text, (source, anchor)

    pairs = list(combinations(NODES, 2))
    eset = set(map(lambda e: pair_key(*e), EDGES))
    assert len(eset) == 11
    nonedges = [p for p in pairs if pair_key(*p) not in eset]
    assert len(nonedges) == 55
    def pair_relator(p):
        return power(p, 3 if pair_key(*p) in eset else 2)

    all_words = ([power([n],2) for n in NODES] +
                 [pair_relator(p) for p in pairs] +
                 [tuple(SPIDER), tuple(CENTRAL)])
    retained = ([power([n],2) for n in CORE_NODES] +
                [pair_relator(p) for p in CORE_EDGES] +
                [pair_relator(p) for p in nonedges] +
                [tuple(SPIDER)])
    residual = ([power([n],2) for n in TAIL_NODES] +
                [pair_relator(p) for p in TAIL_EDGES] +
                [tuple(CENTRAL)])
    assert (len(all_words), len(retained), len(residual)) == (80,72,8)
    assert (sum(map(len,all_words)), sum(map(len,all_words[:-1])))==(463,400)
    assert Counter(map(tuple,all_words)) == Counter(map(tuple,retained+residual))
    assert len(CORE_NODES)==8 and len(CORE_EDGES)==8
    assert len(TAIL_NODES)==4 and len(TAIL_EDGES)==3
    assert 9*8+8 == 71+9 == 80 and 71+10==81
    print("PASS: original Y443 80 relators EXACTLY partition 72 + 8 as a word multiset")
    print("PASS: 55 nonedges + 8 involutions + 8 edge cubes + spider = 72")
    print("PASS: 4 involutions + 3 edge cubes + central quotient = 8")
    print("PASS: source word lengths 400 / 463, all 80 original words preserved")
    print("NO CLAIM: projective F9 equivariance, selected-group kernel, Monster iso")


if __name__=="__main__":
    main()
