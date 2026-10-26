#!/usr/bin/env python3
"""Same-object Hatcher meridian orientation/basing/bit-order audit.

Classical source: Hatcher, Algebraic Topology Example 2B.2 pp171-172,
parent circle maps to commutator of linked child-generator loops.
This establishes the pi1 WORD; a concrete source geometric loop is
STILL required. Standard free homotopy changes the based word by
common conjugacy, reversing orientation gives group inverse.

Prior repository owners: Agda horn #1244 source 3-copy C3 and central
basing paths; neutrino #1247 selected W; Agda #1249 / Lean #84
norm/spectral consequences. Exotic #1254 / Lean #86 discovered the
chronological prepend/append orientation issue; the already-owned
AlexanderHornedBinaryPadicCylinderExact.chronological reversal is
REUSED as an existing mathematical interface, not re-attributed here.

New: exact free-word COMMON-whisker + inversion invariance controls,
explicit newest-first/chronological comparison, and a severe
independently-whiskered sibling negative control. These identities
permit flat norm certification up to COMMON conjugation/inversion
once the genuine Hatcher generator map has been produced; do not
treat arbitrary independently whiskered children as equivalent.

Neither this audit nor its Lean scalar consumer identifies a literal
Euclidean Hatcher meridian, based Stokes homotopy or physical field.
"""
from itertools import product


def reduce_word(word):
    out = []
    for letter in word:
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def multiply(a, b):
    return reduce_word(a + b)


def invert(a):
    return tuple(-x for x in reversed(a))


def conjugate(g, a):
    return multiply(multiply(g, a), invert(g))


def commutator(a, b):
    return multiply(multiply(multiply(a, b), invert(a)), invert(b))


words_a = ((1,), (1, 2, -1), (2, 1, 3))
words_b = ((2,), (3, -2, 1), (4, 2, -3))
whiskers = ((), (3,), (-3, 4, -2, 3))
for a, b, g in product(words_a, words_b, whiskers):
    c = commutator(a, b)
    assert invert(c) == commutator(b, a)
    assert commutator(conjugate(g, a), conjugate(g, b)) == conjugate(g, c)
    assert commutator(invert(a), invert(b)) == conjugate(invert(multiply(a, b)), c)
    assert conjugate(g, invert(c)) == invert(conjugate(g, c))
print("PASS 27 exact free-group triples, four whole-word orientation/basing identities")

for n in range(1, 8):
    for chronological_bits in product((0, 1), repeat=n):
        newest_first = ()
        for bit in chronological_bits:
            newest_first = (bit,) + newest_first
        assert newest_first[::-1] == chronological_bits
        assert newest_first != chronological_bits or chronological_bits == chronological_bits[::-1]
print("PASS 254 exact chronological bit paths n=1..7: reverse after prepend")

# A change of whisker on just ONE child generally destroys the
# *specified* commutator equation. This matters for transported
# parent-to-child curves and especially nonflat Stokes defects.
assert commutator(conjugate((3,), (1,)), (2,)) != conjugate((3,), commutator((1,), (2,)))
print("PASS negative control: independent child whisker != whole-word conjugation")
print("OPEN actual source group-map, finite-stage avoidance and based curved source homotopy")
