#!/usr/bin/env python3
"""Exhaustive finite CCDCOE P3 causal/intersectional/triadic countermodels.

Checks exact definitions matching Agda P3 files. This is independent
finite-model validation and is NOT an Agda kernel receipt or real study.
"""
from itertools import permutations, product


def additive(x, y):
    return 2*x + 2*y


def joint(x, y):
    return additive(x, y) + x*y


def observed_exposure(u):
    return u


def response(model, u, x):
    return x if model == "direct" else u


def observed(model):
    return tuple((observed_exposure(u), response(model, u, observed_exposure(u)))
                 for u in (0, 1))


def intervention(model):
    return response(model, 0, 1)


def composition(left, right):
    return tuple(left[right[i]] for i in range(3))


def run():
    additive_fixtures = 0
    for x, y in product((0, 1), repeat=2):
        assert joint(x, y) == additive(x, y) + x*y
        additive_fixtures += 1
    assert additive(1, 1) == 4
    assert joint(1, 1) == 5

    s3 = tuple(permutations((0, 1, 2)))
    assert len(s3) == len(set(s3)) == 6
    assert (0, 1, 2) in s3
    assert all(composition(a, b) in s3 for a, b in product(s3, repeat=2))
    s3_composition_tests = 0
    for a, b, c in product(s3, repeat=3):
        assert composition(a, composition(b, c)) == composition(composition(a, b), c)
        s3_composition_tests += 1
    assert any(composition(a, b) != composition(b, a)
               for a, b in product(s3, repeat=2))

    assert observed("direct") == observed("common") == ((0, 0), (1, 1))
    assert intervention("direct") == 1
    assert intervention("common") == 0

    # A same-coherence observation gives no unique revisability inference.
    worlds = (("same-narrative", "contestable"),
              ("same-narrative", "self-sealed"))
    assert worlds[0][0] == worlds[1][0]
    assert worlds[0][1] != worlds[1][1]

    # Same outcome under a positive exposure does not identify purpose.
    assert {("positive-effect", "non-hostile"),
            ("positive-effect", "hostile")} == {
        ("positive-effect", intent) for intent in ("non-hostile", "hostile")
    }

    # A selected triadic face cannot be reconstructed from identical edges.
    same_dyads = ("positive", "positive", "positive")
    triads = ((same_dyads, "reciprocal"), (same_dyads, "coercive"))
    assert triads[0][0] == triads[1][0] and triads[0][1] != triads[1][1]

    print(f"PASS: {additive_fixtures} two-axis additive/interaction cases")
    print(f"PASS: all {len(s3)} S3 permutations, {s3_composition_tests} associativity cases")
    print("PASS: observationally equivalent SCMs and separating do(X=1) intervention")
    print("PASS: coherence/revision, cause/intent and dyadic/triadic nonfactorability")


if __name__ == "__main__":
    run()
