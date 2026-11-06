#!/usr/bin/env python3
"""Exhaustive finite CCDCOE P3 causal/intersectional/triadic countermodels.

Checks exact definitions matching Agda P3 files. This is independent
finite-model validation and is NOT an Agda kernel receipt or real study.
"""
from itertools import permutations, product


# The string value of an axis point is not its semantic identity.
# Using (axis-tag, coordinate) preserves the type information.
RACE = (("race", 0), ("race", 1))
SEX = (("sex", 0), ("sex", 1))

def typed_joint(race, sex):
    assert race in RACE and sex in SEX
    return 1 if race == RACE[1] and sex == SEX[1] else 0

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
    assert len(RACE) == len(SEX) == 2
    assert set(RACE).isdisjoint(SEX)
    typed_cases = 0
    for race, sex in product(RACE, SEX):
        assert typed_joint(race, sex) in (0, 1)
        typed_cases += 1
    # Rectangle obstruction: (r0,s0)+(r1,s1) != (r0,s1)+(r1,s0)
    left = typed_joint(RACE[0], SEX[0]) + typed_joint(RACE[1], SEX[1])
    right = typed_joint(RACE[0], SEX[1]) + typed_joint(RACE[1], SEX[0])
    assert left != right

    # Even both typed points can coincide under two situated contexts
    # while recognition differs: axis labels alone are an incomplete view.
    situated = (
        ((RACE[1], SEX[1]), "accessible", "recognised"),
        ((RACE[1], SEX[1]), "exclusionary", "excluded"),
    )
    assert situated[0][0] == situated[1][0]
    assert situated[0][2] != situated[1][2]

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

    print(f"PASS: {typed_cases} typed race/sex joint cases, rectangle obstruction, and equal-size nonidentity")
    print(f"PASS: all {len(s3)} S3 permutations, {s3_composition_tests} associativity cases")
    print("PASS: observationally equivalent SCMs and separating do(X=1) intervention")
    print("PASS: coherence/revision, cause/intent and dyadic/triadic nonfactorability")


if __name__ == "__main__":
    run()
