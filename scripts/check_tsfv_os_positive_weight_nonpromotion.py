#!/usr/bin/env python3
"""HIL07/S10 exact rational OS-positivity nonpromotion regression.

A strictly positive normalized probability on two configurations
can yield a negative reflected quadratic form for an involution
and antisymmetric observable.  This tests the finite control
formalized in TSVFOriginalOSPositiveWeightNotReflectionPositiveExact.
It does NOT show that the selected physical Wilson reflection fails.
"""
from fractions import Fraction

def main():
    configurations = (0, 1)
    weights = {0: Fraction(1, 2), 1: Fraction(1, 2)}
    reflect = lambda x: 1 - x
    observable = lambda x: 1 if x == 0 else -1
    assert sum(weights.values(), Fraction(0)) == 1
    assert all(weights[x] > 0 for x in configurations)
    assert all(reflect(reflect(x)) == x for x in configurations)
    quadratic = sum(
        (weights[x] * observable(reflect(x)) * observable(x)
         for x in configurations),
        Fraction(0),
    )
    assert quadratic == -1, quadratic
    print("PASS: positive normalized weights, reflection involution, OS form = -1")
    print("SCOPE: not the actual Wilson positive-time cylinder algebra")

if __name__ == "__main__":
    main()
