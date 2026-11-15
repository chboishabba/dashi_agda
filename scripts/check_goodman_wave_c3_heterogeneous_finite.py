#!/usr/bin/env python3
"""Independent finite T16 regression; mathematical test, not an Agda kernel run.

A C3 channel permutation is a relabelling symmetry for heterogeneous
componentwise operators only when the operators are also rotated.
These are synthetic ternary input values, not measured acoustic waves.
"""
from itertools import product

def rotate3(values):
    return values[1], values[2], values[0]

def evolve(operators, values):
    return tuple(operator(value) for operator, value in zip(operators, values))

def zero(_):
    return 0

def identity(x):
    return x

def main():
    operators = zero, identity, identity
    all_states = list(product((-1, 0, 1), repeat=3))
    for state in all_states:
        left = evolve(rotate3(operators), rotate3(state))
        right = rotate3(evolve(operators, state))
        assert left == right, (state, left, right)
    failures = sum(
        evolve(operators, rotate3(state)) != rotate3(evolve(operators, state))
        for state in all_states
    )
    assert len(all_states) == 27
    assert failures == 24
    print("T16 synthetic exact: 27/27 joint-action covariance; 24/27 fixed-operator failures")
    print("No empirical physical/acoustic validation; no Agda kernel check")

if __name__ == "__main__":
    main()
