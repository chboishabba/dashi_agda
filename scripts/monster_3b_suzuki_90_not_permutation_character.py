#!/usr/bin/env python3
"""Exact cyclotomic obstruction to a 90-point permutation action.

This verifier consumes one source-paid hypothesis from the Monster/Suzuki lane:
the degree-12 and degree-78 multiplicity factors are faithful irreducible
representations of 6.Suz.  For a nonidentity central element of order 3,
Schur's lemma then forces each factor to act by zeta or zeta^2, never by 1.

We represent Q(zeta) in the basis (1, zeta), using

    zeta^2 = -1 - zeta.

A permutation character takes a nonnegative integer value on every group
element (the number of fixed basis labels).  In this basis an integer has zero
zeta coefficient.  We exhaust the four nontrivial phase assignments for the
12- and 78-dimensional factors and show that the total zeta coefficient is
never zero.

This proves only the character-level obstruction.  It does not construct the
actual Monster multiplicity action, identify an absolute zeta orientation, or
replace the source obligation that the two factors are faithful.
"""

from __future__ import annotations

import json
from itertools import product

DEGREES = (12, 78)

# pair (a,b) means a + b*zeta
PHASES = {
    "zeta": (0, 1),
    "zeta^2": (-1, -1),
}


def scale(n: int, x: tuple[int, int]) -> tuple[int, int]:
    return n * x[0], n * x[1]


def add(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    return x[0] + y[0], x[1] + y[1]


cases = []
for phase12, phase78 in product(PHASES, repeat=2):
    value = add(scale(DEGREES[0], PHASES[phase12]), scale(DEGREES[1], PHASES[phase78]))
    cases.append(
        {
            "phase12": phase12,
            "phase78": phase78,
            "rational_coefficient": value[0],
            "zeta_coefficient": value[1],
            "is_integer": value[1] == 0,
        }
    )

all_noninteger = all(case["zeta_coefficient"] != 0 for case in cases)
assert all_noninteger

# Explicit expected coefficients are useful regression guards against an
# accidental change in the cyclotomic convention or degree pair.
expected = {
    ("zeta", "zeta"): (0, 90),
    ("zeta", "zeta^2"): (-78, -66),
    ("zeta^2", "zeta"): (-12, 66),
    ("zeta^2", "zeta^2"): (-90, -90),
}
for case in cases:
    key = (case["phase12"], case["phase78"])
    assert (case["rational_coefficient"], case["zeta_coefficient"]) == expected[key]

print(
    json.dumps(
        {
            "degrees": list(DEGREES),
            "central_element_order": 3,
            "requires_source_paid_faithful_nontrivial_central_phase": True,
            "phase_cases": cases,
            "all_nontrivial_phase_assignments_noninteger": all_noninteger,
            "permutation_character_compatible": False,
            "barraclough_wilson_doi": "10.1112/S1461157000001352",
            "serre_doi": "10.1007/978-1-4684-9458-7",
            "group_representation_qid": "Q1055807",
            "representation_character_qid": "Q600043",
            "group_representation_dewey": "512.22",
            "finite_group_dewey": "512.23",
            "oeis_authority": False,
        },
        sort_keys=True,
    )
)
