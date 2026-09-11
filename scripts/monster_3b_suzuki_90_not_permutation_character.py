#!/usr/bin/env python3
"""Exact cyclotomic obstruction to a 90-point permutation action.

The source-paid premise is deliberately minimal.  Barraclough--Wilson's
complex degree-12 representation of 6.Suz detects the central element -omega
as a nontrivial scalar.  Thus, on the relevant central C3 element, the
12-dimensional factor has phase zeta or zeta^2.  We do NOT need to assume that
the degree-78 factor is faithful: its central phase is allowed to be any of
1, zeta, or zeta^2.

We represent Q(zeta) in the basis (1, zeta), using

    zeta^2 = -1 - zeta.

A permutation character takes a nonnegative integer value on every group
element (the number of fixed basis labels).  In this basis an integer has zero
zeta coefficient.  We exhaust all six source-admissible phase assignments and
show that the total character always has nonzero zeta coefficient.

This proves only the character-level obstruction to a PURE permutation action
on ninety labels.  It does not construct the actual Monster multiplicity
action, identify an absolute zeta orientation, exclude a monomial action with
nontrivial scalar coefficients, or assert anything about the exact kernel of
the degree-78 character.
"""

from __future__ import annotations

import json
from itertools import product

DEGREES = (12, 78)

# pair (a,b) means a + b*zeta
PHASES = {
    "1": (1, 0),
    "zeta": (0, 1),
    "zeta^2": (-1, -1),
}
TWELVE_PHASES = ("zeta", "zeta^2")
SEVENTY_EIGHT_PHASES = ("1", "zeta", "zeta^2")


def scale(n: int, x: tuple[int, int]) -> tuple[int, int]:
    return n * x[0], n * x[1]


def add(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    return x[0] + y[0], x[1] + y[1]


cases = []
for phase12, phase78 in product(TWELVE_PHASES, SEVENTY_EIGHT_PHASES):
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

# Explicit expected coefficients are regression guards against accidental
# changes in the cyclotomic convention or dimensions.
expected = {
    ("zeta", "1"): (78, 12),
    ("zeta", "zeta"): (0, 90),
    ("zeta", "zeta^2"): (-78, -66),
    ("zeta^2", "1"): (66, -12),
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
            "requires_source_paid_nontrivial_twelve_phase": True,
            "requires_nontrivial_seventy_eight_phase": False,
            "phase_cases": cases,
            "all_source_admissible_phase_assignments_noninteger": all_noninteger,
            "permutation_character_compatible": False,
            "monomial_with_scalar_coefficients_excluded": False,
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
