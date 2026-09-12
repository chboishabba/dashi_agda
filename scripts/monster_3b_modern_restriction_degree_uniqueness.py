#!/usr/bin/env python3
"""Static source-paid verifier for the four low-degree MN3B constituents.

Sources encoded as data obligations, not theorem imports:
- Breuer--Magaard--Wilson detailed Monster verification protocol: the accepted
  H/[1,20] restriction uses exactly four coefficient-one irreducibles among the
  95 irreducibles of degree <= 196883.
- An--Wilson, Table A.17, DOI 10.1112/S1461157009000059: complete degree
  inventory and multiplicities for Irr(3^(1+12).2.Suz.2).

This script proves only the finite degree-inventory uniqueness statement.  It
must not be read as a matrix/action/intertwiner certificate or as a substitute
for the full GAP class-function matcher.
"""

import itertools
import json

DEGREE_MULTIPLICITIES = [
    (1, 2), (143, 2), (220, 2), (364, 2), (728, 1), (780, 2), (1001, 2),
    (1144, 1), (3432, 2), (4928, 2), (5940, 2), (10010, 1), (10725, 2),
    (12012, 2), (14300, 2), (15795, 2), (17496, 1), (18954, 2),
    (20020, 4), (25025, 2), (30030, 1), (32032, 1), (40040, 2),
    (50050, 1), (54054, 2), (64064, 2), (65520, 2), (66560, 2),
    (70200, 2), (75075, 2), (79872, 2), (80080, 4), (88452, 2),
    (96228, 1), (100100, 5), (102400, 2), (113724, 1), (120120, 1),
    (122472, 1), (128128, 2), (128700, 1), (133056, 2), (137280, 2),
    (146432, 2), (159744, 1), (163800, 2), (168960, 2), (187110, 1),
    (189540, 2), (192192, 2), (193050, 2),
]

TARGET = 196883
expanded = [degree for degree, count in DEGREE_MULTIPLICITIES for _ in range(count)]

# Breuer--Magaard--Wilson's accepted H/[1,20] protocol reports 95 candidates
# of degree <= 196883.  The published An--Wilson inventory must reproduce the
# same cardinality before it can be used for this cross-source uniqueness test.
assert len(expanded) == 95

solutions = {
    tuple(sorted(expanded[i] for i in indices))
    for indices in itertools.combinations(range(len(expanded)), 4)
    if sum(expanded[i] for i in indices) == TARGET
}

expected = (143, 17496, 65520, 113724)
assert solutions == {expected}

assert 17496 == 2 * 729 * 12
assert 113724 == 2 * 729 * 78
assert 17496 + 113724 == 2 * 65610
assert 143 + 65520 == 65663
assert sum(expected) == TARGET

print(json.dumps({
    "modern_protocol_candidate_count": 95,
    "restriction_constituent_count": 4,
    "restriction_coefficients_all_one": True,
    "unique_four_constituent_degree_multiset": True,
    "solution_degrees": list(expected),
    "total_degree": TARGET,
    "paired_phase_degrees": [17496, 113724],
    "multiplicity_degrees": [12, 78],
    "paired_phase_total": 131220,
    "single_phase_total": 65610,
    "centre_trivial_total": 65663,
    "an_wilson_doi": "10.1112/S1461157009000059",
    "modern_verification_doi": "10.1016/j.jalgebra.2025.09.034",
    "oeis_authority": False,
}, sort_keys=True))
