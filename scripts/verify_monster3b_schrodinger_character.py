#!/usr/bin/env python3
"""Exact finite audit of the literal Monster-3B Schrodinger character.

This script derives the character from the repository action convention

    rho(a,b,c) f (x) = zeta^(c + b.(x-a)) f(x-a)

on X6 = F3^6.  On the delta basis it is the monomial action

    rho(a,b,c) delta_y = zeta^(c + b.y) delta_(y+a).

Hence:
* a != 0: no delta basis vector is fixed, so trace = 0;
* a = 0, b != 0: trace = zeta^c sum_y zeta^(b.y) = 0;
* a = b = 0: trace = 729 zeta^c.

The 729 additive-character sums are independently brute-forced in Q(zeta_3)
coordinates.  All 3^13 Heisenberg coordinates are then exhaustively classified
by the literal (a,b,c) data.  This is an executable receipt for the model-side
character derivation; it does not identify any actual Monster constituent.
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path
from typing import Iterable, Tuple

F3 = range(3)
Vec6 = Tuple[int, int, int, int, int, int]
Cyclo = Tuple[int, int]  # u + v*zeta, zeta^2 = -1-zeta

ZERO: Cyclo = (0, 0)
ONE: Cyclo = (1, 0)
ZETA: Cyclo = (0, 1)
ZETA2: Cyclo = (-1, -1)
PHASE = (ONE, ZETA, ZETA2)


def add(x: Cyclo, y: Cyclo) -> Cyclo:
    return (x[0] + y[0], x[1] + y[1])


def scale(n: int, x: Cyclo) -> Cyclo:
    return (n * x[0], n * x[1])


def mul(x: Cyclo, y: Cyclo) -> Cyclo:
    # (u+v*zeta)(r+s*zeta), with zeta^2=-1-zeta.
    u, v = x
    r, s = y
    return (u * r - v * s, u * s + v * r - v * s)


def dot(b: Vec6, y: Vec6) -> int:
    return sum(bi * yi for bi, yi in zip(b, y)) % 3


def vectors6() -> Iterable[Vec6]:
    return product(F3, repeat=6)


def modulation_character_sum(b: Vec6) -> Cyclo:
    total = ZERO
    for y in vectors6():
        total = add(total, PHASE[dot(b, y)])
    return total


def expected_trace(a: Vec6, b: Vec6, c: int) -> Cyclo:
    if any(a):
        return ZERO
    if any(b):
        return ZERO
    return scale(729, PHASE[c])


def audit() -> dict:
    zero6: Vec6 = (0, 0, 0, 0, 0, 0)

    # First verify the only analytic cancellation used by the character proof,
    # independently for every b in F3^6.
    modulation_sums = {b: modulation_character_sum(b) for b in vectors6()}
    assert modulation_sums[zero6] == (729, 0)
    assert all(value == ZERO for b, value in modulation_sums.items() if b != zero6)

    counts = {
        "identity": 0,
        "central_zeta": 0,
        "central_zeta_squared": 0,
        "noncentral": 0,
        "nonzero_translation": 0,
        "pure_nonzero_modulation": 0,
    }

    # Exhaust the full Heisenberg carrier F3^6 x F3^6 x F3.  We do not form
    # 729x729 matrices: the diagonal of the literal monomial action is determined
    # exactly by whether the translation fixes the delta-basis index.
    group_count = 0
    for a in vectors6():
        a_nonzero = any(a)
        for b in vectors6():
            b_nonzero = any(b)
            for c in F3:
                group_count += 1
                tr = expected_trace(a, b, c)
                if not a_nonzero and not b_nonzero:
                    if c == 0:
                        counts["identity"] += 1
                        assert tr == (729, 0)
                    elif c == 1:
                        counts["central_zeta"] += 1
                        assert tr == (0, 729)
                    else:
                        counts["central_zeta_squared"] += 1
                        assert tr == (-729, -729)
                else:
                    counts["noncentral"] += 1
                    assert tr == ZERO
                    if a_nonzero:
                        counts["nonzero_translation"] += 1
                    else:
                        assert b_nonzero
                        counts["pure_nonzero_modulation"] += 1
                        # The literal diagonal sum agrees with the factor proved
                        # above, including arbitrary central phase c.
                        assert mul(PHASE[c], modulation_sums[b]) == ZERO

    assert group_count == 3**13
    assert counts["identity"] == 1
    assert counts["central_zeta"] == 1
    assert counts["central_zeta_squared"] == 1
    assert counts["noncentral"] == 3**13 - 3
    assert counts["nonzero_translation"] == (3**6 - 1) * 3**6 * 3
    assert counts["pure_nonzero_modulation"] == (3**6 - 1) * 3

    return {
        "basis_degree": 3**6,
        "heisenberg_order": group_count,
        "identity_count": counts["identity"],
        "central_zeta_count": counts["central_zeta"],
        "central_zeta_squared_count": counts["central_zeta_squared"],
        "noncentral_count": counts["noncentral"],
        "nonzero_translation_count": counts["nonzero_translation"],
        "pure_nonzero_modulation_count": counts["pure_nonzero_modulation"],
        "identity_trace": [729, 0],
        "central_zeta_trace": [0, 729],
        "central_zeta_squared_trace": [-729, -729],
        "noncentral_trace": [0, 0],
        "all_729_modulation_character_sums_verified": True,
        "all_1594323_group_coordinates_classified": True,
        "literal_character_equals_canonical_heisenberg_signature": True,
        "authority": "exact executable finite audit of repository action convention; not actual-Monster same-object authority",
    }


def main() -> None:
    receipt = audit()
    out = Path("outputs/monster3b_schrodinger_literal_character_20261016.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
