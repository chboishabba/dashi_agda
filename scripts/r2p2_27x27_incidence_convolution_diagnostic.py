#!/usr/bin/env python3
"""Exact 27×27 integer-mode incidence and 5-grid INDEX recovery.

This uses existing DASHI T^3/T^6 semantics for *mode labels*. It does
NOT implement a DFT, continuous NS equations, a GF(729) field action, or
the physical Ma/R2P2 clock Hamiltonian. Source hierarchy:
Patterson/Orszag Fourier dealiasing, Lambert-Reneuve-Augier (2026),
then DASHI original codec/NS integer-mode and current branch adapters.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
import json

MODE = (-1, 0, 1)
CUBE27 = tuple(product(MODE, repeat=3))
PAIRS729 = tuple(product(CUBE27, repeat=2))
WIDE125 = tuple(product((-2, -1, 0, 1, 2), repeat=3))


def integer_sum(p: tuple[int, int, int], q: tuple[int, int, int]):
    return tuple(x + y for x, y in zip(p, q))


def six_trits(pair):
    return (*pair[0], *pair[1])


def pair_from_six_trits(trits):
    if len(trits) != 6 or any(t not in MODE for t in trits):
        raise ValueError("six signed trits required")
    return (tuple(trits[:3]), tuple(trits[3:]))


def inside_cube(k):
    return all(abs(v) <= 1 for v in k)


def grid5_index(k):
    if any(abs(v) > 2 for v in k):
        raise ValueError("outside exact quadratic [-2,2]^3 support")
    return tuple((v + 2) % 5 for v in k)


def recover_grid5(encoded):
    if any(v not in range(5) for v in encoded):
        raise ValueError("grid index outside 0..4")
    return tuple(v - 2 for v in encoded)


def fold3(k):
    return tuple((v + 1) % 3 - 1 for v in k)


def exact_convolution(amplitude):
    output = Counter()
    for p, q in PAIRS729:
        output[integer_sum(p, q)] += amplitude[p] * amplitude[q]
    return output


def index_recovered_five_convolution(amplitude):
    output = Counter()
    for p, q in PAIRS729:
        k = integer_sum(p, q)
        output[recover_grid5(grid5_index(k))] += amplitude[p] * amplitude[q]
    return output


def aliased_three_convolution(amplitude):
    output = Counter()
    for p, q in PAIRS729:
        output[fold3(integer_sum(p, q))] += amplitude[p] * amplitude[q]
    return output


def audit():
    assert len(CUBE27) == len(set(CUBE27)) == 27
    assert len(PAIRS729) == len(set(PAIRS729)) == 729
    all_six = tuple(map(six_trits, PAIRS729))
    assert len(set(all_six)) == 729
    assert all(pair_from_six_trits(s) == p for s, p in zip(all_six, PAIRS729))

    inside = sum(inside_cube(integer_sum(p, q)) for p, q in PAIRS729)
    assert inside == 343 and len(PAIRS729) - inside == 386
    assert all(recover_grid5(grid5_index(wide)) == wide for wide in WIDE125)
    assert len({grid5_index(wide) for wide in WIDE125}) == 125

    profiles = {
        "zero": {m: 0 for m in CUBE27},
        "one": {m: 1 for m in CUBE27},
        "indexed_mod5": {m: i % 5 for i, m in enumerate(CUBE27)},
        "single_x_plus": {m: int(m == (1, 0, 0)) for m in CUBE27},
    }
    checks = {}
    for name, amp in profiles.items():
        exact = exact_convolution(amp)
        recovered = index_recovered_five_convolution(amp)
        assert all(exact[k] == recovered[k] for k in WIDE125)
        assert set(exact) <= set(WIDE125) and set(recovered) <= set(WIDE125)
        checks[name] = sum(exact.values())

    example = profiles["single_x_plus"]
    exact = exact_convolution(example)
    aliased = aliased_three_convolution(example)
    assert exact[(2, 0, 0)] == 1 and exact[(-1, 0, 0)] == 0
    assert aliased[(-1, 0, 0)] == 1

    return {
        "scope": "finite exact index arithmetic, not a full DFT",
        "signed_mode_cube_count": 27,
        "unique_ordered_pairs_and_six_trit_codes": 729,
        "inside_integer_sum_window": inside,
        "outside_integer_sum_window": 386,
        "distinct_five_grid_indices": len({grid5_index(w) for w in WIDE125}),
        "all_coefficients_theorem": "Agda source quantifies over any Nat-valued amplitude; kernel unverified",
        "finite_profiles_compared": checks,
        "three_grid_alias_example": {
            "true_output": [2, 0, 0],
            "spurious_folded_output": [-1, 0, 0],
            "true_retained_coefficient": 0,
            "folded_retained_coefficient": 1,
        },
        "claimed_full_DFT_or_NS_solution": False,
        "claimed_GF729_or_Monster_action": False,
        "claimed_R2P2_physical_measurement": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), sort_keys=True, indent=2))
