#!/usr/bin/env python3
"""Original 13-in-27, five-in-nine symmetry used as Fourier reality codec.

Actual source owners:
- DASHI.Foundations.BalancedTernaryAntipodalOrbitExact
- DASHI.Foundations.BalancedTernaryAntipodal369OrbitHierarchyExact
- DASHI.Foundations.TernaryNineAntipodalD4SeparationExact
- DASHI.Biology.Physical.C3CubeCyclotomicFourierExact

13 means 13 PAIRS outside centre; there are 14 orbit classes in 27.
5 means 5 orbit classes in 9 (centre + four pairs).
D4 nine-cell orbits = 3; D4 irreducible representation species = 5.
Neither is identified with the five antipodal classes by cardinality.
Real Fourier fields require conjugation of opposite mode coefficients.
No arbitrary-complex compression, no full DFT4/5, NS Clay, Monster 3B.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from itertools import product
import json

CUBE27 = tuple(product((-1, 0, 1), repeat=3))
PLANE9 = tuple(product((-1, 0, 1), repeat=2))
PAIRS729 = tuple(product(CUBE27, repeat=2))
ZERO3 = (0, 0, 0)


def neg(k):
    return tuple(-x for x in k)


def representative(k):
    first = next((x for x in k if x), 0)
    return k if first >= 0 else neg(k)


def conjugate(z):
    a, b = z
    return a-b, -b


def multiply(z, w):
    a,b = z
    c,d = w
    return a*c-b*d, a*d+b*c-b*d


def add(z, w):
    return z[0]+w[0], z[1]+w[1]


def pack_hermitian(values, modes):
    """Only valid for conjugate-symmetric finite input spectra."""
    assert set(values) == set(modes)
    assert all(values[neg(k)] == conjugate(values[k]) for k in modes)
    zeros = (0,)*len(modes[0])
    assert values[zeros][1] == 0
    return {representative(k): values[k] for k in modes if k == representative(k)}


def unpack_hermitian(packed, modes):
    return {
        k: packed[representative(k)] if k == representative(k)
        else conjugate(packed[representative(k)])
        for k in modes
    }


def sample_hermitian(modes, variant=0):
    representatives = tuple(sorted(set(map(representative, modes))))
    centre = (0,)*len(modes[0])
    stored = {}
    for i, k in enumerate(representatives):
        stored[k] = (Fraction(7 + variant), Fraction(0)) if k == centre else (
            Fraction(i + 2 * variant - 9, 5), Fraction(((3 * i + variant) % 7) - 3, 11)
        )
    return unpack_hermitian(stored, modes)


def convolution(left, right):
    output = defaultdict(lambda: (Fraction(0), Fraction(0)))
    for p,q in PAIRS729:
        k = tuple(a+b for a,b in zip(p,q))
        output[k] = add(output[k], multiply(left[p], right[q]))
    return dict(output)


def audit():
    cube_reps = set(map(representative, CUBE27))
    plane_reps = set(map(representative, PLANE9))
    assert (len(cube_reps), len(plane_reps)) == (14,5)
    assert len(cube_reps - {ZERO3}) == 13
    assert len(plane_reps - {(0,0)}) == 4
    assert all(representative(neg(k)) == representative(k) for k in CUBE27)
    assert all(representative(neg(k)) == representative(k) for k in PLANE9)
    assert {(*k,0) for k in plane_reps}.issubset(cube_reps)

    left = sample_hermitian(CUBE27)
    right = {k: multiply((Fraction(3),Fraction(1)),v) for k,v in left.items()}
    # Complex multiplication by a nonreal scalar destroys Hermitian symmetry.
    assert any(right[neg(k)] != conjugate(right[k]) for k in CUBE27)
    right = sample_hermitian(CUBE27, variant=1)
    assert right != left
    assert pack_hermitian(left, CUBE27)
    assert unpack_hermitian(pack_hermitian(left, CUBE27), CUBE27) == left
    assert unpack_hermitian(pack_hermitian(right, CUBE27), CUBE27) == right

    nine = sample_hermitian(PLANE9)
    assert unpack_hermitian(pack_hermitian(nine, PLANE9), PLANE9) == nine

    compressed_left = pack_hermitian(left, CUBE27)
    compressed_right = pack_hermitian(right, CUBE27)
    compact_output = convolution(
        unpack_hermitian(compressed_left, CUBE27),
        unpack_hermitian(compressed_right, CUBE27),
    )
    output = convolution(left, right)
    assert compact_output == output
    assert len(output) == 125
    assert all(output[neg(k)] == conjugate(z) for k,z in output.items())
    output_reps = {representative(k) for k in output}
    assert len(output_reps) == 63

    plus=(1,0,0); minus=(-1,0,0)
    assert representative(plus) == representative(minus)
    assert (tuple(plus[i]+plus[i] for i in range(3))
            != tuple(minus[i]+plus[i] for i in range(3)))
    pair_reps={min((p,q),(neg(p),neg(q))) for p,q in PAIRS729}
    assert len(pair_reps)==365

    return {
        "source_orbit_counts": {
            "three_mode_plane":9, "plane_nonneutral_pairs":4, "plane_classes":5,
            "signed_mode_cube":27, "cube_nonneutral_pairs":13, "cube_classes":14,
            "ordered_input_pairs":729, "pair_nonneutral_antipodal_pairs":364,
            "pair_orbit_classes":365, "wide_product_modes":125,
            "wide_product_antipodal_classes":63
        },
        "real_coefficients": {
            "plane": "1 real zero + 4 complex = 9 real components",
            "cube": "1 real zero + 13 complex = 27 real components",
            "cube_roundtrip": True,
            "plane_roundtrip": True,
            "conjugate_closed_125_output": True,
            "packed_13_pairs_preserve_all_729_product_terms": True,
            "arbitrary_complex_27_is_losslessly_compressed": False,
        },
        "operator_cut": {
            "pair_orbit_labels_determine_true_integer_sum": False,
            "conjugate_residual_required": True,
            "d4_orbits_are_not_5_antipodal_orbit_classes": True,
        },
        "real_NS_or_clock_or_monster_claimed": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), sort_keys=True, indent=2))
