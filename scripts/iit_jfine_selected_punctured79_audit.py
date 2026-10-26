#!/usr/bin/env python3
"""Source-aware selected/punctured j-fine/F81/5-cube audit.
Finite arithmetic, NOT same-object biology, physics, Monster action or IIT Phi.

Owners:
- BalancedTernaryHarmonicCarrierExact and JFinePhaseQuotientFieldExact: 9 trits.
- PointedTernaryBulkExact: unmarked + nine marked = ten sheets.
- RiemannQuarticPuncturedKernel4EnumerationExact: 3^4-1 = 80 states.
- IIT ternary 5-cube F: diagonal 5-trit lost-profile with F^80=I-JP.

Chosen (not canonical under translations) D4-stable cross/corner split:
      NW  N  NE            corner: NW NE SW SE
       W  C   E            cross: C N E S W
      SW  S  SE
The five cyclic C5 profile labels are placed on C,N,E,S,W in order.
D4 keeps the CROSS SET, not the selected C5 cyclic order.
"""
from __future__ import annotations
from collections import Counter
from hashlib import sha256
from itertools import product
from math import gcd
import json
import argparse

P = 3
ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)
POLY = (2, 1, 0, 0, 1)  # x^4+x+2, irreducible over F3
CROSS = (4, 1, 5, 7, 3)     # C N E S W
CORNERS = (0, 2, 6, 8)     # NW NE SW SE


def join(profile: tuple[int, ...], residue: tuple[int, ...]) -> tuple[int, ...]:
    if len(profile) != 5 or len(residue) != 4:
        raise ValueError("Expected 5+4 trits")
    out = [0] * 9
    for i, v in zip(CROSS, profile):
        out[i] = v
    for i, v in zip(CORNERS, residue):
        out[i] = v
    if any(v not in (0, 1, 2) for v in out):
        raise ValueError("Not F3 trits")
    return tuple(out)


def split(sheet):
    assert len(sheet) == 9
    return tuple(sheet[i] for i in CROSS), tuple(sheet[i] for i in CORNERS)


def add(a, b):
    return tuple((x + y) % P for x, y in zip(a, b))


def multiply(a, b):
    poly = [0] * 7
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            poly[i + j] = (poly[i + j] + x*y) % P
    for i in range(6, 3, -1):
        k = poly[i]
        for j in range(4):
            poly[i - 4 + j] = (poly[i - 4 + j] - k*POLY[j]) % P
    return tuple(poly[:4])


def power(a, exponent):
    if exponent < 0:
        raise ValueError("use q-2 inversion for nonzero")
    result = ONE
    while exponent:
        if exponent & 1:
            result = multiply(result, a)
        a = multiply(a, a)
        exponent >>= 1
    return result


def rotation90(sheet):
    # Original D4 sheet coordinates: a b c / d e f / g h i
    a,b,c,d,e,f,g,h,i = sheet
    return (g,d,a,h,e,b,i,f,c)


def reflection(sheet):
    a,b,c,d,e,f,g,h,i = sheet
    return (c,b,a,f,e,d,i,h,g)


def audit():
    profiles = tuple(product(range(P), repeat=5))
    residuals = tuple(product(range(P), repeat=4))
    assert len(profiles) == 243
    assert len(residuals) == 81
    assert 243 * 81 == 19683
    assert (9 + 1)*len(profiles)*len(residuals) == 196830
    assert 196830 + 53 == 196883
    assert 196830 + 54 == 196884
    # Exhaustive two-sided source chart on all 19683 fine states.
    for sheet in product(range(P), repeat=9):
        cross, corner = split(sheet)
        assert join(cross, corner) == sheet
    for p, r in product(profiles, residuals):
        assert split(join(p, r)) == (p, r)
    # D4-stable decomposition as SETS, not an equivariant 5-cycle label map.
    for i in CROSS:
        sheet = tuple(int(j == i) for j in range(9))
        assert split(rotation90(sheet))[1] == (0,) * 4
        assert split(reflection(sheet))[1] == (0,) * 4
    for i in CORNERS:
        sheet = tuple(int(j == i) for j in range(9))
        assert split(rotation90(sheet))[0] == (0,) * 5
        assert split(reflection(sheet))[0] == (0,) * 5
    # Multiplication table builds the field GF(3^4) from an irreducible quartic.
    # Every nonzero element has multiplicative order dividing 80.
    assert len(set(multiply(a,b) for a,b in product(residuals,residuals))) == 81
    assert all(power(a,80) == ONE and multiply(a,power(a,79)) == ONE
               for a in residuals if a != ZERO)
    assert all(multiply(a,b) != ZERO for a,b in product(residuals[1:],residuals[1:])
               if a != ZERO and b != ZERO)
    # Recover the unique F9 subfield by x^9=x; affine group has 9*8=72 maps.
    f9 = tuple(a for a in residuals if power(a,9) == a)
    assert len(f9) == 9
    affine = {tuple(add(multiply(a,x),b) for x in f9)
              for a,b in product(f9,f9) if a != ZERO}
    assert len(affine) == 72
    # Every nontrivial fifth root belongs to F81, but not to F9.
    roots = tuple(a for a in residuals if power(a,5)==ONE)
    assert len(roots) == 5
    assert len(set(roots).intersection(f9)) == 1
    # The 3D 5-torus operator eigenvalues are sums of three fifth roots.
    multiplicity = Counter()
    for a,b,c in product(roots,repeat=3):
        value = add(add(a,b),c)
        if value == ZERO:
            multiplicity[0] += 1
            continue
        order = next(i for i in (1,2,4,5,8,10,16,20,40,80)
                     if power(value,i)==ONE)
        multiplicity[order] += 1
    assert dict(multiplicity) == {0:5, 8:12, 16:12, 40:48, 80:48}
    # Inversion exponent 79 is q-2; it is NOT a Monster SSP lane.
    ssp = (2,3,5,7,11,13,17,19,23,29,31,41,47,59,71)
    assert all(79 % j for j in range(2,9)) and 79 not in ssp
    # C5 cannot embed in 9-point translation C3^2 or in AGL(1,9) (|G|=72).
    assert gcd(5,9) == gcd(5,72) == 1
    receipt = {
      "scope":"DASHI_CHOSEN_CODEC_AND_FINITE_FIELD_NOT_CONSCIOUSNESS_OR_MONSTER_REP",
      "jFine_selected_five_trits": 5, "jFine_corner_four_trits": 4,
      "selected_configurations": 243, "corner_configurations": 81,
      "jFine_states": 19683, "pointed_channels": 10, "pointed_states": 196830,
      "exhaustive_fine_codec_roundtrips": 19683,
      "D4_preserves_selected_sets_not_C5_order": True,
      "F81_irreducible_polynomial_coefficients": POLY,
      "F81_nonzero_states":80, "inverse_exponent":79,
      "F9_subfield_size":9,"AGL1_F9_order":72,
      "fifth_root_subgroup_size":5,"nontrivial_fifth_roots_in_F9":0,
      "5cube_eigenvalue_order_multiplicities": dict(sorted(multiplicity.items())),
      "5cube_minimal_retained_period":80,
      "79_is_prime":True,"79_is_SSP15_prime":False,
      "C5_natural_translation_into_C3xC3":False,
      "jFine_equals_5cube_profile_whole_carrier":False,
      "Monster_representation_identification":False,
    }
    receipt["payload_sha256"] = sha256(json.dumps(receipt,sort_keys=True).encode()).hexdigest()
    return receipt


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--json",default="")
    args=parser.parse_args()
    result=audit()
    output=json.dumps(result,sort_keys=True,indent=2)
    print(output)
    if args.json:
        with open(args.json,"w",encoding="utf-8") as f:f.write(output+"\n")
