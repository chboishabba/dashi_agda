#!/usr/bin/env python3
"""CT11 exact enumerated rectangle membership and candidate counting oracle.

Uses the same descending 1..B, E-1..0 coordinates as the Agda
TwinPrimeProperPowerRectangleEnumerationExact owner. Checks that ALL
actual proper prime powers occur in the mapped value image, even when
multiple candidate coordinates map to one value. Finite tests, not
kernel proof or a completed uniform analytic estimate.
"""
from math import isqrt

def proper_prime_power(n):
    if n < 4: return None
    for p in range(2, isqrt(n) + 1):
        if n % p: continue
        t, e = n, 0
        while t % p == 0:
            t //= p
            e += 1
        return (p, e) if t == 1 and e >= 2 else None
    return None

def main():
    stats = {"targets":0, "value_memberships":0,
             "coordinate_memberships":0, "rectangle_size_checks":0}
    for upper in range(4, 5000, 7):
        root = isqrt(upper)
        exponent_cutoff = upper.bit_length() - 1
        coordinates = [(base,k) for base in range(root,0,-1)
                       for k in range(exponent_cutoff-1,-1,-1)]
        assert len(coordinates) == root * exponent_cutoff
        stats["rectangle_size_checks"] += 1
        image = {base**(k+2) for base,k in coordinates}
        actual_values = set()
        for n in range(4, upper+1):
            witness = proper_prime_power(n)
            if witness is None: continue
            base, exponent = witness
            assert base <= root and 2**exponent <= upper
            assert (base, exponent-2) in coordinates
            assert n in image
            actual_values.add(n)
            stats["coordinate_memberships"] += 1
            stats["value_memberships"] += 1
        assert len(actual_values) <= len(image) <= len(coordinates)
        stats["targets"] += 1
    assert stats == {"targets":714, "value_memberships":22645,
        "coordinate_memberships":22645, "rectangle_size_checks":714}
    print({"status":"PASS", **stats, "agda_kernel_verified":False,
           "CT11_universal_image_cardinality_proved":False,
           "CT15_gap_two_positive_proved":False})

if __name__ == "__main__":
    main()
