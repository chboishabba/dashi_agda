#!/usr/bin/env python3
"""Exact Nat arithmetic regression for CT11 finite binary exponent cutoff.

Models TwinPrimeProperPowerBinaryCutoffNatExact.floorBinaryExponent:
choose maximal e in 0..upper such that 2**e <= upper.
Checks it equals integer floor-log2 for upper>=1 and that EVERY
bounded proper positive-base power lies in the computed CT11 rectangle.

No floating logs; no inferred prime-distribution law.
Finite Python regression, not Agda kernel or analytic proof.
Original owners: GeneralResidualFibreCardinalityExact.pow2,
FiniteNatFloorSquareRootExact and RiemannPrimePowerArithmetic.natPow.
"""
from math import isqrt

def floor_binary_exponent(upper):
    current = 0
    for e in range(1, upper + 1):
        if (1 << e) <= upper:
            current = e
    return current

def main():
    powers = 0
    for upper in range(2049):
        cutoff = floor_binary_exponent(upper)
        expected = upper.bit_length() - 1 if upper else 0
        assert cutoff == expected, (upper, cutoff, expected)
        for exponent in range(min(14, upper + 1)):
            if (1 << exponent) <= upper:
                assert exponent <= cutoff
        for base in range(2, isqrt(upper) + 1):
            exponent = 2
            while base ** exponent <= upper:
                assert base <= isqrt(upper)
                assert (1 << exponent) <= upper
                assert exponent <= cutoff
                assert exponent - 2 < cutoff
                powers += 1
                exponent += 1
    assert powers == 97619, powers
    print({"status": "PASS", "upper_bounds": 2049,
           "proper_power_coordinate_witnesses": powers,
           "agda_kernel_checked": False,
           "analytic_gap_two_positive_proved": False})

if __name__ == "__main__":
    main()
