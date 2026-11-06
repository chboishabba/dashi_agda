#!/usr/bin/env python3
"""Independent all-short-input binary-native signed/zigzag agreement."""
from itertools import product

def reference_signed(bits):
    zeros = 0
    while zeros < len(bits) and bits[zeros] == 0:
        zeros += 1
    if 2 * zeros + 1 > len(bits):
        return None
    n = int("1" + "".join(map(str, bits[zeros + 1:2 * zeros + 1])), 2) - 1
    integer = n // 2 if n % 2 == 0 else -(n // 2 + 1)
    return integer, bits[2 * zeros + 1:]

def native_signed(bits):
    zeros = 0
    while zeros < len(bits) and bits[zeros] == 0:
        zeros += 1
    if 2 * zeros + 1 > len(bits):
        return None
    successor_bits = (1,) + bits[zeros + 1:2 * zeros + 1]
    sign_bit = successor_bits[-1]
    magnitude_bits = successor_bits[:-1]
    magnitude = int("".join(map(str, magnitude_bits)) or "0", 2)
    return (magnitude if sign_bit else -magnitude), bits[2 * zeros + 1:]

def main():
    tested = 0
    for count in range(13):
        for bits in product((0, 1), repeat=count):
            assert native_signed(bits) == reference_signed(bits), bits
            tested += 1
    assert tested == 8191
    print(f"PASS: {tested} binary-native signed token/source zigzag agreements")

if __name__ == "__main__":
    main()
