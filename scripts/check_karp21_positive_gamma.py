#!/usr/bin/env python3
"""All short words: original gamma >0 and native successor-bit predecessor.

Independent mathematical model; not an Agda compiler receipt.
"""
from itertools import product

def old_gamma(bits):
    zeros = 0
    while zeros < len(bits) and not bits[zeros]:
        zeros += 1
    if zeros == len(bits) or 2 * zeros + 1 > len(bits):
        return None
    successor = bits[zeros : 2 * zeros + 1]
    value = int("".join(str(x) for x in successor), 2) - 1
    return value, bits[2 * zeros + 1 :]

def native_gamma_positive(bits):
    zeros = 0
    while zeros < len(bits) and not bits[zeros]:
        zeros += 1
    if zeros == len(bits) or 2 * zeros + 1 > len(bits):
        return None
    successor_le = list(reversed(bits[zeros : 2 * zeros + 1]))
    for i, bit in enumerate(successor_le):
        if bit:
            successor_le[i] = 0
            break
        successor_le[i] = 1
    if not any(successor_le):
        return None
    return sum(x << i for i, x in enumerate(successor_le)), bits[2 * zeros + 1 :]

def main():
    cases = 0
    for width in range(15):
        for bits in product((0, 1), repeat=width):
            original = old_gamma(bits)
            expected = original if original is not None and original[0] > 0 else None
            assert native_gamma_positive(bits) == expected, bits
            cases += 1
    assert cases == 32767
    print(f"PASS {cases} original-positive-gamma / bit-native threshold and suffix cases")

if __name__ == "__main__":
    main()
