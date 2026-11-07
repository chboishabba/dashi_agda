#!/usr/bin/env python3
"""Bounded differential check of original and binary-native signed gamma."""
from itertools import product

def old_signed(word):
    k = 0
    while k < len(word) and word[k] == 0:
        k += 1
    if k >= len(word) or 2 * k + 1 > len(word):
        return None
    n = (1 << k) - 1
    for i, bit in enumerate(word[k + 1:2 * k + 1]):
        n += bit << (k - i - 1)
    return (n // 2 if n % 2 == 0 else -(n // 2 + 1),
            word[2 * k + 1:])

def native_signed(word):
    k = 0
    while k < len(word) and word[k] == 0:
        k += 1
    if k >= len(word) or 2 * k + 1 > len(word):
        return None
    binary_successor = word[k:2 * k + 1]
    magnitude = 0
    for bit in binary_successor[:-1]:
        magnitude = 2 * magnitude + bit
    return (magnitude if binary_successor[-1] else -magnitude,
            word[2 * k + 1:])

def main():
    total = 0
    for n in range(14):
        for word in product((0, 1), repeat=n):
            assert old_signed(word) == native_signed(word), word
            total += 1
    print(f"PASS: {total} all binary words length <=13: sign, value, suffix, rejection")

if __name__ == "__main__":
    main()
