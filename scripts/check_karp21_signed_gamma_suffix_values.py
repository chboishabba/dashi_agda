#!/usr/bin/env python3
"""Finite differential for original gamma(n+1) versus native binary signed reader.

Tests literal source algorithms, not Agda proof terms or an original
graph-level verifier. Retains malformed input and suffix, not just encodings.
"""
from itertools import product
from random import Random

def gamma(bits):
    k = 0
    while k < len(bits) and not bits[k]:
        k += 1
    if k >= len(bits) or len(bits) - k - 1 < k:
        return None
    numeral = bits[k:k + k + 1]
    return numeral, bits[k + k + 1:]

def original(bits):
    result = gamma(bits)
    if result is None:
        return None
    numeral, suffix = result
    n = int(''.join('1' if b else '0' for b in numeral), 2) - 1
    signed = n // 2 if n % 2 == 0 else -(n // 2 + 1)
    return signed, suffix

def native(bits):
    result = gamma(bits)
    if result is None:
        return None
    numeral, suffix = result
    if not numeral:
        return None
    magnitude = numeral[:-1]
    value = int(''.join('1' if b else '0' for b in magnitude), 2) if magnitude else 0
    return (value if numeral[-1] else -value), suffix

def main():
    n = 0
    accepted = 0
    for length in range(16):
        for word in product((False, True), repeat=length):
            o, v = original(word), native(word)
            assert o == v, (word, o, v)
            n += 1
            accepted += o is not None
    rnd = Random(1972)
    for i in range(200):
        length = rnd.choice((256, 1024, 2048))
        bits = (False,) * (length - 1) + (True,) + tuple(
            rnd.choice((False, True)) for _ in range(length - 1)
        )
        suffix = tuple(rnd.choice((False, True)) for _ in range(i % 11))
        o, v = original(bits + suffix), native(bits + suffix)
        assert o == v
        assert o is not None and o[1] == suffix
        n += 1
        accepted += 1
    print(f'Original/native signed gamma finite comparison: {n:,} PASS')
    print(f'Valid parsed frames: {accepted:,}')
    print('Covers sign, value, suffix and rejection; not Agda or all-word mathematical proof')

if __name__ == '__main__':
    main()
