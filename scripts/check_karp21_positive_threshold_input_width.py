#!/usr/bin/env python3
"""F2.2 original positive-gamma W register source-bit charge.

Independent finite mirror of actual readGammaBinary -> reverse ->
predecessorLE -> anyOne, with original suffix preservation.
No Agda kernel or physical bit-TM receipt.
"""
from itertools import product
from random import Random

def scan(word):
    zeros = 0
    while zeros < len(word) and not word[zeros]:
        zeros += 1
    if zeros == len(word) or len(word) < 2 * zeros + 1:
        return None
    return word[zeros:2 * zeros + 1], word[2 * zeros + 1:]

def predecessor_le(bits):
    bits = list(bits)
    for i, bit in enumerate(bits):
        if bit:
            bits[i] = False
            break
        bits[i] = True
    return tuple(bits)

def read_positive_gamma_le(word):
    parsed = scan(word)
    if parsed is None:
        return None
    successor, suffix = parsed
    threshold = predecessor_le(successor[::-1])
    if not any(threshold):
        return None
    return threshold, suffix

def gamma(value):
    payload = tuple(c == "1" for c in bin(value + 1)[2:])
    return (False,) * (len(payload) - 1) + payload

def main():
    count = 0
    for width in range(16):
        for word in product((False, True), repeat=width):
            result = read_positive_gamma_le(word)
            if result is not None:
                threshold, suffix = result
                assert len(threshold) + len(suffix) <= len(word)
                assert sum(int(bit) << i for i, bit in enumerate(threshold)) > 0
            count += 1
    rng = Random(1972)
    for _ in range(20000):
        value = rng.randrange(1, 1 << rng.randrange(2, 100))
        prefix = gamma(rng.randrange(1 << 40)) + gamma(rng.randrange(1 << 40))
        suffix = tuple(bool(rng.getrandbits(1)) for _ in range(rng.randrange(60)))
        source = gamma(value) + suffix
        result = read_positive_gamma_le(source)
        assert result is not None
        threshold, after = result
        assert after == suffix
        assert len(threshold) <= len(gamma(value)) <= len(prefix) + len(source)
        count += 1
    print(f"Original positive W gamma register/suffix bit charge: {count:,}/{count:,} PASS")
    print("Finite source mirror only, not Agda checking or tape-cost proof.")

if __name__ == "__main__":
    main()
