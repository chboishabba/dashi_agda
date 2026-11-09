#!/usr/bin/env python3
"""Finite original signed-gamma BE→LE/native zigzag numeric regression.

This independently reproduces the Agda source's payloadValue and
Native.SignedMagnitudeBits arithmetic equations. It is a finite
differential, NOT an Agda proof, complete graph-parser simulation or
polynomial-time bit-machine receipt.
"""
from itertools import product
from random import Random


def value_be(xs):
    n = 0
    for bit in xs:
        n = 2 * n + int(bit)
    return n


def original_unzigzag(code):
    return code // 2 if code % 2 == 0 else -(code // 2 + 1)


def check(prefix, last):
    magnitude = (1 << len(prefix)) + value_be(prefix)
    native_bits = (True,) + prefix
    native_le_observation = sum(int(bit) << i
                                for i, bit in enumerate(reversed(native_bits)))
    assert magnitude == native_le_observation
    successor = value_be(native_bits + (last,))
    assert successor == 2 * magnitude + int(last)
    original = original_unzigzag(successor - 1)
    actual_token = magnitude if last else -magnitude
    assert original == actual_token
    assert magnitude >= 1


def main():
    count = 0
    for width in range(15):
        for prefix in product((False, True), repeat=width):
            check(prefix, False)
            check(prefix, True)
            count += 2

    rng = Random(1972)
    for width in (128, 256, 1024, 2048):
        for _ in range(100):
            prefix = tuple(bool(rng.getrandbits(1)) for _ in range(width))
            check(prefix, False)
            check(prefix, True)
            count += 2

    assert original_unzigzag(0) == 0   # gamma zero, [true]
    print(f'Original zigzag/native signed gamma number theory: {count:,} cases PASS')
    print('Positive/negative; BE payload vs LE ledger; 2M+b; nonzero negative magnitude')
    print('Not Agda kernel, original graph-word parser, or a bit-Turing-machine clock')


if __name__ == '__main__':
    main()
