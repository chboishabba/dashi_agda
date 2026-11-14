#!/usr/bin/env python3
"""Executable, exact-integer reference for Karp21BinaryNativeSignedLedgerExact.

Independent finite test. Not an Agda kernel receipt.
"""
from itertools import product

def add_bits(a, b):
    result, carry = [], 0
    for i in range(max(len(a), len(b))):
        t = (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) + carry
        result.append(t & 1)
        carry = t >> 1
    if carry:
        result.append(1)
    return result

def unsigned_be(n):
    return [int(x) for x in bin(n)[2:]]

def value_le(bits):
    return sum(b << i for i, b in enumerate(bits))

def ledger(tokens):
    positive, negative = [], []
    for v in tokens:
        bits = list(reversed(unsigned_be(abs(v))))
        if v >= 0:
            positive = add_bits(positive, bits)
        else:
            negative = add_bits(negative, bits)
    return value_le(positive), value_le(negative)

def main():
    cases = 0
    for n in range(7):
        for tokens in product((-5, -2, -1, 0, 1, 2, 5), repeat=n):
            p, q = ledger(tokens)
            assert p == sum(max(v, 0) for v in tokens), tokens
            assert q == sum(max(-v, 0) for v in tokens), tokens
            assert p - q == sum(tokens), tokens
            cases += 1
    assert cases == 137257
    print(f"PASS: {cases} signed-lists; positive/negative totals and signed score")

if __name__ == "__main__":
    main()
