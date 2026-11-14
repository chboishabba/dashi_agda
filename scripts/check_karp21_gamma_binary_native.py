#!/usr/bin/env python3
"""Exhaustive original-gamma vs bit-native payload parser reference.

Proof authority: none. Finite regression only; Agda original sources are
Karp21GammaZigzagPartitionWordDecodeExact and
Karp21GammaBinaryNativePayloadExact.
"""
from itertools import product

def original_gamma(bits):
    zeros = 0
    while zeros < len(bits) and bits[zeros] == 0:
        zeros += 1
    if zeros == len(bits) or 2 * zeros + 1 > len(bits):
        return None
    payload = bits[zeros + 1:2 * zeros + 1]
    value = int("1" + "".join(str(bit) for bit in payload), 2) - 1
    return value, bits[2 * zeros + 1:]

def binary_native_gamma(bits):
    pos = zeros = work = 0
    while pos < len(bits) and bits[pos] == 0:
        zeros += 1
        pos += 1
        work += 1
    if pos == len(bits):
        return None, work + 1
    pos += 1
    work += 1
    payload = []
    for _ in range(zeros):
        work += 1
        if pos == len(bits):
            return None, work
        payload.append(bits[pos])
        pos += 1
    return ((1, *payload), bits[pos:]), work

def main():
    count = 0
    for length in range(13):
        for bits in product((0, 1), repeat=length):
            native, work = binary_native_gamma(bits)
            old = original_gamma(bits)
            assert work <= 1 + len(bits), (bits, work)
            if native is None:
                assert old is None, bits
            else:
                payload, suffix = native
                decoded_value = int("".join(str(b) for b in payload), 2) - 1
                assert (decoded_value, suffix) == old, bits
            count += 1
    assert count == 8191
    print(f"PASS: {count} gamma inputs (all length <=12), original-value/suffix agreement and linear inspection bound")

if __name__ == "__main__":
    main()
