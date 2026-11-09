#!/usr/bin/env python3
"""Finite binary signed-token/SSP-polarity residual codec regression.

Tests binary residual round trips; establishes no Agda or machine-clock proof.
"""
from itertools import product

def encode(sign, bits):
    return ("forward" if sign else "inverse", bits)

def decode(code):
    direction, bits = code
    if direction == "forward":
        return True, bits
    if direction == "inverse":
        return False, bits
    return None

def main():
    count = 0
    for width in range(11):
        for word in product((False, True), repeat=width):
            for sign in (False, True):
                assert decode(encode(sign, word)) == (sign, word)
                count += 1
    assert encode(True, ())[0] == encode(True, (True,))[0]
    assert (True, ()) != (True, (True,))
    assert decode(("mediated", (True,))) is None
    assert count == 4094
    print(f"PASS {count} signed-polarity residual roundtrips; orientation collision confirmed")

if __name__ == "__main__":
    main()
