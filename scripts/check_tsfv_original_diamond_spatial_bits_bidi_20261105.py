#!/usr/bin/env python3
"""Exact 5-event original diamond spatial sensor/cardinality reference.
A finite information lower bound, NOT a physical 4D causal cone,
continuum, OS Hilbert, or kernel acceptance receipt.
"""
from itertools import product

EVENTS = ("past", "xNow", "yNow", "zNow", "future")
LEVELS = {
    "past": "initial",
    "xNow": "intermediate",
    "yNow": "intermediate",
    "zNow": "intermediate",
    "future": "terminal",
}


def check():
    checked = 0
    for values in product((False, True), repeat=5):
        sensor = dict(zip(EVENTS, values))
        assert len({
            (LEVELS[event], sensor[event])
            for event in ("xNow", "yNow", "zNow")
        }) < 3
        checked += 1

    bits = (
        (False, False), (False, True),
        (True, False), (True, True),
    )
    injective = 0
    for codes in product(bits, repeat=3):
        if len(set(codes)) == 3:
            injective += 1
    assert injective == 24

    sensor = {
        "past": (False, False),
        "xNow": (False, False),
        "yNow": (False, True),
        "zNow": (True, False),
        "future": (False, False),
    }

    def decode(level, code):
        if level == "initial":
            return "past"
        if level == "terminal":
            return "future"
        return {
            (False, False): "xNow",
            (False, True): "yNow",
            (True, False): "zNow",
            (True, True): "zNow",
        }[code]

    assert all(decode(LEVELS[e], sensor[e]) == e for e in EVENTS)
    print(f"PASS: all {checked} one-bit 5-event sensor maps fail x/y/z decoding")
    print(f"PASS: 64 two-bit spatial assignments; exactly {injective} injective")
    print("PASS: original two-bit and filtration decoder reconstructs all five")
    print("REFERENCE ONLY: no 4D propagation or Agda kernel proof")


if __name__ == "__main__":
    check()
