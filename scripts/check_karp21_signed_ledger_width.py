#!/usr/bin/env python3
"""Real signed two-lane ripple-ledger width budget finite differential.

Bound: width(final) <= width(initial)+sum(1+len(magnitude bits)).
Mirror of actual Ledger.insertSigned / accumulateSigned. Not Agda proof.
"""
from random import Random
from itertools import product
from check_karp21_whole_binary_graph import ripple_add

def insert(token, ledger):
    positive, magnitude_be = token
    p, n = ledger
    magnitude_le = tuple(reversed(magnitude_be))
    if positive:
        return ripple_add(p, magnitude_le), n
    return p, ripple_add(n, magnitude_le)

def width(ledger):
    return len(ledger[0]) + len(ledger[1])

def check(tokens, ledger):
    original_width = width(ledger)
    budget = sum(1 + len(bits) for sign, bits in tokens)
    for token in tokens:
        next_ledger = insert(token, ledger)
        assert width(next_ledger) <= width(ledger) + 1 + len(token[1])
        ledger = next_ledger
    assert width(ledger) <= original_width + budget

def main():
    cases = 0
    for count in range(6):
        for bits in product((False, True), repeat=count):
            for positive in (False, True):
                for p in ((), (False,), (True, True), (False,)*8):
                    for n in ((), (False,), (True, True), (True,)*8):
                        check(((positive, bits),), (p, n))
                        cases += 1
    rng = Random(1972)
    for _ in range(100000):
        tokens = [
            (bool(rng.getrandbits(1)),
             tuple(bool(rng.getrandbits(1))
                   for _ in range(rng.randrange(49))))
            for _ in range(rng.randrange(32))
        ]
        p = tuple(bool(rng.getrandbits(1))
                  for _ in range(rng.randrange(40)))
        n = tuple(bool(rng.getrandbits(1))
                  for _ in range(rng.randrange(40)))
        check(tokens, (p, n))
        cases += 1
    print(f"Actual signed ledger register-width budget: {cases:,}/{cases:,} PASS")
    print("Finite runtime differential only; not Agda kernel or TM cost.")

if __name__ == "__main__":
    main()
