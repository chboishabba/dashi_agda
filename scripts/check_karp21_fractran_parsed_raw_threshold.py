#!/usr/bin/env python3
"""Original rawSparseScore vs ordered parsed-raw N21 binary ledger machine.

Finite same-source differential only: not Agda kernel certification or
complete original graph-word, bit-machine clock or PR.InNP.
"""
from itertools import product
from random import Random


def endpoint_ok(u, a, history):
    return all(v != u or b == a for v, b in history)


def original_score(edges, bits, history=()):
    if not edges:
        return 0 if not bits else None
    if len(bits) < 2:
        return None
    (u, v, w), rest = edges[0], edges[1:]
    a, b = bits[:2]
    if not (endpoint_ok(u, a, history) and endpoint_ok(v, b, history)):
        return None
    tail = original_score(rest, bits[2:], ((u, a), (v, b)) + history)
    return None if tail is None else tail + (w if a != b else 0)


def compiled_first_enabled(edges, bits, threshold):
    remaining = list(edges)
    witness = list(bits)
    history = ()
    pos, neg = 0, 0
    for _ in range(len(edges) + 2):
        advance = (bool(remaining) and len(witness) >= 2 and
                   endpoint_ok(remaining[0][0], witness[0], history) and
                   endpoint_ok(remaining[0][1], witness[1], history))
        finish = (not remaining and not witness and pos >= neg + threshold)
        if advance:
            u, v, weight = remaining.pop(0)
            a, b = witness[:2]
            witness = witness[2:]
            if a != b:
                if weight >= 0:
                    pos += weight
                else:
                    neg -= weight
            history = ((u, a), (v, b)) + history
        elif finish:
            return True
        else:
            return False
    raise AssertionError("raw-list cursor failed to halt")


def check(edges, bits, threshold):
    s = original_score(edges, bits)
    assert compiled_first_enabled(edges, bits, threshold) == (
        s is not None and s >= threshold)


def main():
    cases = 0
    alphabet = list(product(range(2), range(2), (-2, 0, 3)))
    for n in range(3):
        for edges in product(alphabet, repeat=n):
            for length in range(2*n + 3):
                for bits in product((False, True), repeat=length):
                    for threshold in (1, 2, 4):
                        check(edges, bits, threshold)
                        cases += 1
    rng = Random(1972)
    for _ in range(7000):
        n = rng.randrange(0, 40)
        edges = [(rng.randrange(12), rng.randrange(12),
                  rng.randrange(-(2**128), 2**128))
                 for _ in range(n)]
        bits = [bool(rng.getrandbits(1))
                for _ in range(rng.randrange(0, 2*n + 4))]
        threshold = rng.randrange(1, 2**128)
        check(edges, bits, threshold)
        cases += 1
    print(f'Original N21 parsed raw-score vs first-enabled '
          f'binary threshold machine: {cases:,}/{cases:,} PASS')
    print('Finite differential only; graph codec, Agda and bit clock OPEN.')


if __name__ == "__main__":
    main()
