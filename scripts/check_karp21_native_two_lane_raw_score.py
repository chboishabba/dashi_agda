#!/usr/bin/env python3
"""Independent finite original N21 rawSparseScore vs real two-lane binary arithmetic.

The original endpoint-history and exactly two label bits per edge mirror
Karp21FinFreeRawSparseWordVerifierExact; the native selected token fold
models Karp21BinaryNativeSignedLedgerExact using LE binary registers.
This is a differential test, NOT an Agda checker or proof of a tape clock.
"""
from itertools import product
from random import Random


def endpoint_consistent(vertex, selected, history):
    return all(other != vertex or observed == selected
               for other, observed in history)


def original_score(edges, certificate, history=()):
    if not edges:
        return 0 if not certificate else None
    if len(certificate) < 2:
        return None
    u, v, weight = edges[0]
    a, b = certificate[:2]
    if not endpoint_consistent(u, a, history):
        return None
    if not endpoint_consistent(v, b, history):
        return None
    tail = original_score(edges[1:], certificate[2:],
                          ((u, a), (v, b)) + history)
    if tail is None:
        return None
    return tail + (weight if a != b else 0)


def selected_original_tokens(edges, certificate, history=()):
    if not edges:
        return [] if not certificate else None
    if len(certificate) < 2:
        return None
    u, v, weight = edges[0]
    a, b = certificate[:2]
    if not endpoint_consistent(u, a, history):
        return None
    if not endpoint_consistent(v, b, history):
        return None
    tail = selected_original_tokens(
        edges[1:], certificate[2:], ((u, a), (v, b)) + history)
    if tail is None:
        return None
    return ([weight] if a != b else []) + tail


def observe_le(bits):
    return sum(int(bit) << i for i, bit in enumerate(bits))


def to_le(n):
    assert n >= 0
    return tuple(bool((n >> i) & 1) for i in range(n.bit_length()))


def ripple_add(xs, ys):
    result = []
    carry = False
    for i in range(max(len(xs), len(ys))):
        x = int(xs[i]) if i < len(xs) else 0
        y = int(ys[i]) if i < len(ys) else 0
        total = x + y + int(carry)
        result.append(bool(total & 1))
        carry = bool(total >> 1)
    if carry:
        result.append(True)
    return tuple(result)


def native_ledger_score(edges, certificate):
    tokens = selected_original_tokens(edges, certificate)
    if tokens is None:
        return None
    positive, negative = (), ()
    for weight in tokens:
        if weight >= 0:
            positive = ripple_add(positive, to_le(weight))
        else:
            negative = ripple_add(negative, to_le(-weight))
    return observe_le(positive) - observe_le(negative)


def main():
    alphabet = [(u, v, w) for u, v, w
                in product(range(2), range(2), (-2, 0, 3))]
    checked = 0
    for n in range(4):
        for edges in product(alphabet, repeat=n):
            for width in range(2 * n + 2):
                for cert in product((False, True), repeat=width):
                    assert native_ledger_score(edges, cert) == original_score(edges, cert)
                    checked += 1
    rng = Random(1972)
    for _ in range(5000):
        n = rng.randrange(1, 35)
        edges = [(rng.randrange(7), rng.randrange(7),
                  rng.randrange(-(1 << 256), 1 << 256))
                 for _ in range(n)]
        cert = tuple(bool(rng.randrange(2)) for _ in range(2 * n))
        assert native_ledger_score(edges, cert) == original_score(edges, cert)
        checked += 1
    print(f'Original signed rawSparseScore / native two-lane binary ledger: {checked:,} PASS')
    print('Finite differential only. Agda, full graph header, clock and InNP not certified.')


if __name__ == "__main__":
    main()
