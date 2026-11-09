#!/usr/bin/env python3
"""Original rawSelectedTrace vs emitted ACTUAL bit-native first-enabled events.

This tests the ordered selected signed-weight LIST, not just final acceptance.
It deliberately uses raw LE binary endpoints during the native side; the
older native_graph regression returns Nat observations and is unsuitable
for testing the binary endpoint-history implementation. Finite differential,
not Agda kernel checking or a physical tape-clock proof.
"""
from itertools import product
from random import Random
from check_karp21_whole_binary_graph import (
    original_graph, native_unsigned, native_edges, gamma, zigzag,
    compare_le, ripple_add, length_le, val,
)

def original_trace(word, certificate):
    graph = original_graph(word)
    if graph is None:
        return None
    _, edges, threshold = graph
    if len(certificate) != 2 * len(edges):
        return None
    seen = []
    selected = []
    for (u, v, w), (a, b) in zip(
        edges, zip(certificate[::2], certificate[1::2])
    ):
        if any(t != a for x, t in seen if x == u):
            return None
        if any(t != b for x, t in seen if x == v):
            return None
        seen = [(u, a), (v, b)] + seen
        if a != b:
            selected.append(w)
    # Selected trace is defined even when total score misses threshold.
    return selected

def native_graph_bits(word):
    first = native_unsigned(word)
    if first is None:
        return None
    n, rest = first
    second = native_unsigned(rest)
    if second is None:
        return None
    m, rest = second
    if compare_le(length_le(rest), ripple_add(m, ripple_add(m, m))) < 0:
        return None
    parsed = native_edges(m, rest, len(rest))
    if parsed is None:
        return None
    edges, rest = parsed
    last = native_unsigned(rest)
    if last is None:
        return None
    threshold, rest = last
    if val(threshold) == 0 or rest:
        return None
    previous = None
    for u, v, _ in edges:
        if compare_le(u, v) >= 0 or compare_le(v, n) >= 0:
            return None
        if previous is not None:
            a, b = previous
            if not (
                compare_le(a, u) < 0
                or (compare_le(a, u) == 0 and compare_le(b, v) < 0)
            ):
                return None
        previous = (u, v)
    return n, edges, threshold

def binary_first_enabled_events(word, certificate):
    graph = native_graph_bits(word)
    if graph is None:
        return None
    _, edges, threshold = graph
    history = []
    selected = []
    remaining = tuple(certificate)
    # Source priority: advance, finish, reject.  Halt after <= m+1.
    for _ in range(len(edges) + 1):
        if not edges:
            return selected if not remaining else None
        if len(remaining) < 2:
            return None
        u, v, w = edges[0]
        a, b = remaining[:2]
        if any(compare_le(u, x) == 0 and a != bit for x, bit in history):
            return None
        if any(compare_le(v, x) == 0 and b != bit for x, bit in history):
            return None
        if a != b:
            selected.append(w)
        history = [(u, a), (v, b)] + history
        edges = edges[1:]
        remaining = remaining[2:]
    return None

def check(word, certificate):
    expected = original_trace(word, certificate)
    actual = binary_first_enabled_events(word, certificate)
    assert actual == expected, (word, certificate, expected, actual)

def main():
    checked = 0
    certificates = [
        tuple(bits) for n in range(5)
        for bits in product((False, True), repeat=n)
    ]
    for n in range(12):
        for word in product((False, True), repeat=n):
            for certificate in certificates:
                check(word, certificate)
                checked += 1
    rng = Random(1972)
    below = 0
    for _ in range(5000):
        n = rng.randrange(2, 24)
        pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
        chosen = sorted(
            rng.sample(pairs, rng.randrange(min(len(pairs), 8) + 1))
        )
        triples = [
            (u, v, rng.randrange(-(1 << 64), 1 << 64))
            for u, v in chosen
        ]
        threshold = rng.randrange(1, 1 << 50)
        word = gamma(n) + gamma(len(triples))
        for u, v, weight in triples:
            word += gamma(u) + gamma(v) + gamma(zigzag(weight))
        word += gamma(threshold)
        for _ in range(5):
            certificate = tuple(
                bool(rng.getrandbits(1))
                for _ in range(rng.randrange(2 * len(triples) + 4))
            )
            check(word, certificate)
            checked += 1
        labels = tuple(bool(rng.getrandbits(1)) for _ in range(n))
        valid = tuple(
            bit for u, v, _ in triples
            for bit in (labels[u], labels[v])
        )
        trace = original_trace(word, valid)
        check(word, valid)
        checked += 1
        assert trace is not None
        if sum(trace) < threshold:
            below += 1
        check(word + (True,), valid)
        checked += 1
    print(
        "Original ordered signed trace vs binary first-enabled events: "
        f"{checked:,}/{checked:,} PASS"
    )
    print(f"Valid below-threshold selected traces retained: {below:,}")
    print("Finite mirror only; no Agda kernel or physical bit-TM receipt.")

if __name__ == "__main__":
    main()
