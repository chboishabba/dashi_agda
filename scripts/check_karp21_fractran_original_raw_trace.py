#!/usr/bin/env python3
"""Bounded reproduction of original N21 rawSparseScore versus trace replay.

Follows the source original guard, history order, certificate length
and signed weight semantics; not an Agda kernel or NP clock receipt.
"""
from itertools import product

def endpoint_consistent(vertex, selected, history):
    return all(other != vertex or observed == selected
               for other, observed in history)

def score(edges, bits, history):
    if not edges:
        return 0 if not bits else None
    if len(bits) < 2:
        return None
    u, v, w = edges[0]
    a, b = bits[:2]
    if not endpoint_consistent(u, a, history) or not endpoint_consistent(v, b, history):
        return None
    rest = score(edges[1:], bits[2:], ((u, a), (v, b)) + history)
    if rest is None:
        return None
    return rest if a == b else w + rest

def selected_trace(edges, bits, history):
    if not edges:
        return [] if not bits else None
    if len(bits) < 2:
        return None
    u, v, w = edges[0]
    a, b = bits[:2]
    if not endpoint_consistent(u, a, history) or not endpoint_consistent(v, b, history):
        return None
    tail = selected_trace(edges[1:], bits[2:], ((u, a), (v, b)) + history)
    if tail is None:
        return None
    return tail if a == b else [w] + tail

def main():
    alphabet = [(u, v, w) for u, v, w in product(range(2), range(2), (-2, 0, 3))]
    count = accepted = rejected = 0
    for n in range(4):
        for edges in product(alphabet, repeat=n):
            for width in range(2*n + 2):
                for bits in product((False, True), repeat=width):
                    original = score(edges, bits, ())
                    trace = selected_trace(edges, bits, ())
                    reconstructed = None if trace is None else sum(trace)
                    assert original == reconstructed, (edges, bits, original, trace)
                    accepted += original is not None
                    rejected += original is None
                    count += 1
    assert score(((0, 1, -2),), (False, True), ()) == -2
    assert selected_trace(((0, 1, -2),), (False, True), ()) == [-2]
    assert selected_trace(((0, 0, 3), (0, 1, -2)), (False, True, True, False), ()) is None
    print(f'Original raw signed-score / trace replay: {count:,} cases PASS')
    print(f'Accepted {accepted:,}; rejected {rejected:,}')
    print('Controls: negative cut contribution and conflicting endpoint rejection PASS')
    print('No Agda kernel receipt or full binary gamma/NP clock claimed.')

if __name__ == '__main__':
    main()
