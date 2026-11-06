#!/usr/bin/env python3
"""Independent bounded model of ORIGINAL N21 strictAfter/validRawEdges.

Does not substitute for Agda 2.9 kernel acceptance. The source
structure follows Karp21GammaZigzagGraphWordDecodeExact.strictAfter and
Karp21FinFreeRawSparseWordVerifierExact.validRawEdges.
"""
from itertools import product

def strict_after(previous, u, v):
    if previous is None:
        return True
    a, b = previous
    if a < u:
        return True
    if a != u:
        return False
    return b < v

def strict_after_counted(previous, u, v):
    if previous is None:
        return True, 0
    a, b = previous
    if a < u:
        return True, 1
    if a != u:
        return False, 2
    return b < v, 3

def raw_valid(n, previous, edges):
    if not edges:
        return True
    (u, v), *rest = edges
    if u < v and v < n and strict_after(previous, u, v):
        return raw_valid(n, (u, v), rest)
    return False

def counted_raw(n, previous, edges):
    if not edges:
        return True, 0
    (u, v), *rest = edges
    status, cost = strict_after_counted(previous, u, v)
    if u < v and v < n and status:
        result, remaining = counted_raw(n, (u, v), rest)
        return result, 2 + cost + remaining
    return False, 2 + cost

def main():
    pairs = list(product(range(4), repeat=2))
    total = 0
    for n in range(6):
        for edge_count in range(4):
            for edges in product(pairs, repeat=edge_count):
                result, cost = counted_raw(n, None, list(edges))
                assert result == raw_valid(n, None, list(edges))
                assert cost <= 5 * edge_count
                total += 1
    assert total == 26214, total
    print(f"PASS original N21 raw validation: {total} primitive-comparison cases")

if __name__ == "__main__":
    main()
