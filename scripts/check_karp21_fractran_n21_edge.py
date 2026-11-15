#!/usr/bin/env python3
"""Finite differential control for original N21 endpoint-score FRACDASH phase.
Not an Agda typecheck, entire original verifier, or an all-word clock.
"""
from itertools import product


def consistent(vertex, label, history):
    return all(v != vertex or b == label for v, b in history)


def live_guard(u, v, a, b, history, live):
    return live and consistent(u, a, history) and consistent(v, b, history)


def source_step(u, v, a, b, weight, history, live, ledger):
    if not live_guard(u, v, a, b, history, live):
        return False, ledger
    p, n = ledger
    if a != b:
        if weight >= 0:
            p += weight
        else:
            n -= weight
    return True, (p, n)


def cached_step(u, v, a, b, weight, history, ledger, cached):
    rule = next((i for i, ok in enumerate(cached) if ok), None)
    assert rule is not None
    if rule == 1:
        return False, ledger
    p, n = ledger
    if a != b:
        if weight >= 0:
            p += weight
        else:
            n -= weight
    return True, (p, n)


def main():
    histories = [()]
    for k in (1, 2):
        histories.extend(product(product(range(2), (False, True)), repeat=k))
    count = 0
    for u, v, a, b, live, weight, history, p, n in product(
        range(2), range(2), (False, True), (False, True),
        (False, True), (-9, -1, 0, 1, 9), histories,
        range(2), range(2)
    ):
        # Mutate both score lanes without touching fixed original
        # endpoint identities, certificate labels or source history.
        score_only = (p + 100, n + 99)
        fresh = [live_guard(u, v, a, b, history, live), True]
        cached = list(fresh)
        assert cached_step(u, v, a, b, weight, history, score_only, cached) == (
            source_step(u, v, a, b, weight, history, live, score_only)
        )
        count += 1
    assert not live_guard(0, 1, True, False, ((0, False),), True)
    print(f'N21 edge FRACTRAN bounded differential: {count:,} passed')
    print('conflicting endpoint negative control: passed')
    print('Not full rawSparseScore, Agda 2.9 or a polynomial bit-machine receipt')


if __name__ == '__main__':
    main()
