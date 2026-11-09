#!/usr/bin/env python3
"""Original source Karp compareLE numerical differential, exact bit-order semantics.

Exhaustive all bitwords of lengths 0..7; random independently sized
bitwords to 513 digits. Validates high-priority higher bit and implicit
zero-extension. Does NOT replace the missing Agda proof or bit-TM clock.
"""
from itertools import product
from random import Random


def bitorder(a, b):
    if a == b:
        return 0
    return 1 if a else -1


def compare(xs, ys):
    if not xs and not ys:
        return 0
    a = xs[0] if xs else False
    b = ys[0] if ys else False
    higher = compare(xs[1:] if xs else (), ys[1:] if ys else ())
    return higher if higher != 0 else bitorder(a, b)


def value(xs):
    return sum(int(b) << i for i, b in enumerate(xs))


def check(xs, ys):
    actual = compare(xs, ys)
    expected = (value(xs) > value(ys)) - (value(xs) < value(ys))
    assert actual == expected, (xs, ys, actual, expected)
    assert (actual >= 0) == (value(xs) >= value(ys))


def main():
    cases = 0
    words = [tuple(w) for n in range(8)
             for w in product((False, True), repeat=n)]
    for xs in words:
        for ys in words:
            check(xs, ys)
            cases += 1
    rng = Random(1972)
    for _ in range(6000):
        xs = tuple(bool(rng.getrandbits(1))
                   for _ in range(rng.randint(0, 513)))
        ys = tuple(bool(rng.getrandbits(1))
                   for _ in range(rng.randint(0, 513)))
        check(xs, ys)
        cases += 1
    print(f'Original Karp native compareLE numerical differential: '
          f'{cases:,}/{cases:,} PASS')
    print('Not an Agda kernel proof or a physical tape clock.')


if __name__ == '__main__':
    main()
