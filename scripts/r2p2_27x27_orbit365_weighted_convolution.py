"""Exact Q(omega) checks for the 365-orbit real-field bilinear compiler.

Scientific and repository provenance: Serre orbit counting; Orszag/Patterson
pseudo-spectral convolution; DASHI original 27/729, 13/27 and Q(omega) owners.
This is an arithmetic check, NOT an Agda kernel receipt or NS theorem.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from random import Random

MODES = tuple(product((-1, 0, 1), repeat=3))
WIDE = tuple(product((-2, -1, 0, 1, 2), repeat=3))
PAIRS = tuple(product(MODES, repeat=2))
ZERO = (0, 0, 0)
CZERO = (Fraction(0), Fraction(0))


def neg(k):
    return tuple(-v for v in k)


def add_modes(p, q):
    return tuple(x + y for x, y in zip(p, q))


def canonical(k):
    return next((v > 0 for v in k if v), True)


def pair_canonical(pair):
    p, q = pair
    return canonical(p) if p != ZERO else canonical(q)


def conj(z):
    a, b = z
    return a - b, -b


def mul(x, y):
    a, b = x
    c, d = y
    return a * c - b * d, a * d + b * c - b * d


def plus(x, y):
    return x[0] + y[0], x[1] + y[1]


def field(seed):
    rng = Random(seed)
    coefficients = {}
    for k in MODES:
        if canonical(k):
            coefficients[k] = (Fraction(rng.randrange(-8, 9), 7),
                               Fraction(0 if k == ZERO else rng.randrange(-8, 9), 11))
    for k in MODES:
        if k not in coefficients:
            coefficients[k] = conj(coefficients[neg(k)])
    assert all(coefficients[neg(k)] == conj(coefficients[k]) for k in MODES)
    return coefficients


def baseline(f, g):
    values = {k: CZERO for k in WIDE}
    multiplications = 0
    for p, q in PAIRS:
        k = add_modes(p, q)
        values[k] = plus(values[k], mul(f[p], g[q]))
        multiplications += 1
    return values, multiplications


def reduced(f, g):
    values = {k: CZERO for k in WIDE}
    multiplications = 0
    representatives = [pair for pair in PAIRS if pair_canonical(pair)]
    for p, q in representatives:
        k = add_modes(p, q)
        z = mul(f[p], g[q])
        multiplications += 1
        values[k] = plus(values[k], z)
        if (p, q) != (ZERO, ZERO):
            values[neg(k)] = plus(values[neg(k)], conj(z))
    return values, multiplications, representatives


def check():
    # Exhaustive address permutation, independent of coefficient profiles.
    reps = [pair for pair in PAIRS if pair_canonical(pair)]
    expanded = []
    for p, q in reps:
        expanded.append((p, q))
        if (p, q) != (ZERO, ZERO):
            expanded.append((neg(p), neg(q)))
    assert len(reps) == 365 and len(expanded) == 729
    assert Counter(expanded) == Counter(PAIRS)

    # Existing five-in-nine symmetry: 81 ordered pairs form 41 orbits.
    plane = tuple(product((-1, 0, 1), repeat=2))
    plane_pairs = tuple(product(plane, repeat=2))
    plane_zero = (0, 0)
    plane_reps = [(p, q) for p, q in plane_pairs
                  if (canonical(p) if p != plane_zero else canonical(q))]
    plane_expanded = [(p, q) for p, q in plane_reps]
    plane_expanded += [(neg(p), neg(q)) for p, q in plane_reps
                       if (p, q) != (plane_zero, plane_zero)]
    assert len(plane_reps) == 41 and len(plane_expanded) == 81
    assert Counter(plane_expanded) == Counter(plane_pairs)
    for p, q in PAIRS:
        assert pair_canonical((p, q)) != pair_canonical((neg(p), neg(q))) or (p, q) == (ZERO, ZERO)
        assert add_modes(neg(p), neg(q)) == neg(add_modes(p, q))
    for i in range(12):
        f = field(20261029 + i)
        g = field(100000 + 37 * i)
        full, full_muls = baseline(f, g)
        fast, fast_muls, reps = reduced(f, g)
        assert len(reps) == 365
        assert full_muls == 729 and fast_muls == 365
        assert fast == full, next((k for k in WIDE if fast[k] != full[k]), None)
        assert all(full[neg(k)] == conj(full[k]) for k in WIDE)
        assert full[ZERO][1] == 0
        assert len([k for k in WIDE if all(abs(x) <= 1 for x in k)]) == 27
    print('PASS: 12 distinct exact Q(omega) Hermitian two-field profiles, all 125 coefficients')
    print('PASS: 729 original vs 365 products (+364 conjugations), 365 orbits, 729 emitted events')
    print('PASS: exhaustive address permutation in 3D (365) and 2D (41)')
    print('PASS: global negation, integer-sum covariance, real zero-frequency output')


if __name__ == '__main__':
    check()
