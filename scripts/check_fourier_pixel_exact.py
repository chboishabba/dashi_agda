#!/usr/bin/env python3
"""Exact finite Gaussian-rational optics fixtures (not device simulations).

Source: Glauser, Vonk, Seda et al. (2026), Nature 655, 87-92,
doi:10.1038/s41586-026-10681-7 (especially Methods equations 3-9).
All equalities below are exact rational computations; spectral routing is
an EXPLICIT finite-model assumption, not a measured light-cone criterion.
"""
import json
from fractions import Fraction


def z(re=0, im=0):
    return Fraction(re), Fraction(im)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[0], -a[1]


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def conj(a):
    return a[0], -a[1]


def scale(q, a):
    return Fraction(q) * a[0], Fraction(q) * a[1]


def norm2(a):
    return a[0] ** 2 + a[1] ** 2


I = z(0, 1)
ONE = z(1)
ZERO = z()
ROOT4 = [ONE, neg(I), neg(ONE), I]  # exp(-2*pi*i*k/4)


def dft4(xs):
    assert len(xs) == 4
    out = []
    for k in range(4):
        val = ZERO
        for n, x in enumerate(xs):
            val = add(val, mul(x, ROOT4[(k * n) % 4]))
        out.append(val)
    return out


def idft4(xs):
    assert len(xs) == 4
    return [scale(Fraction(1, 4), v) for v in
            [sum_z(mul(xs[k], conj(ROOT4[(k * n) % 4]))
                   for k in range(4)) for n in range(4)]]


def sum_z(values):
    result = ZERO
    for value in values:
        result = add(result, value)
    return result


def spectrum_add(a, b):
    return {k: add(a.get(k, ZERO), b.get(k, ZERO)) for k in set(a) | set(b)}


def spectrum_scale(q, a):
    return {k: scale(q, v) for k, v in a.items()}


def spectrum_conj(a, N):
    return {(-k) % N: conj(v) for k, v in a.items()}


def spectrum_shift(a, shift, N):
    return {(k + shift) % N: v for k, v in a.items()}


def trim(a):
    return {k: v for k, v in a.items() if v != ZERO}


def phase_measurements():
    roots = [ONE, I, neg(ONE), neg(I)]
    intensity_only = [norm2(x) for x in roots]
    first = [norm2(add(x, ONE)) for x in roots]
    second = [norm2(add(x, I)) for x in roots]
    assert intensity_only == [1, 1, 1, 1]
    assert first == [4, 2, 0, 2]
    assert second == [2, 4, 2, 0]
    assert len(set(zip(first, second))) == 4
    assert len(set(first)) == 3  # one quadrature has an unresolved collision
    return {"intensity_only": list(map(int, intensity_only)),
            "x_reference": list(map(int, first)),
            "y_reference": list(map(int, second)),
            "pair_decodes_four_phases": True}


def spectral_fixture():
    """N=16 exact group-ring frequency fixture for paper's Eq. (8).

    Reference r is bin 4, r**2 bin 8. Radiated bin mask {0,1,15}
    is stipulated by the fixture; it is NOT a Maxwell-based filter.
    """
    N = 16
    desired = {0: z(2, 1), 1: z(1, -1), 15: z(Fraction(1, 2), 1)}
    reference = {4: ONE}
    mirror = spectrum_shift(spectrum_conj(desired, N), 8, N)
    actual = spectrum_add(reference, spectrum_scale(Fraction(1, 2),
                      spectrum_add(desired, spectrum_scale(-1, mirror))))
    radiated_bins = {0, 1, 15}
    isolated = trim({k: v for k, v in actual.items() if k in radiated_bins})
    assert isolated == spectrum_scale(Fraction(1, 2), desired)
    assert set(mirror) == {8, 7, 9}
    assert set(mirror).isdisjoint(radiated_bins)
    assert 4 not in radiated_bins
    # A target Fourier mode in the 'mirror' band gives a ghost at bin 0.
    bad = {8: z(1, 1)}
    bad_mirror = spectrum_shift(spectrum_conj(bad, N), 8, N)
    bad_actual = spectrum_add(reference, spectrum_scale(Fraction(1, 2),
                              spectrum_add(bad, spectrum_scale(-1, bad_mirror))))
    assert bad_actual[0] != ZERO  # undesired radiating bin: -conj(bad)/2
    assert 0 not in bad
    return {"size": N, "guided_bin": 4, "twin_shift_bin": 8,
            "desired_bins": sorted(desired),
            "mirror_bins": sorted(mirror),
            "desired_recovered_at_half_scale": True,
            "counterexample_target_bin": 8,
            "counterexample_ghost_bin": 0,
            "universal_spectral_isolation": False}


def main():
    basis = [[ONE if n == j else ZERO for n in range(4)] for j in range(4)]
    input_samples = [z(2, -1), z(-3, 2), z(Fraction(2, 3), 4), z(0, Fraction(1, 2))]
    for v in basis + [input_samples]:
        assert idft4(dft4(v)) == v
        assert sum(norm2(x) for x in dft4(v)) == 4 * sum(norm2(x) for x in v)
    out = {"authority": "exact finite synthetic calculation, not kernel or physical proof",
           "fourier_4_roundtrips": len(basis) + 1,
           "fourier_4_parseval_fixtures": len(basis) + 1,
           "quadrature": phase_measurements(),
           "spectral_routing": spectral_fixture()}
    print(json.dumps(out, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
