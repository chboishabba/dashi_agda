"""Exact finite Zipf F13 parity: existing unreduced fractions vs PNF masses.

Independent computational check of source-written Agda F13; NOT Agda kernel
verification. Classical finite mathematics belongs to Zipf/Estoup,
Mandelbrot, Hurwitz; adaptation Johl Brown + OpenAI ChatGPT, 2026-10-28.
"""
from __future__ import annotations
from fractions import Fraction
from math import prod


def _parameters(support: int, exponent: int, shift: int) -> None:
    if (type(support) is not int or support < 1
            or type(exponent) is not int or exponent < 0
            or type(shift) is not int or shift < 0):
        raise ValueError('support>=1, exponent/shift nonnegative integers')


def source_unreduced_hurwitz_fraction(
    support: int, exponent: int, shift: int = 0
) -> tuple[int, int]:
    """Independent implementation of ZipfFamilyFiniteExact.sumFirst/addFraction."""
    _parameters(support, exponent, shift)
    numerator, denominator = 0, 1
    for rank in range(1, support+1):
        d = (rank+shift)**exponent
        numerator, denominator = numerator*d+denominator, denominator*d
    assert numerator > 0 and denominator > 0
    return numerator, denominator


def constructive_pnf_masses(
    support: int, exponent: int, shift: int = 0
) -> tuple[Fraction, ...]:
    """Reversed-rank Agda mass order; all atoms positive, exact sum one."""
    _parameters(support, exponent, shift)
    raw = tuple(Fraction(1,(r+shift)**exponent)
                for r in range(support,0,-1))
    z = sum(raw,Fraction())
    assert z > 0
    p = tuple(w/z for w in raw)
    assert sum(p,Fraction()) == 1 and all(x > 0 for x in p)
    return p


def rational_parity_certificate(
    support: int, exponent: int, shift: int = 0
) -> dict:
    """Two independently evaluated source normalizers and PNF mass parity."""
    a,b = source_unreduced_hurwitz_fraction(support,exponent,shift)
    denoms = tuple((r+shift)**exponent for r in range(1,support+1))
    common = prod(denoms)
    independent_numerator = sum(common//d for d in denoms)
    assert (a,b) == (independent_numerator,common)
    masses = constructive_pnf_masses(support,exponent,shift)
    assert masses == tuple(Fraction(common//d,a) for d in reversed(denoms))
    assert all(m == Fraction(b,a*d) for m,d in zip(masses,reversed(denoms)))
    return {'source_fraction':(a,b),'pnf_masses':masses,
            'normalized':sum(masses,Fraction())}


def pnf_constant_expectation(
    support: int, exponent: int, shift: int, rate: Fraction
) -> Fraction:
    if type(rate) is not Fraction:
        raise ValueError('exact rational rate required')
    return sum((p*rate for p in constructive_pnf_masses(
        support,exponent,shift)),Fraction())
