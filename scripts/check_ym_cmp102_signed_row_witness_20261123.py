#!/usr/bin/env python3
"""Exact finite CMP102 signed-row index weld.

Checks the rank-1 complementary-index algebra used by
DASHI/Physics/YangMills/BalabanCMP102BishopShiftedCoefficientExact.agda:
signedEvenRow = evenPart, signedOddRow = -oddPart, inclusive row
cancellation, and the shifted-bracket zero. Finite rational reference only;
not an Agda kernel receipt and not an analytic/physical CMP102 attachment.
"""
import sympy as S


def a_coefficient(n):
    return S.Rational(1, S.factorial(2 * (n + 1)))


def b_coefficient(n):
    return S.Rational(1, S.factorial(2 * (n + 1) + 1))


def cauchy(left, right, n):
    return sum((left(r) * right(n - r) for r in range(n + 1)), S.Rational(0))


def even_part(n):
    if n == 0:
        return 2 * a_coefficient(0)
    return 2 * a_coefficient(n) + cauchy(a_coefficient, a_coefficient, n - 1)


def odd_part(n):
    if n == 0:
        return S.Rational(1)
    if n == 1:
        return 2 * b_coefficient(0)
    return 2 * b_coefficient(n - 1) + cauchy(b_coefficient, b_coefficient, n - 2)


def signed_term(m, j):
    return S.Rational((-1) ** (m - j), S.factorial(j) * S.factorial(m - j))


def signed_even_row(n):
    m = 2 * (n + 1)
    return sum((signed_term(m, 2 * r) for r in range(n + 1)), S.Rational(0)) + signed_term(m, m)


def signed_odd_row(n):
    m = 2 * (n + 1)
    return sum((signed_term(m, 2 * r + 1) for r in range(n + 1)), S.Rational(0))


def main():
    total = 128
    even_ok = odd_ok = cancel_ok = bracket_ok = 0
    for n in range(total):
        m = 2 * (n + 1)
        even = signed_even_row(n)
        odd = signed_odd_row(n)
        expected_even = even_part(n)
        expected_odd = -odd_part(n)
        if S.simplify(even - expected_even) == 0:
            even_ok += 1
        if S.simplify(odd - expected_odd) == 0:
            odd_ok += 1
        if S.simplify(even + odd) == 0:
            cancel_ok += 1
        if S.simplify(odd_part(n) - even_part(n)) == 0:
            bracket_ok += 1
        assert sum(
            (signed_term(m, j) for j in range(m + 1)), S.Rational(0)
        ) == 0

    assert (even_ok, odd_ok, cancel_ok, bracket_ok) == (total,) * 4
    print(
        f"PASS exact CMP102 signed-row weld: {even_ok}/{total} signedEvenRow=evenPart, "
        f"{odd_ok}/{total} signedOddRow=-oddPart, {cancel_ok}/{total} row cancellations, "
        f"{bracket_ok}/{total} shifted-bracket zeros"
    )


if __name__ == "__main__":
    main()
