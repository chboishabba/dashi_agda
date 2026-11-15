#!/usr/bin/env python3
"""Dependency-free finite regressions and negative controls for K4."""
from fractions import Fraction
from check_bsd_level32_positive_tail import (
    QMAX, LOWER_BOUND, certify, finite_eta_product, global_defect, tail_defect,
)


def test_exact_constants():
    assert global_defect(QMAX) == Fraction(12, 85)
    assert LOWER_BOUND == Fraction(73, 85)
    assert tail_defect(0) == global_defect(QMAX)
    assert tail_defect(10) < Fraction(1, 10**12)


def test_finite_products_and_tails():
    for q in (Fraction(0), Fraction(1, 256), Fraction(1, 64), QMAX):
        for n in range(12):
            p = finite_eta_product(n, q)
            assert LOWER_BOUND <= p <= 1
            for m in range(n + 1, 13):
                assert 0 <= p - finite_eta_product(m, q) <= tail_defect(n)


def test_negative_controls():
    for bad_q in (Fraction(-1, 32), Fraction(1), Fraction(9, 8)):
        try:
            global_defect(bad_q)
        except ValueError:
            pass
        else:
            raise AssertionError(f"failed to reject out-of-domain q={bad_q}")
    try:
        tail_defect(-1)
    except ValueError:
        pass
    else:
        raise AssertionError("failed to reject negative cutoff")
    assert global_defect(Fraction(1, 8)) > global_defect(QMAX)


def test_no_proof_promotion():
    report = certify(9)
    assert report["finite_fraction_regressions"]
    for key in ("same_object_modularity_proved", "bishop_exponential_and_eta_constructed",
                "mellin_identification_proved", "agda_kernel_accepted"):
        assert report[key] is False


if __name__ == '__main__':
    test_exact_constants()
    test_finite_products_and_tails()
    test_negative_controls()
    test_no_proof_promotion()
    print('PASS: exact constants, finite products, finite tail controls, negative controls, non-promotion')
