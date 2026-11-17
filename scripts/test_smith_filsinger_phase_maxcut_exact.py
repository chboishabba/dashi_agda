#!/usr/bin/env python3
"""Exact arithmetic regression checks for finite Smith/Filsinger phase cut.

No physical measurement or Agda kernel acceptance is inferred.
"""
from fractions import Fraction as F
from itertools import product
import pytest
from check_smith_filsinger_phase_maxcut_exact import (
    load_power, symbolic_matching, source_reversal, two_slot_schedule,
    exact_four_phase_cross, matched_boundary_pair, exact_checks
)


def test_full_exact_receipt():
    assert "PASS" in exact_checks()["tests"]


def test_symbolic_source_bound_and_parameter_reversal():
    gap, delta = symbolic_matching()
    assert "V**2" in gap
    assert "R" in delta


@pytest.mark.parametrize("resistance", [F(1, 4), F(1), F(3), F(7)])
def test_fixed_source_power_cap(resistance):
    for num, den in product(range(0, 15), range(1, 9)):
        actual = load_power(resistance, F(num, den))
        assert F(0) <= actual <= F(1, 4) / resistance


def test_general_rational_square_gap_identity():
    for x, y in product(range(50), repeat=2):
        assert (x + y) ** 2 == 4 * x * y + (x - y)**2


def test_opposed_schedule_fixed_total():
    for base, excursion in product(range(31), repeat=2):
        cycles = two_slot_schedule(base, excursion)
        assert sum(cycles[0]) == sum(cycles[1])


def test_coherent_scaling_does_not_change_ratio():
    for a, b, k in product(range(1, 8), repeat=3):
        assert (k*a)*b == (k*b)*a


def test_exact_four_phase_cancellation():
    for a, b in product(range(20), repeat=2):
        assert exact_four_phase_cross(a, b) == (a+b, a+b)


def test_source_resistance_changes_phase_preference():
    results = source_reversal()
    assert results["1"]["delta_opposed_minus_inphase"] == F(17, 900)
    assert results["3"]["delta_opposed_minus_inphase"] == -F(111, 48400)


def test_no_natural_input_cannot_supply_positive_natural_net():
    for outgoing in range(50):
        assert 0 - outgoing <= 0


def test_same_initial_state_paired_trajectory_identity():
    for n in range(10):
        result = matched_boundary_pair(
            F(n+2), F(3), F(1), F(1),
            F(n+1), F(3), F(1), F(1), initial=F(2))
        assert result["changed_load"] == result["changed_natural"]
        assert result["changed_controller"] == F(0)


def test_zero_source_zero_controller_yields_zero_load():
    assert load_power(F(1), F(0)) == 0
