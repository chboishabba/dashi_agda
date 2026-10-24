#!/usr/bin/env python3
"""Exact finite projective-qubit ABL/postselection fixture.

The prepared state is |+>=(|0>+|1>)/sqrt(2). An intermediate Z
projective measurement has outcomes k=0,1. A later Z measurement yields
f=0,1. The common 1/sqrt(2) factor is removed before squaring amplitudes.
Conditional ABL statistics are derived from *observed* final outcomes;
there is no freely controlled earlier-event intervention.
"""
from fractions import Fraction
import unittest

OUTCOMES = (0, 1)

def bare_transition_amplitude(final: int, intermediate: int) -> int:
    """sqrt(2)*<final|P_intermediate|+> for Z projectors."""
    if final not in OUTCOMES or intermediate not in OUTCOMES:
        raise ValueError("outcome outside Z basis")
    return int(final == intermediate)

def joint_weight(final: int, intermediate: int) -> Fraction:
    """P(final, intermediate|preselected +) with Z measurement at both times."""
    amplitude = bare_transition_amplitude(final, intermediate)
    return Fraction(amplitude * amplitude, 2)

def abl_probability(intermediate: int, selected_final: int) -> Fraction:
    numerator = joint_weight(selected_final, intermediate)
    denominator = sum((joint_weight(selected_final, k) for k in OUTCOMES), Fraction())
    if denominator == 0:
        raise ZeroDivisionError("inadmissible postselection")
    return numerator / denominator

def marginal_intermediate(intermediate: int) -> Fraction:
    """No postselection: sum over complete final Z outcomes."""
    return sum((joint_weight(f, intermediate) for f in OUTCOMES), Fraction())

def witness() -> dict:
    return {
        "ABL_given_final_0": [str(abl_probability(k, 0)) for k in OUTCOMES],
        "ABL_given_final_1": [str(abl_probability(k, 1)) for k in OUTCOMES],
        "Born_unconditioned": [str(marginal_intermediate(k)) for k in OUTCOMES],
        "later_filter_equals_freely_set_final_outcome": False,
        "operational_retrocausal_signal_proved": False,
    }

class QubitABLTests(unittest.TestCase):
    def test_amplitude_table(self):
        self.assertEqual([[bare_transition_amplitude(f, k) for k in OUTCOMES]
                          for f in OUTCOMES], [[1, 0], [0, 1]])

    def test_joint_table(self):
        self.assertEqual([[joint_weight(f, k) for k in OUTCOMES]
                          for f in OUTCOMES], [[Fraction(1, 2), Fraction(0)],
                                               [Fraction(0), Fraction(1, 2)]])

    def test_joint_normalization(self):
        self.assertEqual(sum((joint_weight(f, k) for f in OUTCOMES
                             for k in OUTCOMES), Fraction()), Fraction(1))

    def test_abl_conditionals_differ(self):
        self.assertEqual([abl_probability(k, 0) for k in OUTCOMES],
                         [Fraction(1), Fraction(0)])
        self.assertEqual([abl_probability(k, 1) for k in OUTCOMES],
                         [Fraction(0), Fraction(1)])

    def test_final_marginal_recovers_born(self):
        self.assertEqual([marginal_intermediate(k) for k in OUTCOMES],
                         [Fraction(1, 2), Fraction(1, 2)])

    def test_reject_invalid_basis_outcomes(self):
        with self.assertRaises(ValueError):
            bare_transition_amplitude(0, 2)

    def test_nonpromotion(self):
        result = witness()
        self.assertFalse(result["later_filter_equals_freely_set_final_outcome"])
        self.assertFalse(result["operational_retrocausal_signal_proved"])

if __name__ == "__main__":
    unittest.main(verbosity=2)
