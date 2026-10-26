#!/usr/bin/env python3
"""Finite synthetic design diagnostics motivated by PANDORA's 1969-70 review.

NOT recovered animal records, a biological effect, human trial, or a physical
measurement. Original sources: Kubis (1969-12-04); Peterson committee meeting
(1970-01-12, typed 1970-03-23); Chanda correction (1970-03-31).
The source authors did not publish these synthetic calculations.
"""
from fractions import Fraction
import json
import unittest


def rank(matrix):
    if not matrix:
        return 0
    n = len(matrix[0])
    if any(len(row) != n for row in matrix):
        raise ValueError('nonrectangular matrix')
    a = [[Fraction(x) for x in row] for row in matrix]
    pivot = 0
    for col in range(n):
        row = next((i for i in range(pivot, len(a)) if a[i][col]), None)
        if row is None:
            continue
        a[pivot], a[row] = a[row], a[pivot]
        factor = a[pivot][col]
        a[pivot] = [x / factor for x in a[pivot]]
        for i in range(len(a)):
            if i == pivot:
                continue
            factor = a[i][col]
            a[i] = [x - factor * y for x, y in zip(a[i], a[pivot])]
        pivot += 1
        if pivot == len(a):
            break
    return pivot


def design(assignments):
    """Rows are (field_on, time_period), not calibrated observations."""
    if not assignments or any(len(row) != 2 or any(x not in (0, 1) for x in row)
                              for row in assignments):
        raise ValueError('binary exposure/period assignments required')
    return [[1, field, period] for field, period in assignments]


def predict(assignments, intercept, field_effect, period_effect):
    return [Fraction(intercept + field_effect * field + period_effect * period)
            for field, period in assignments]


def synthetic_witness():
    confounded = [(0, 0), (0, 0), (1, 1), (1, 1)]
    balanced = [(0, 0), (0, 1), (1, 0), (1, 1)]
    observations_a = predict(confounded, 10, 0, 2)
    observations_b = predict(confounded, 10, 2, 0)
    assert observations_a == observations_b
    assert rank(design(confounded)) == 2
    assert rank(design(balanced)) == 3
    return {
        'confounded_rank': 2,
        'balanced_rank': 3,
        'confounded_observations': list(map(int, observations_a)),
        'alternative_physical_interpretations_fit_identically': True,
        'historical_primate_effect_established': False,
        'clinical_or_rf_acoustic_interaction_established': False,
        'notes': 'Synthetic independent design-identifiability example only; '
                 'no actual PANDORA trial baselines reconstructed.'
    }


class TestFiniteConfound(unittest.TestCase):
    def test_original_baseline_confounded(self):
        self.assertEqual(rank(design([(0, 0), (0, 0), (1, 1)])), 2)

    def test_balanced_design(self):
        self.assertEqual(rank(design([(0, 0), (0, 1), (1, 0), (1, 1)])), 3)

    def test_same_response_different_causes(self):
        a = [(0, 0), (1, 1)]
        self.assertEqual(predict(a, 10, 0, 2), predict(a, 10, 2, 0))

    def test_balanced_separates_interpretations(self):
        a = [(0, 0), (0, 1), (1, 0), (1, 1)]
        self.assertNotEqual(predict(a, 10, 0, 2), predict(a, 10, 2, 0))

    def test_permuted_order_keeps_rank(self):
        a = [(0, 0), (0, 1), (1, 0), (1, 1)]
        self.assertEqual(rank(design(a)), rank(design(a[::-1])))

    def test_malformed_assignments(self):
        for value in ([], [(1, 2)], [(1,)], [(0, 1, 0)]):
            with self.assertRaises(ValueError):
                design(value)

    def test_nonrectangular_rejected(self):
        with self.assertRaises(ValueError):
            rank([[1], [1, 2]])

    def test_no_empirical_promotion(self):
        self.assertFalse(synthetic_witness()['historical_primate_effect_established'])


if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['--selftest']:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestFiniteConfound)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        raise SystemExit(0 if result.wasSuccessful() else 1)
    if sys.argv[1:] == ['--synthetic']:
        print(json.dumps(synthetic_witness(), indent=2))
    else:
        raise SystemExit('Use --selftest or --synthetic. No human/animal exposure input.')
