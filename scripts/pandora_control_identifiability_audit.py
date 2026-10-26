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


def factorial_design(assignments):
    """Synthetic rows: (higher_dose, rf_modulated, later_period).

    Columns: intercept, dose, modulation, period, dose*modulation.
    This is NOT a PANDORA trial dataset, calibrated RF model or estimate.
    """
    if not assignments or any(
        len(row) != 3 or any(type(x) is not int or x not in (0, 1) for x in row)
        for row in assignments
    ):
        raise ValueError('binary dose/modulation/period triples required')
    return [[1, d, m, p, d * m] for d, m, p in assignments]


def contrast_estimable(matrix, contrast):
    """Exact row-space test for one linear coefficient contrast.

    A contrast is identifiable only when it lies in the row space of X.
    In particular, repeating the same animal/trial configuration cannot
    rescue structural rank deficiency; nor does full rank prove causation.
    """
    if not matrix or not matrix[0] or len(contrast) != len(matrix[0]):
        raise ValueError('contrast dimension must match nonempty design')
    if any(len(row) != len(contrast) for row in matrix):
        raise ValueError('nonrectangular design')
    return rank(matrix) == rank(matrix + [list(contrast)])


def factorial_witness():
    """Named synthetic contrasts, deliberately detached from historical data."""
    aliased = [(0, 0, 0)] * 4 + [(1, 1, 1)] * 4
    full = [(d, m, p) for d in (0, 1) for m in (0, 1)
            for p in (0, 1)]
    interaction = (0, 0, 0, 0, 1)
    period = (0, 0, 0, 1, 0)
    return {
        'model': 'intercept + dose + modulation + period + dose:modulation',
        'aliased_rank': rank(factorial_design(aliased)),
        'full_rank': rank(factorial_design(full)),
        'aliased_interaction_estimable': contrast_estimable(
            factorial_design(aliased), interaction),
        'full_interaction_estimable': contrast_estimable(
            factorial_design(full), interaction),
        'full_period_estimable': contrast_estimable(
            factorial_design(full), period),
        'historical_effect_established': False,
        'historical_null_effect_established': False,
        'historical_animal_level_data_used': False,
        'note': 'Exact synthetic design algebra, not a biological null, '
                'replication, or evidence of human behavioural control.'
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


    def test_factorial_fully_crossed_identifiable(self):
        sample = [(d, m, p) for d in (0, 1) for m in (0, 1)
                  for p in (0, 1)]
        matrix = factorial_design(sample)
        self.assertEqual(rank(matrix), 5)
        for col in range(5):
            contrast = [int(i == col) for i in range(5)]
            self.assertTrue(contrast_estimable(matrix, contrast))

    def test_factorial_dose_modulation_period_alias(self):
        sample = [(0, 0, 0)] * 8 + [(1, 1, 1)] * 8
        matrix = factorial_design(sample)
        self.assertEqual(rank(matrix), 2)
        self.assertFalse(contrast_estimable(matrix, (0, 0, 0, 0, 1)))
        self.assertFalse(contrast_estimable(matrix, (0, 0, 0, 1, 0)))

    def test_more_trials_do_not_make_more_independent_conditions(self):
        minimal = factorial_design([(0, 0, 0), (1, 1, 1)])
        repeated = factorial_design([(0, 0, 0)] * 100 + [(1, 1, 1)] * 100)
        self.assertEqual(rank(minimal), rank(repeated))
        self.assertFalse(contrast_estimable(repeated, (0, 0, 0, 0, 1)))

    def test_specific_contrast_may_be_estimable_without_all_coefficients(self):
        same_period = factorial_design([(d, m, 0) for d in (0, 1)
                                         for m in (0, 1)])
        self.assertEqual(rank(same_period), 4)
        self.assertTrue(contrast_estimable(same_period, (0, 0, 0, 0, 1)))
        self.assertFalse(contrast_estimable(same_period, (0, 0, 0, 1, 0)))

    def test_factorial_rejects_unverified_input_shapes(self):
        for bad in ([], [(0, 0)], [(0, 0, 0, 0)],
                    [(0, True, 1)], [(1, 2, 0)]):
            with self.assertRaises(ValueError):
                factorial_design(bad)
        with self.assertRaises(ValueError):
            contrast_estimable([[1, 0]], (1, 0, 0))

    def test_factorial_never_claims_historical_null(self):
        witness = factorial_witness()
        self.assertEqual(witness['aliased_rank'], 2)
        self.assertEqual(witness['full_rank'], 5)
        self.assertFalse(witness['historical_effect_established'])
        self.assertFalse(witness['historical_null_effect_established'])
        self.assertFalse(witness['historical_animal_level_data_used'])


if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['--selftest']:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestFiniteConfound)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        raise SystemExit(0 if result.wasSuccessful() else 1)
    if sys.argv[1:] == ['--synthetic']:
        print(json.dumps({'two_factor': synthetic_witness(),
                          'factorial': factorial_witness()}, indent=2))
    else:
        raise SystemExit('Use --selftest or --synthetic. No human/animal exposure input.')
