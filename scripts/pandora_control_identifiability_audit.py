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


def muts_mode_episode_window(
        count, min_minutes, max_minutes, conditional_spot_power=None):
    """Exact, synthetic *conditional* 1977 exposure-bound algebra.

    4 Oct 1977 Moscow 14515 reports 14 previous MUTS-2 high-mode occurrences
    of 5-30 minutes with NO direct prior high-mode RF power measurements.
    The document's 3.15-5.70 uW/cm2 belongs to a separate same-day spot
    measurement reported by telegram, citing unavailable MOSCOW 14513.
    Without a transfer assumption this routine MUST NOT give a finite
    upper bound on prior fluence, biological dose, or actual human exposure.

    If a caller *explicitly* applies the same-day spot-power interval to
    all earlier mode-only episodes, output is a **counterfactual range**,
    not a recovered observation. Pointwise time/power correlation ignored
    only because all values are fixed to the caller's hypothetical bounds.
    """
    if type(count) is not int or count < 1:
        raise ValueError('positive integer event count required')
    if type(min_minutes) not in (int, str, Fraction) or type(max_minutes) not in (int, str, Fraction):
        raise ValueError('exact int/str/Fraction durations required; no floats or booleans')
    try:
        dmin, dmax = Fraction(min_minutes), Fraction(max_minutes)
    except (TypeError, ValueError, ZeroDivisionError, OverflowError) as exc:
        raise ValueError('positive finite duration bounds required') from exc
    if not (0 < dmin <= dmax):
        raise ValueError('duration interval must be positive and ordered')
    duration = (count * dmin, count * dmax)
    result = {
        'event_count': count,
        'duration_min': [str(x) for x in duration],
        'earlier_power_directly_measured': False,
        'unconditional_fluence_upper_bound': None,
        'unconditional_individual_dose_established': False,
        'conditional_spot_transfer': conditional_spot_power is not None,
        'conditional_fluence_mJ_per_cm2': None,
    }
    if conditional_spot_power is not None:
        if not isinstance(conditional_spot_power, (list, tuple)) or len(conditional_spot_power) != 2:
            raise ValueError('explicit spot power interval required')
        if any(type(x) not in (int, str, Fraction) for x in conditional_spot_power):
            raise ValueError('exact int/str/Fraction power required; no floats or booleans')
        try:
            pmin, pmax = [Fraction(x) for x in conditional_spot_power]
        except (TypeError, ValueError, ZeroDivisionError, OverflowError) as exc:
            raise ValueError('finite spot power interval required') from exc
        if not (0 <= pmin <= pmax):
            raise ValueError('spot power interval must be nonnegative and ordered')
        # uW/cm2 x minutes x 60s/min / 1000 = mJ/cm2
        lower = pmin * duration[0] * Fraction(60, 1000)
        upper = pmax * duration[1] * Fraction(60, 1000)
        result['conditional_fluence_mJ_per_cm2'] = [
            str(lower), str(upper)]
    return result


def historical_muts_conditional_witness():
    """Metadata from 1977 telegram + EXPLICIT nonhistorical transfer model."""
    no_transfer = muts_mode_episode_window(14, 5, 30)
    hypothetical = muts_mode_episode_window(
        14, 5, 30, conditional_spot_power=('3.15', '5.70'))
    return {
        'source': 'US Embassy Moscow telegram 14515 dated 1977-10-04',
        'spot_measurement_parent': 'MOSCOW 14513 not yet obtained',
        'high_mode_indications': 14,
        'mode_only_no_transfer': no_transfer,
        'transferred_spot_range_hypothesis_only': hypothetical,
        'not_an_observed_individual_dose_or_biological_outcome': True,
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


    def test_muts_no_finite_fluence_without_prior_power(self):
        result = muts_mode_episode_window(14, 5, 30)
        self.assertEqual(result['duration_min'], ['70', '420'])
        self.assertFalse(result['earlier_power_directly_measured'])
        self.assertIsNone(result['unconditional_fluence_upper_bound'])
        self.assertIsNone(result['conditional_fluence_mJ_per_cm2'])

    def test_muts_explicit_spot_transfer_is_only_conditional(self):
        result = muts_mode_episode_window(
            14, 5, 30, conditional_spot_power=('3.15', '5.70'))
        self.assertEqual(result['conditional_fluence_mJ_per_cm2'],
                         ['1323/100', '3591/25'])
        self.assertIsNone(result['unconditional_fluence_upper_bound'])
        self.assertFalse(result['unconditional_individual_dose_established'])

    def test_muts_duration_endpoint_cannot_be_relabelled_measured(self):
        a = muts_mode_episode_window(14, 5, 30)
        b = muts_mode_episode_window(28, 5, 30)
        self.assertEqual(b['duration_min'], ['140', '840'])
        self.assertIsNone(a['unconditional_fluence_upper_bound'])
        self.assertIsNone(b['unconditional_fluence_upper_bound'])

    def test_muts_individual_exposure_never_claimed(self):
        witness = historical_muts_conditional_witness()
        self.assertEqual(witness['spot_measurement_parent'],
                         'MOSCOW 14513 not yet obtained')
        self.assertTrue(witness['not_an_observed_individual_dose_or_biological_outcome'])
        self.assertFalse(witness['mode_only_no_transfer']['conditional_spot_transfer'])
        self.assertTrue(witness['transferred_spot_range_hypothesis_only']
                        ['conditional_spot_transfer'])

    def test_muts_invalid_count_and_durations_rejected(self):
        for n in (0, -1, True, 1.5):
            with self.assertRaises(ValueError):
                muts_mode_episode_window(n, 5, 30)
        for lower, upper in ((0, 30), (40, 30), (-1, 2), ('bad', 30),
                             (True, 30), (0.1, 30)):
            with self.assertRaises(ValueError):
                muts_mode_episode_window(14, lower, upper)

    def test_muts_invalid_spot_transfer_power_rejected(self):
        for power in ((-1, 2), (3, 2), (1,), '3.15', ('NaN', 4),
                      (True, 2), (0.1, 2)):
            with self.assertRaises(ValueError):
                muts_mode_episode_window(14, 5, 30, power)


if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['--selftest']:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestFiniteConfound)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        raise SystemExit(0 if result.wasSuccessful() else 1)
    if sys.argv[1:] == ['--synthetic']:
        print(json.dumps({'two_factor': synthetic_witness(),
                          'factorial': factorial_witness(),
                          'muts_1977': historical_muts_conditional_witness()}, indent=2))
    else:
        raise SystemExit('Use --selftest or --synthetic. No human/animal exposure input.')
