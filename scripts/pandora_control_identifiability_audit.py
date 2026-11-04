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


def within_animal_fixed_effects(assignments):
    """Synthetic animal-fixed-effect design, not historic trial observations.

    Each row (animal_id, RF_field_indicator, session_period_indicator).
    Animal baseline means are unrestricted nuisance coefficients.
    Columns are one indicator per individual animal plus field and period.
    Full structural rank or target contrast estimability is not proof of
    randomisation, period washout, blinding, adequate sample size or biology.
    """
    if not assignments:
        raise ValueError('nonempty animal/trial list required')
    animals = []
    for row in assignments:
        if not isinstance(row, (tuple, list)) or len(row) != 3:
            raise ValueError('expected (animal_id, field, period)')
        animal, field, period = row
        if type(animal) is not str or not animal or not animal.strip():
            raise ValueError('nonempty string synthetic animal identity required')
        if type(field) is not int or type(period) is not int:
            raise ValueError('binary int field and period required')
        if field not in (0, 1) or period not in (0, 1):
            raise ValueError('binary field and period required')
        if animal not in animals:
            animals.append(animal)
    matrix = [
        [int(animal == label) for label in animals] + [field, period]
        for animal, field, period in assignments
    ]
    return animals, matrix


def within_animal_witness():
    """Repeated between-animal groups vs crossed vs period-aliased crossover.

    In a subject fixed-effect model, 100 repeated trials on same condition
    per subject cannot identify RF effect independently of subject baseline.
    """
    between = [(a, int(a in ('C', 'D')), 0)
               for a in ('A', 'B', 'C', 'D') for _ in range(20)]
    crossed = [(a, f, p) for a in ('A', 'B', 'C', 'D')
               for f in (0, 1) for p in (0, 1)]
    aligned = [(a, p, p) for a in ('A', 'B', 'C', 'D')
               for p in (0, 1)]
    def outcome(rows):
        animals, matrix = within_animal_fixed_effects(rows)
        effect = [0] * len(animals) + [1, 0]
        period = [0] * len(animals) + [0, 1]
        return {
            'animals': len(animals),
            'rows': len(rows),
            'rank': rank(matrix),
            'field_contrast_estimable': contrast_estimable(matrix, effect),
            'period_contrast_estimable': contrast_estimable(matrix, period),
        }
    return {
        'between_animal_only': outcome(between),
        'within_animal_crossed': outcome(crossed),
        'within_animal_period_aliased': outcome(aligned),
        'assumptions': 'linear animal-specific baselines and additive '
                       'time period; no inference about historical exposure',
        'historical_animal_data_used': False,
        'causal_rf_effect_established': False,
    }


# Transcribed directly from Eugene V. Byron (JHU/APL), November 1966,
# PROJECT PANDORA (U) Final Report MRT-4-046/QM-66-072, printed p. 15,
# original facsimile PDF page index 20, Table III, 18 tabulated rows.
# Columns: GHz, horn section, antenna gain, transmit watts, calculated
# mW/cm2, measured mW/cm2, printed Delta=(calculated - measured) mW/cm2.
# This is laboratory instrument comparison, not primate/civilian exposure.
# The model reuses measured transmitter power & horn gain; it is NOT an
# independent replication of a biological response or absolute SAR.
BYRON_1966_TABLE_III = """
2.6 D6 99.6 228 3.40 3.70 -0.30
2.7 D6 105.0 226 3.55 3.90 -0.35
2.7 D5 91.2 220 3.0 3.0 0.00
2.8 D5 95.6 216 3.09 3.2 -0.11
2.9 D5 102.0 210 3.20 2.9 +0.30
2.9 D4 89.0 236 3.14 2.85 +0.29
3.0 D4 93.5 234 3.27 3.1 +0.17
3.1 D4 100.0 232 3.47 3.35 +0.12
3.2 D3 93.5 226 3.16 3.0 +0.16
3.3 D3 100.0 232 3.47 3.45 +0.02
3.4 D2 91.2 232 3.17 3.0 +0.17
3.6 D2 102.0 236 3.61 3.6 +0.01
3.6 D1 89.0 245 3.27 3.6 -0.33
3.7 D1 95.6 260 3.71 3.6 +0.11
3.8 D1 100.0 278 4.16 4.15 +0.01
3.9 D1 105.0 250 3.93 4.0 -0.07
3.95 D1 110.0 250 4.12 4.35 -0.23
4.0 D1 112.0 250 4.19 4.25 -0.06
""".strip()


def byron_1966_table_iii_rows():
    """Original printed Table III transcribed values; not animal observations."""
    rows = []
    for line in BYRON_1966_TABLE_III.splitlines():
        values = line.split()
        if len(values) != 7:
            raise ValueError('expected seven original-table columns')
        ghz, horn, gain, watts, calculated, measured, difference = values
        if not (horn.startswith('D') and horn[1:].isdigit()):
            raise ValueError('malformed horn section')
        if type(horn) is not str:
            raise ValueError('malformed source horn')
        watts_int = int(watts)
        if watts_int <= 0:
            raise ValueError('nonpositive transmission')
        numeric = tuple(Fraction(x) for x in
                        (ghz, gain, calculated, measured, difference))
        if any(x <= 0 for x in numeric[:4]):
            raise ValueError('nonpositive source quantity')
        if numeric[2] - numeric[3] != numeric[4]:
            raise ValueError('original table delta transcription mismatch')
        rows.append((numeric[0], horn, numeric[1], watts_int,
                     numeric[2], numeric[3], numeric[4]))
    if len(rows) != 18:
        raise ValueError('original Table III must have eighteen rows')
    return rows


def byron_1966_table_iii_audit():
    rows = byron_1966_table_iii_rows()
    residuals = [row[6] for row in rows]
    return {
        'report': 'E.V. Byron JHU/APL MRT-4-046 QM-66-072 1966-11',
        'original_table': 'Table III, printed p.15, PDF index 20',
        'independent_documentary_object': True,
        'original_instrument_comparisons': len(rows),
        'frequency_ghz': [str(rows[0][0]), str(rows[-1][0])],
        'max_abs_calc_minus_meas_mW_per_cm2': str(max(map(abs, residuals))),
        'mean_calc_minus_meas_mW_per_cm2':
            str(sum(residuals) / len(residuals)),
        'mean_absolute_difference_mW_per_cm2':
            str(sum(map(abs, residuals)) / len(residuals)),
        'same_report_model_and_measured_input_not_independent_replication': True,
        'is_animal_outcome_or_moscow_1977_measurement': False,
    }



# Directly checked against E. V. Byron, JHU/APL Project PANDORA Final
# Report MRT-4-046 / QM-66-072 (Nov 1966), printed p.14, Table II.
# These are AUTHOR-REPORTED *worst-case spatial field variations* of
# different conditions, not independently measured uncertainty bars,
# measurement noise, absorbed doses, or 1977 embassy calibrations.
BYRON_1966_TABLE_II = (
    ('absorber_lined_3_8_in_plexiglas_back', '3.63'),
    ('absorber_lined_no_back', '4.88'),
    ('absorber_lined_1_16_in_plexiglas_back', '2.63'),
    ('sample_in_absorber_lined_1_16_in_container', '2.88'),
    ('sample_movement_alone', '0.88'),
)


def byron_1966_table_ii_spatial_variations():
    """Exact transcription of five Table II worst-case *spatial* dB spans."""
    if len(BYRON_1966_TABLE_II) != 5:
        raise ValueError('original Table II requires five test conditions')
    names = [name for name, _ in BYRON_1966_TABLE_II]
    if len(set(names)) != len(names):
        raise ValueError('duplicate Table II original test condition')
    rows = [(name, Fraction(magnitude))
            for name, magnitude in BYRON_1966_TABLE_II]
    if any(v <= 0 for _, v in rows):
        raise ValueError('positive observed dB variation required')
    return rows


def byron_1966_spatial_variation_witness():
    """In-report descriptive span ranking, never statistical error bars."""
    rows = byron_1966_table_ii_spatial_variations()
    largest = max(rows, key=lambda item: item[1])
    smallest = min(rows, key=lambda item: item[1])
    return {
        'original': 'Byron JHU/APL 1966 Final Report Table II, printed p.14',
        'conditions': len(rows),
        'largest_worst_case_spatial_half_span_db': str(largest[1]),
        'largest_condition': largest[0],
        'smallest_worst_case_spatial_half_span_db': str(smallest[1]),
        'smallest_condition': smallest[0],
        'not_estimated_statistical_measurement_error': True,
        'not_calibrated_Moscow_signal_or_personal_SAR': True,
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


    def test_animal_fixed_effect_between_group_repeats_not_identifiable(self):
        w = within_animal_witness()['between_animal_only']
        self.assertEqual((w['animals'], w['rows'], w['rank']), (4, 80, 4))
        self.assertFalse(w['field_contrast_estimable'])
        self.assertFalse(w['period_contrast_estimable'])

    def test_animal_fixed_effect_fully_crossed_identifiable_in_model(self):
        w = within_animal_witness()['within_animal_crossed']
        self.assertEqual((w['animals'], w['rows'], w['rank']), (4, 16, 6))
        self.assertTrue(w['field_contrast_estimable'])
        self.assertTrue(w['period_contrast_estimable'])

    def test_animal_fixed_effect_period_treatment_alias(self):
        w = within_animal_witness()['within_animal_period_aliased']
        self.assertEqual((w['animals'], w['rows'], w['rank']), (4, 8, 5))
        self.assertFalse(w['field_contrast_estimable'])
        self.assertFalse(w['period_contrast_estimable'])

    def test_animal_fixed_effect_invalid_identity_assignment(self):
        for bad in ([], [('A', 0)], [('', 0, 0)],
                    [(1, 0, 1)], [('A', True, 0)],
                    [('A', 0, 2)], [('A', 0, 0, 2)]):
            with self.assertRaises(ValueError):
                within_animal_fixed_effects(bad)

    def test_animal_fixed_effect_does_not_establish_causation(self):
        w = within_animal_witness()
        self.assertFalse(w['causal_rf_effect_established'])
        self.assertFalse(w['historical_animal_data_used'])


    def test_byron_table_iii_all_18_original_delta_rows(self):
        rows = byron_1966_table_iii_rows()
        self.assertEqual(len(rows), 18)
        self.assertTrue(all(r[4] - r[5] == r[6] for r in rows))

    def test_byron_table_iii_exact_residual_summary(self):
        audit = byron_1966_table_iii_audit()
        self.assertEqual(audit['max_abs_calc_minus_meas_mW_per_cm2'], '7/20')
        self.assertEqual(audit['mean_calc_minus_meas_mW_per_cm2'], '-1/200')
        self.assertEqual(audit['mean_absolute_difference_mW_per_cm2'],
                         '281/1800')

    def test_byron_table_iii_frequency_and_horn_range(self):
        rows = byron_1966_table_iii_rows()
        self.assertEqual(rows[0][0], Fraction('2.6'))
        self.assertEqual(rows[-1][0], Fraction('4.0'))
        self.assertEqual({r[1] for r in rows}, set('D' + str(n)
                                                  for n in range(1, 7)))

    def test_byron_table_iii_transcription_negative_control(self):
        global BYRON_1966_TABLE_III
        original = BYRON_1966_TABLE_III
        try:
            BYRON_1966_TABLE_III = original.replace(
                '3.40 3.70 -0.30', '3.40 3.70 +0.30', 1)
            with self.assertRaises(ValueError):
                byron_1966_table_iii_rows()
        finally:
            BYRON_1966_TABLE_III = original

    def test_byron_table_iii_original_not_health_causation(self):
        audit = byron_1966_table_iii_audit()
        self.assertEqual(audit['original_instrument_comparisons'], 18)
        self.assertTrue(audit[
            'same_report_model_and_measured_input_not_independent_replication'])
        self.assertFalse(audit['is_animal_outcome_or_moscow_1977_measurement'])

    def test_byron_table_ii_exact_original_five_conditions(self):
        values = dict(byron_1966_table_ii_spatial_variations())
        self.assertEqual(len(values), 5)
        self.assertEqual(values['absorber_lined_3_8_in_plexiglas_back'],
                         Fraction('3.63'))
        self.assertEqual(values['absorber_lined_no_back'], Fraction('4.88'))
        self.assertEqual(values['absorber_lined_1_16_in_plexiglas_back'],
                         Fraction('2.63'))
        self.assertEqual(values['sample_in_absorber_lined_1_16_in_container'],
                         Fraction('2.88'))
        self.assertEqual(values['sample_movement_alone'], Fraction('0.88'))

    def test_byron_table_ii_spatial_span_is_not_error_bar(self):
        evidence = byron_1966_spatial_variation_witness()
        self.assertTrue(evidence['not_estimated_statistical_measurement_error'])
        self.assertTrue(evidence['not_calibrated_Moscow_signal_or_personal_SAR'])
        self.assertEqual(evidence['largest_worst_case_spatial_half_span_db'],
                         '122/25')
        self.assertEqual(evidence['smallest_worst_case_spatial_half_span_db'],
                         '22/25')

    def test_byron_table_ii_reject_duplicate_conditions(self):
        global BYRON_1966_TABLE_II
        original = BYRON_1966_TABLE_II
        try:
            BYRON_1966_TABLE_II = original + (original[0],)
            with self.assertRaises(ValueError):
                byron_1966_table_ii_spatial_variations()
        finally:
            BYRON_1966_TABLE_II = original


if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['--selftest']:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestFiniteConfound)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        raise SystemExit(0 if result.wasSuccessful() else 1)
    if sys.argv[1:] == ['--synthetic']:
        print(json.dumps({'two_factor': synthetic_witness(),
                          'factorial': factorial_witness(),
                          'muts_1977': historical_muts_conditional_witness(),
                          'animal_fixed_effect': within_animal_witness(),
                          'byron_1966_original': byron_1966_table_iii_audit(),
                          'byron_1966_spatial': byron_1966_spatial_variation_witness()}, indent=2))
    else:
        raise SystemExit('Use --selftest or --synthetic. No human/animal exposure input.')
