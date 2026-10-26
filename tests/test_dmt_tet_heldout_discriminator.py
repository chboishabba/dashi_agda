"""Synthetic-only DMT-TET held-out model comparison regressions."""
import copy
import unittest

from scripts.audit_dmt_tet_presence_synthetic import DIMENSIONS, CODE_COMMIT, CONFIG_BLOB, SCHEMA
from scripts.dmt_tet_heldout_discriminator import audit, build_rows, heldout, FEATURES


def fixture():
    samples = []
    for person in ('toy-person-A', 'toy-person-B', 'toy-person-C'):
        for dose in (20, 40):
            for stage in ('RS', 'DMT'):
                for t in range(5):
                    values = {k: '0' for k in DIMENSIONS}
                    values['general_intensity'] = '6' if stage == 'DMT' else '0'
                    values['complex_imagery'] = '7' if stage == 'DMT' and t > 0 else '0'
                    values['salience'] = '7' if stage == 'DMT' and t > 1 else '0'
                    values['entity'] = '7' if stage == 'DMT' and t > (2 if person == 'toy-person-C' else 1) else '0'
                    samples.append({'person': person, 'dose_mg': dose,
                                    'stage': stage, 'time_index': t, 'values': values})
    return {'schema': SCHEMA, 'mode': 'synthetic', 'source_id': 'synthetic:three',
            'code_commit': CODE_COMMIT, 'config_blob': CONFIG_BLOB,
            'interval_seconds': 4, 'dimensions': list(DIMENSIONS),
            'threshold': '5', 'samples': samples}


class HeldoutDiscriminatorTests(unittest.TestCase):
    def test_subject_exclusion(self):
        out = audit(fixture())
        self.assertEqual(len(out['folds']), 3)
        self.assertEqual([f['n_test_transitions'] for f in out['folds']], [8, 8, 8])
        self.assertFalse(out['original_human_data_analysed'])

    def test_permutation_of_input_rows(self):
        a = fixture(); b = copy.deepcopy(a); b['samples'].reverse()
        self.assertEqual(audit(a)['folds'], audit(b)['folds'])

    def test_one_extra_feature_future_is_not_read(self):
        a = fixture(); base = audit(a)['folds']
        for r in a['samples']:
            if r['stage'] == 'DMT' and r['time_index'] == 4:
                r['values']['complex_imagery'] = '1'
                r['values']['salience'] = '2'
                r['values']['general_intensity'] = '3'
        self.assertEqual(base, audit(a)['folds'])

    def test_model_feature_count_is_seven(self):
        self.assertTrue(all(len(v) == 7 for v in FEATURES.values()))
        self.assertFalse(audit(fixture())['model_capacity_equal_in_all_respects'])

    def test_previous_entity_is_shared_autoregressive_control(self):
        self.assertIn('entity', FEATURES['M0_nuisance_proxy'])
        self.assertIn('entity', FEATURES['M1a_endogenous_proxy'])

    def test_next_entity_is_not_current_entity(self):
        d = fixture()
        rows = build_rows(d)
        first = [r for r in rows if r['person'] == 'toy-person-A' and r['dose'] == 20][0]
        self.assertEqual(first['entity'], 0)
        self.assertEqual(first['target'], 0)
        second = [r for r in rows if r['person'] == 'toy-person-A' and r['dose'] == 20][1]
        self.assertEqual(second['entity'], 0)
        self.assertEqual(second['target'], 1)

    def test_training_only_predictions_are_fractions(self):
        f = audit(fixture())['folds'][0]
        for result in f['models'].values():
            self.assertEqual(len(result['predictions_exact']), 8)
            self.assertTrue(result['unseen_cell_fallback_training_only'])

    def test_heldout_label_tamper_does_not_change_own_predictions(self):
        before = build_rows(fixture())
        edited = copy.deepcopy(before)
        for row in edited:
            if row['person'] == 'toy-person-A':
                row['target'] = 1 - row['target']
        original = next(f for f in heldout(before) if f['held_out_person'] == 'toy-person-A')
        changed = next(f for f in heldout(edited) if f['held_out_person'] == 'toy-person-A')
        for model in FEATURES:
            self.assertEqual(original['models'][model]['predictions_exact'],
                             changed['models'][model]['predictions_exact'])

    def test_partial_outcome_samples_do_not_become_independent_people(self):
        data = fixture()
        result = audit(data)
        self.assertEqual(sum(f['n_test_transitions'] for f in result['folds']), 24)
        self.assertEqual(len(result['folds']), 3)
        self.assertTrue(result['within_subject_targets_not_independent_samples'])

    def test_non_target_dimension_future_not_used(self):
        data = fixture()
        initial = audit(data)['folds']
        for sample in data['samples']:
            if sample['stage'] == 'DMT' and sample['time_index'] == 4:
                sample['values']['selfhood'] = '9'
                sample['values']['pleasantness'] = '9'
                sample['values']['anxiety'] = '9'
        self.assertEqual(initial, audit(data)['folds'])

    def test_reject_real_mode(self):
        d = fixture(); d['mode'] = 'authorized_research'
        with self.assertRaises(ValueError):
            audit(d)

    def test_reject_missing_time(self):
        d = fixture(); d['samples'] = [r for r in d['samples'] if not (
            r['person'] == 'toy-person-C' and r['dose_mg'] == 40 and r['stage'] == 'DMT' and r['time_index'] == 3)]
        with self.assertRaises(ValueError):
            audit(d)

    def test_reject_single_sample_dmt_episode(self):
        d = fixture(); d['samples'] = [r for r in d['samples'] if not (
            r['person'] == 'toy-person-A' and r['dose_mg'] == 20 and r['stage'] == 'DMT' and r['time_index'] > 0)]
        with self.assertRaises(ValueError):
            audit(d)

    def test_reject_duplicate_person_bin(self):
        d = fixture(); d['samples'].append(copy.deepcopy(d['samples'][0]))
        with self.assertRaises(ValueError):
            audit(d)

    def test_new_person_without_doses_rejected(self):
        d = fixture(); d['samples'][0]['person'] = 'toy-person-D'
        with self.assertRaises(ValueError):
            audit(d)

    def test_training_stratum_coverage_denominators(self):
        report = audit(fixture())
        for fold in report['folds']:
            for model in fold['models'].values():
                n = fold['n_test_transitions']
                self.assertEqual(model['heldout_seen_strata_count'] +
                                 model['heldout_unseen_strata_count'], n)
                from fractions import Fraction
                self.assertEqual(Fraction(model['heldout_exact_stratum_coverage']),
                                 Fraction(model['heldout_seen_strata_count'], n))

    def test_unseen_heldout_strata_fall_back_without_lookahead(self):
        rows = build_rows(fixture())
        for row in rows:
            if row['person'] == 'toy-person-A':
                for f in ('pleasantness', 'unpleasantness', 'anxiety', 'selfhood'):
                    row[f] = 1
        held = next(x for x in heldout(rows) if x['held_out_person'] == 'toy-person-A')
        for model in held['models'].values():
            self.assertEqual(model['heldout_seen_strata_count'], 0)
            self.assertEqual(model['heldout_exact_stratum_coverage'], '0')
            self.assertEqual(len(set(model['predictions_exact'])), 1)

    def test_predeclared_clock_does_not_use_test_episode_length(self):
        rows = build_rows(fixture())
        self.assertTrue(all(r['time'] == 0 for r in rows))
        self.assertIn('600 seconds', audit(fixture())['time_threshold_source_defined_not_heldout_length'])

    def test_positive_signal_can_distinguish_proxy_predictions(self):
        rows = []
        for i in range(4):
            for dose in (20, 40):
                for image in (0, 1):
                    row = {'person': 'toy-person-'+str(i), 'dose': dose,
                           'target': image, 'time': 0}
                    for f in set(FEATURES['M0_nuisance_proxy'] +
                                 FEATURES['M1a_endogenous_proxy']) - {'dose', 'time'}:
                        row[f] = 0
                    row['complex_imagery'] = image
                    rows.append(row)
        folds = heldout(rows)
        self.assertEqual(len(folds), 4)
        self.assertTrue(all(f['distinct_proxy_predictions'] > 0 for f in folds))
        from fractions import Fraction
        self.assertTrue(all(Fraction(f['exact_brier_M0_minus_M1a']) > 0 for f in folds))

    def test_synthetic_only_claim_ceilings(self):
        r = audit(fixture())
        self.assertFalse(r['M1a_full_mechanistic_implementation'])
        self.assertFalse(r['M1b_observational_ceiling_disproved'])
        self.assertFalse(r['M2_external_agent_fitted'])
        self.assertFalse(r['future_information_leakage_allowed'])


if __name__ == '__main__':
    unittest.main()
