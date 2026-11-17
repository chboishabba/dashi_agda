#!/usr/bin/env python3
"""Offline synthetic regression suite for Field Loom S1/S6 PR.

Run: python3 scripts/test_psychotronics_field_loom_gate.py
This suite never tests a physical apparatus or certifies an anomaly.
"""
import json
import math
from pathlib import Path
import tempfile
import unittest
from hashlib import sha256

from psychotronics_field_loom_coils import loop_b
from psychotronics_field_loom_metrology import force_budget, paired_analysis
from psychotronics_field_loom_covariance import correlated_residual_gls
from psychotronics_field_loom_factorial import audit_settings
from psychotronics_field_loom_source_join import verify_pair_source
from psychotronics_field_loom_observability import (
    gram_2x2, response_grid, fault_tolerant_four_sensor_layout,
)


class FieldLoomGates(unittest.TestCase):
    def test_analytic_finite_difference(self):
        budget = force_budget()
        h=0.001
        def B(z):
            return (loop_b(0,0,z,.1,-.05,100,1)[2]
                  + loop_b(0,0,z,.1,+.05,100,-1)[2])
        measured=(B(h)-B(-h))/(2*h)
        self.assertLess(abs(measured/budget['anti_coil_center_gradient_T_per_m']-1),.0002)
        self.assertLess(abs(budget['force_to_weight_abs']-.011),.0001)

    def test_shared_calibration_cannot_average_away(self):
        p={'residual_n':1e-7,'random_std_n':2e-7,
           'moment_am2':.01,'moment_gradient_t_m':-.01,
           'moment_std_am2':.001,'moment_calibration_id':'shared'}
        a=correlated_residual_gls([p])
        b=correlated_residual_gls([p]*16)
        self.assertLess(b['random_std_n'],a['random_std_n'])
        self.assertAlmostEqual(b['shared_moment_calibration_std_n'],1e-5,places=12)
        self.assertGreater(b['total_std_n'],9.9e-6)
        c=correlated_residual_gls([{**p,'moment_calibration_id':str(i)} for i in range(4)])
        self.assertAlmostEqual(c['shared_moment_calibration_std_n'],5e-6,places=12)

    def test_factorial_rank_does_not_grow_with_repeats(self):
        arms=[{'coil_sign':c,'dipole_sign':m} for c in (-1,0,1) for m in (-1,1)]
        self.assertEqual(audit_settings(arms)['rank'],5)
        poor=[{'coil_sign':c,'dipole_sign':1} for c in (0,1)]
        self.assertEqual(audit_settings(poor*15)['rank'],2)

    def test_gram_stability_and_fault_robustness(self):
        mid=gram_2x2(response_grid((0.,)))
        self.assertEqual(mid['numerical_rank'],1)
        self.assertEqual(gram_2x2([(1,2),(2,4)])['numerical_rank'],1)
        self.assertEqual(gram_2x2([(0,0),(0,0)])['numerical_rank'],0)
        layout=fault_tolerant_four_sensor_layout()
        self.assertEqual(layout['examined_layouts'],17550)
        self.assertTrue(layout['all_single_failure_cases_rank_2'])
        self.assertAlmostEqual(layout['one_sensor_failure_maximin_min_singular_t_per_A'],
                               0.0001954629955,places=11)

    def test_source_pair_calibration_weld(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td)
            stream=root/'sensor.csv'
            stream.write_text('time_s,force_n\n0,0\n1,0\n')
            pairs=[{'pair_id':'A','moment_calibration_id':'one','moment_am2':.01,
                    'moment_std_am2':.001,'common_systematic_std_n':1e-6}]
            raw={'apparatus_id':'a','configuration_revision':'rev','instrument_serial':'serial',
                 'pairs':pairs,'instrument_source_stream_file':str(stream),
                 'instrument_source_stream_sha256':sha256(stream.read_bytes()).hexdigest()}
            cal={'apparatus_id':'a','configuration_revision':'rev','instrument_serial':'serial',
                 'calibration_revision':'cal','common_force_offset_std_n':3e-6,
                 'gradient_calibration_fractional_std':.02,
                 'moment_calibration_groups':{'one':{'moment_am2':.01,'moment_std_am2':.001}}}
            data=root/'data.json'; calibr=root/'cal.json'
            data.write_text(json.dumps(raw));calibr.write_text(json.dumps(cal))
            meta={'apparatus_id':'a','configuration_revision':'rev','instrument_serial':'serial',
                  'calibration_revision':'cal','gradient_calibration_fractional_std':.02,
                  'raw_data_file':str(data),'calibration_file':str(calibr),
                  'raw_data_sha256':sha256(data.read_bytes()).hexdigest(),
                  'calibration_sha256':sha256(calibr.read_bytes()).hexdigest()}
            good=verify_pair_source(meta,pairs)
            self.assertTrue(good['bytes_and_exact_pair_source_join'])
            self.assertEqual(good['calibration_reported_common_force_offset_std_n'],3e-6)
            self.assertFalse(good['independent_instrument_authentication'])
            self.assertFalse(verify_pair_source(meta,[{**pairs[0],'moment_am2':.02}])
                             ['bytes_and_exact_pair_source_join'])
            stream.write_text('tampered')
            self.assertFalse(verify_pair_source(meta,pairs)['bytes_and_exact_pair_source_join'])

    def test_synthetic_anomaly_promotion_blocked(self):
        p={'pair_id':'p1','session_id':'s1','moment_am2':.01,
           'moment_std_am2':.001,'common_systematic_std_n':2e-6,
           'active':{'force_n':-.000108,'force_std_n':1e-6,
                     'gradient_t_m':-.01079,'gradient_std_t_m':.0001},
           'sham':{'force_n':0,'force_std_n':1e-6,
                   'gradient_t_m':0,'gradient_std_t_m':.0001}}
        response=paired_analysis({'metadata':{'origin':'synthetic','apparatus_id':'X',
                                              'configuration_revision':'idealised'},
                                  'pairs':[p]})
        self.assertFalse(response['submission_ready_for_independent_metrology_review'])
        self.assertFalse(response['gravitational_result_admissible'])
        self.assertIn('unverified_raw_to_pair_reduction',response['unpaid_obligations'])
        self.assertIn('synthetic_input_cannot_support_empirical_detection',
                      response['unpaid_obligations'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
