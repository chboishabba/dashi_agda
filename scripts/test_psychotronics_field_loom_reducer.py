#!/usr/bin/env python3
"""Synthetic, offline S1 raw-stream reduction regressions (not instrument tests)."""
import unittest
import json
import tempfile
from pathlib import Path
from hashlib import sha256
from psychotronics_field_loom_reducer import replay_si_csv, VERSION
from psychotronics_field_loom_source_join import verify_pair_source
from psychotronics_field_loom_metrology import paired_analysis

HEADER = 'pair_id,session_id,condition,time_ns,coil_current_a,dipole_sign,force_n,gradient_t_m,moment_calibration_id'


def calibration():
    return {'moment_calibration_groups': {
        'pos': {'moment_am2': .01, 'moment_std_am2': .001, 'shared_magnitude_id':'magnet-A'},
        'neg': {'moment_am2': -.01, 'moment_std_am2': .001, 'shared_magnitude_id':'magnet-A'}},
        'force_readout_std_n':1e-6, 'gradient_readout_std_t_m':1e-4,
        'common_force_offset_std_n':2e-6,
        'coil_sham_max_abs_a':.002, 'coil_active_min_abs_a':.1,
        'max_pair_gap_ns':1000}


def rows():
    result=[HEADER]
    t=10
    for i,(current,sign) in enumerate(((1,1),(-1,1),(1,-1),(-1,-1))):
        for condition,c in (('sham',0),('active',current)):
            result.append(f'p{i},s{i//2},{condition},{t},{c},{sign},0,0,{"pos" if sign==1 else "neg"}')
            t+=5
    return result


def replay(lines=None, cal=None):
    raw={'pair_to_stream_reducer': VERSION, 'stream_unit_convention': 'SI'}
    return replay_si_csv(("\n".join(rows() if lines is None else lines)+"\n").encode(),
                         raw, calibration() if cal is None else cal)


class ReducerTest(unittest.TestCase):
    def test_two_sessions_four_pairs_six_arms(self):
        result=replay()
        self.assertEqual(result['row_count'],8)
        self.assertEqual(len(result['pairs']),4)
        self.assertEqual(len(result['factorial_settings']),6)
        self.assertEqual(len({p['session_id'] for p in result['pairs']}),2)
        self.assertEqual(result['pairs'][0]['active']['gradient_std_t_m'],1e-4)
        self.assertEqual(result['pairs'][2]['moment_am2'],-.01)
        self.assertFalse(result['instrument_origin_authenticated'])
        self.assertEqual(len({p['moment_covariance_group_id'] for p in result['pairs']}),1)

    def reject(self, line_index, col_index, new_value):
        lines=rows()
        cols=lines[line_index].split(',')
        cols[col_index]=str(new_value)
        lines[line_index]=','.join(cols)
        with self.assertRaises(ValueError):
            replay(lines)

    def test_corrupt_arms_polarity_and_calibration(self):
        self.reject(2,4,.00001)
        self.reject(1,4,.9)
        self.reject(2,5,-1)
        self.reject(2,8,'neg')

    def test_timestamp_order_and_window(self):
        self.reject(2,3,10)
        self.reject(2,3,100000)
        self.reject(2,3,'NaN')

    def test_incomplete_duplicate_and_nonfinite(self):
        with self.assertRaises(ValueError): replay(rows()[:-1])
        with self.assertRaises(ValueError): replay(rows()+[rows()[2]])
        self.reject(2,6,'NaN')
        self.reject(2,7,'Inf')

    def test_end_to_end_same_object_and_synthetic_ceiling(self):
        def digest(path):
            return sha256(path.read_bytes()).hexdigest()
        with tempfile.TemporaryDirectory() as td:
            root=Path(td)
            stream=root/'instrument.csv'
            stream.write_text("\n".join(rows())+"\n",encoding='utf-8')
            cal=calibration()
            cal.update({'apparatus_id':'fixture-A','configuration_revision':'revA',
                        'instrument_serial':'S-1','calibration_revision':'C-1',
                        'gradient_calibration_fractional_std':.02})
            raw={'apparatus_id':'fixture-A','configuration_revision':'revA',
                 'instrument_serial':'S-1', 'pair_to_stream_reducer':VERSION,
                 'stream_unit_convention':'SI', 'instrument_source_stream_file':str(stream),
                 'instrument_source_stream_sha256':digest(stream)}
            derived=replay_si_csv(stream.read_bytes(),raw,cal)
            raw['pairs']=derived['pairs']
            data=root/'raw.json'; calibration_file=root/'calibration.json'
            data.write_text(json.dumps(raw));calibration_file.write_text(json.dumps(cal))
            meta={'origin':'synthetic','apparatus_id':'fixture-A',
                  'configuration_revision':'revA','instrument_serial':'S-1',
                  'calibration_revision':'C-1','gradient_calibration_fractional_std':.02,
                  'raw_data_file':str(data),'raw_data_sha256':digest(data),
                  'calibration_file':str(calibration_file),
                  'calibration_sha256':digest(calibration_file)}
            join=verify_pair_source(meta,derived['pairs'])
            self.assertTrue(join['bytes_and_exact_pair_source_join'])
            self.assertTrue(join['raw_stream_replayed_to_pairs'])
            self.assertEqual(len(join['factorial_settings_from_source']),6)
            # Deliberately false externally supplied arms must be ignored.
            record={'metadata':meta,'pairs':derived['pairs'], 'factorial_settings':[]}
            analysed=paired_analysis(record)
            self.assertTrue(analysed['raw_stream_to_pair_replay_passed'])
            self.assertEqual(analysed['factorial_identifiability']['rank'],5)
            self.assertEqual(analysed['factorial_settings_source'],
                             'replayed_hashed_raw_sensor_stream')
            self.assertFalse(analysed['submission_ready_for_independent_metrology_review'])
            self.assertFalse(analysed['gravitational_result_admissible'])
            tampered=[{**derived['pairs'][0], 'active':{
                **derived['pairs'][0]['active'],'force_n':42.}}, *derived['pairs'][1:]]
            mismatch=verify_pair_source(meta,tampered)
            self.assertFalse(mismatch['bytes_and_exact_pair_source_join'])
            self.assertFalse(mismatch['raw_stream_replayed_to_pairs'])
            stream.write_text('tampered')
            self.assertFalse(verify_pair_source(meta,derived['pairs'])
                             ['raw_stream_replayed_to_pairs'])

    def test_header_and_calibration_must_be_exact(self):
        with self.assertRaises(ValueError): replay([HEADER+',extra']+rows()[1:])
        c=calibration();c['coil_sham_max_abs_a']=.2
        with self.assertRaises(ValueError): replay(cal=c)
        c=calibration();c['force_readout_std_n']=-1
        with self.assertRaises(ValueError): replay(cal=c)


if __name__=='__main__':
    unittest.main(verbosity=2)
