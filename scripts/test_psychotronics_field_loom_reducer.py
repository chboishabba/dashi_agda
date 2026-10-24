#!/usr/bin/env python3
"""Synthetic, offline S1 raw-stream reduction regressions (not instrument tests)."""
import unittest
from psychotronics_field_loom_reducer import replay_si_csv, VERSION

HEADER = 'pair_id,session_id,condition,time_ns,coil_current_a,dipole_sign,force_n,gradient_t_m,moment_calibration_id'


def calibration():
    return {'moment_calibration_groups': {
        'pos': {'moment_am2': .01, 'moment_std_am2': .001},
        'neg': {'moment_am2': -.01, 'moment_std_am2': .001}},
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

    def test_header_and_calibration_must_be_exact(self):
        with self.assertRaises(ValueError): replay([HEADER+',extra']+rows()[1:])
        c=calibration();c['coil_sham_max_abs_a']=.2
        with self.assertRaises(ValueError): replay(cal=c)
        c=calibration();c['force_readout_std_n']=-1
        with self.assertRaises(ValueError): replay(cal=c)


if __name__=='__main__':
    unittest.main(verbosity=2)
