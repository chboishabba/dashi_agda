"""Synthetic NOAA ISD record-format and provenance boundary tests.

Original format is NOAA/NCEI Jan 2018 ISD Format Document, pp. 5, 13-14.
Tests: Johl Brown with ChatGPT assistance; no authentic 1953 hour is tested.
"""
import gzip
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_psychotronics_bangor_1953_isd_original import (
    examine, parse_header, self_test, synthetic_record,
)


class ISD1953BangorOriginalFormatTests(unittest.TestCase):
    def test_zero_variable_field_means_105_bytes_not_zero(self):
        r = synthetic_record()
        self.assertEqual(len(r), 105)
        self.assertEqual(r[:4], '0000')
        self.assertEqual(parse_header(r)['utc_time'], '1200')

    def test_original_nonzero_variable_field_adds_to_105(self):
        r = synthetic_record(variable='ADDAA101001541')
        self.assertEqual(len(r), 119)
        self.assertEqual(r[:4], '0014')
        self.assertEqual(parse_header(r)['utc_date'], '19530706')

    def test_old_defective_full_length_0105_is_rejected(self):
        r = synthetic_record()
        with self.assertRaises(ValueError):
            parse_header('0105' + r[4:])

    def test_mismatch_extra_bytes_rejected(self):
        r = synthetic_record()
        with self.assertRaises(ValueError):
            parse_header(r + 'ADD')
        with self.assertRaises(ValueError):
            parse_header(synthetic_record(variable='ADD')[:-1])

    def test_wrong_station_ids_rejected(self):
        for keyword in ({'wban': '99999'}, {'usaf': '999999'}):
            with self.subTest(ids=keyword), self.assertRaises(ValueError):
                parse_header(synthetic_record(**keyword))

    def test_bad_utc_time_rejected(self):
        for value in ('2460', '2500', '2360', 'ABCD'):
            with self.subTest(time=value), self.assertRaises(ValueError):
                parse_header(synthetic_record(time=value))

    def test_invalid_calendar_dates_rejected(self):
        for value in ('19530230', '19531301', '195307AA'):
            with self.subTest(date=value), self.assertRaises(ValueError):
                parse_header(synthetic_record(date=value))

    def test_non_numeric_record_prefix_rejected(self):
        r = synthetic_record()
        with self.assertRaises(ValueError):
            parse_header('x' + r[1:])

    def test_gzip_window_counts_flags_without_interpreting_rain(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / '726071-14606-1953.gz'
            with gzip.open(path, 'wt', encoding='ascii') as f:
                f.write(synthetic_record('19530705', '2359') + '\n')
                f.write(synthetic_record('19530706', '0000', variable='ADD') + '\n')
                f.write(synthetic_record('19530707', '0159') + '\n')
                f.write(synthetic_record('19530709', '1800') + '\n')
            result = examine(path)
            self.assertEqual(sum(result['utc_hourly_or_synoptic_observation_counts'].values()), 4)
            self.assertEqual(result['source_flag_counts_original_record_labels_only'], {'4': 4})
            self.assertEqual(result['utc_time_labels']['19530706'], ['0000'])
            self.assertFalse(result['precipitation_payload_interpreted'])
            self.assertFalse(result['local_timezone_alignment_verified'])
            self.assertFalse(result['original_noaa_full_file_bytes_authenticated'])
            self.assertFalse(result['causal_intervention_verified'])

    def test_out_of_window_only_is_not_claimed_as_1953_july_observation(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'fixture.gz'
            with gzip.open(path, 'wt', encoding='ascii') as f:
                f.write(synthetic_record('19530710') + '\n')
            with self.assertRaises(ValueError):
                examine(path)

    def test_embedded_original_self_test(self):
        self.assertEqual(self_test()['synthetic_negative_cases_passed'], 8)
        self.assertFalse(self_test()['publisher_1953_original_bytes_acquired'])


if __name__ == '__main__':
    unittest.main()
