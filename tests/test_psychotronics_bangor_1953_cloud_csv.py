import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_psychotronics_bangor_1953_cloud_csv import (
    STATION, BASENAME, BUCKET, list_station_key, inspect_csv_text,
    acquire_from_actual_listing, inspect_file,
)

HEADER = 'STATION,DATE,SOURCE,QUALITY_CONTROL,AA1,MW1\n'

def row(date, station=STATION, aa='01,0000,9,1'):
    return f'{station},{date},4,V,"{aa}",00\n'

class CSVSourceTests(unittest.TestCase):
    def test_unknown_s3_key_from_user_year_directory_is_not_positive_listing(self):
        root = list_station_key(fetch=lambda u, timeout: io.BytesIO(b'<ListBucketResult><IsTruncated>false</IsTruncated></ListBucketResult>'))
        self.assertEqual(root['actual_listed_matches'], [])
        self.assertFalse(root['hourly_observations_acquired'])

    def test_prefix_scoped_to_bangor_and_original_s3_year(self):
        seen = []
        def fetch(u, timeout):
            seen.append(u)
            return io.BytesIO(b'<ListBucketResult><IsTruncated>false</IsTruncated></ListBucketResult>')
        list_station_key(fetch=fetch)
        self.assertIn('prefix=1953%2F72607114606', seen[0])
        self.assertTrue(seen[0].startswith(BUCKET))

    def test_original_listing_exact_match(self):
        xml = ('<ListBucketResult><Contents><Key>1953/'+ BASENAME+'</Key><Size>823000</Size></Contents><IsTruncated>false</IsTruncated></ListBucketResult>').encode()
        r = list_station_key(fetch=lambda u, timeout:io.BytesIO(xml))
        self.assertEqual(len(r['actual_listed_matches']), 1)
        self.assertEqual(r['actual_listed_matches'][0]['key'], '1953/'+BASENAME)

    def test_rows_and_encoded_aa_are_not_claimed_as_rain(self):
        data = HEADER + row('1953-07-06T12:00:00') + row('1953-07-06T18:00:00') + row('1953-07-08T00:00:00')
        r=inspect_csv_text(data)
        self.assertEqual(r['utc_observation_counts_by_date'], {'1953-07-06':2,'1953-07-08':1})
        self.assertEqual(r['encoded_rain_and_weather_groups_not_interpreted']['1953-07-06'][0]['AA1_uninterpreted'], '01,0000,9,1')
        self.assertFalse(r['rainfall_onset_hour_identified'])
        self.assertFalse(r['Reich_causality_established'])

    def test_non_utc_offset_not_accepted(self):
        with self.assertRaises(ValueError):
            inspect_csv_text(HEADER+row('1953-07-06T12:00:00+10:00'))

    def test_wrong_station_not_accepted(self):
        with self.assertRaises(ValueError):
            inspect_csv_text(HEADER+row('1953-07-06T12:00:00',station='72607014606'))

    def test_bad_calendar_date_rejected(self):
        with self.assertRaises(ValueError):
            inspect_csv_text(HEADER+row('1953-02-30T12:00:00'))

    def test_missing_or_wrong_schema_rejected(self):
        for content in ('DATE,AA1\n1953-07-06T12:00:00,00\n', HEADER):
            with self.subTest(content=content[:20]),self.assertRaises(ValueError):
                inspect_csv_text(content)

    def test_no_july_data_not_a_negative_rain_result(self):
        with self.assertRaises(ValueError):
            inspect_csv_text(HEADER+row('1953-07-10T12:00:00'))

    def test_local_input_hash_not_authentic_publisher_receipt(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/BASENAME
            p.write_text(HEADER+row('1953-07-06T12:00:00'))
            self.assertFalse(inspect_file(p)['csv_original_publisher_custody_verified'])

    def test_download_rejects_non_matching_or_non_unique_s3_key(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(ValueError):
                acquire_from_actual_listing({'actual_listed_matches':[]},Path(d)/BASENAME)

    def test_download_bad_csv_not_written(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/BASENAME
            listing={'actual_listed_matches':[{'key':'1953/'+BASENAME}]}
            with self.assertRaises(ValueError):
                acquire_from_actual_listing(listing,p,fetch=lambda u,timeout:io.BytesIO(b'not csv'))
            self.assertFalse(p.exists())

    def test_local_download_mock_retains_derived_not_independent_status(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/BASENAME
            listing={'actual_listed_matches':[{'key':'1953/'+BASENAME}]}
            out=acquire_from_actual_listing(listing,p,fetch=lambda u,timeout:io.BytesIO((HEADER+row('1953-07-06T00:00:00')).encode()))
            self.assertTrue(out['derived_converted_csv'])
            self.assertFalse(out['original_fixed_width_ISD_format'])
            self.assertFalse(out['original_1953_precipitation_hour_interpreted'])
            with self.assertRaises(FileExistsError):
                acquire_from_actual_listing(listing,p,fetch=lambda u,timeout:io.BytesIO(b''))

if __name__=='__main__':
    unittest.main()
