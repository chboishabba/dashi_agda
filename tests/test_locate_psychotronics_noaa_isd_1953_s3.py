"""Synthetic first-party S3 acquisition boundary tests; no actual NOAA download.

NOAA original agency distribution and data copyright credited to NOAA/NCEI.
Case-specific test code: Johl Brown with OpenAI ChatGPT assistance.
"""
import gzip
import hashlib
import io
import sys
import tempfile
import unittest
import urllib.error
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
from locate_psychotronics_noaa_isd_1953_s3 import (
    BUCKET, TARGET, parse_listing, listing_url, locate, download_exact_key, self_test,
)


def listing(key=TARGET, size=160944, truncated=False, token=None):
    item = '<Contents><Key>' + key + '</Key><Size>' + str(size) + '</Size></Contents>'
    flag = '<IsTruncated>' + ('true' if truncated else 'false') + '</IsTruncated>'
    cont = '<NextContinuationToken>' + token + '</NextContinuationToken>' if token else ''
    return ('<ListBucketResult>' + flag + cont + item + '</ListBucketResult>').encode()


class NOAAS3OriginalObjectAcquisitionTests(unittest.TestCase):
    def test_namespaced_original_schema_fixture(self):
        self.assertEqual(self_test()['synthetic_listing_cases_passed'], 5)

    def test_s3_cloud_actual_listing_key_required(self):
        with patch('locate_psychotronics_noaa_isd_1953_s3.urllib.request.urlopen',
                   return_value=io.BytesIO(listing('data/1953/' + TARGET))):
            r = locate(('data/1953/',))
        self.assertEqual(r['actual_listing_matches'][0]['key'], 'data/1953/' + TARGET)
        self.assertFalse(r['historical_1953_data_read'])
        self.assertFalse(r['agency_authenticated_original_checksum'])

    def test_paginated_listing_does_not_stop_at_first_page(self):
        with patch('locate_psychotronics_noaa_isd_1953_s3.urllib.request.urlopen',
                   side_effect=[io.BytesIO(listing('unrelated.gz', truncated=True, token='next')),
                                io.BytesIO(listing('1953/' + TARGET))]) as mocked:
            r = locate(('1953/',))
        self.assertEqual(mocked.call_count, 2)
        self.assertEqual(len(r['actual_listing_matches']), 1)
        self.assertFalse(r['prefix_failures_or_bounded_gaps'])

    def test_no_s3_discovery_is_explicitly_unpaid(self):
        with patch('locate_psychotronics_noaa_isd_1953_s3.urllib.request.urlopen',
                   return_value=io.BytesIO(listing('different-1953.gz'))):
            r = locate(('1953/',))
        self.assertEqual(r['actual_listing_matches'], [])

    def test_access_denied_is_not_a_negative_weather_result(self):
        with patch('locate_psychotronics_noaa_isd_1953_s3.urllib.request.urlopen',
                   side_effect=urllib.error.URLError('AccessDenied')):
            r = locate(('1953/',))
        self.assertEqual(r['actual_listing_matches'], [])
        self.assertEqual(len(r['prefix_failures_or_bounded_gaps']), 1)
        self.assertFalse(r['historical_1953_data_read'])

    def test_original_object_download_sha_is_local_only(self):
        payload = gzip.compress(b'NOT ORIGINAL NOAA -- synthetic bytes only')
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / TARGET
            with patch('locate_psychotronics_noaa_isd_1953_s3.urllib.request.urlopen',
                       return_value=io.BytesIO(payload)):
                r = download_exact_key('data/1953/' + TARGET, target)
            self.assertEqual(target.read_bytes(), payload)
            self.assertEqual(r['local_sha256_not_publisher_authenticated'], hashlib.sha256(payload).hexdigest())
            self.assertFalse(r['is_original_1953_hourly_data_parsed'])
            with self.assertRaises(FileExistsError):
                download_exact_key('data/1953/' + TARGET, target)

    def test_invalid_download_content_never_writes_original(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / TARGET
            with patch('locate_psychotronics_noaa_isd_1953_s3.urllib.request.urlopen',
                       return_value=io.BytesIO(b'<html>error</html>')):
                with self.assertRaises(ValueError):
                    download_exact_key('data/1953/' + TARGET, target)
            self.assertFalse(target.exists())

    def test_unrelated_key_is_not_downloaded(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError):
                download_exact_key('data/1953/other.gz', Path(tmp) / TARGET)

    def test_s3_prefix_escapes_arbitrary_metacharacters(self):
        self.assertIn('prefix=data%2F1953%2F', listing_url('data/1953/'))
        self.assertIn('continuation-token=a%26b', listing_url('data/1953/', 'a&b'))


if __name__ == '__main__':
    unittest.main()
