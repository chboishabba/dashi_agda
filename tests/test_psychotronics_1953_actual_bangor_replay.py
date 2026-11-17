"""Synthetic plus user-file conditional source replay tests (no NOAA attribution inflation)."""
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from check_psychotronics_1953_actual_bangor_replay import analyze

HEADER='STATION,DATE,SOURCE,MW1,MW2,MW3,MW4,AA1,SLP\n'
ROW='72607114606,1953-07-07T02:00:00,4,"80,1",,,,"24,0190,9,1","10088,1"\n'

class NOAA1953ActualBangorReplay(unittest.TestCase):
    def sample(self,contents):
        temp=tempfile.TemporaryDirectory()
        p=Path(temp.name)/'sample.csv'
        p.write_text(contents,encoding='utf-8')
        self.addCleanup(temp.cleanup)
        return p

    def test_synthetic_code80_not_causal_proof(self):
        x=analyze(self.sample(HEADER+ROW))
        self.assertEqual(x['weather_at_1953_07_06_2200_local']['weather_code'],'80')
        self.assertEqual(x['weather_at_1953_07_06_2200_local']['local'],'1953-07-06T22:00:00-04:00')
        self.assertFalse(x['limits']['cloudbuster_causality_supported'])
        self.assertFalse(x['limits']['exact_rain_onset_determined'])
        self.assertEqual(x['24h_precipitation_reports'][0]['mm'],19)

    def test_synthetic_bad_station_rejected(self):
        with self.assertRaises(ValueError):
            analyze(self.sample((HEADER+ROW).replace('72607114606','72607014606')))

    def test_synthetic_duplicate_hours_rejected(self):
        with self.assertRaises(ValueError):
            analyze(self.sample(HEADER+ROW+ROW))

    def test_synthetic_non_utc_offset_rejected(self):
        with self.assertRaises(ValueError):
            analyze(self.sample((HEADER+ROW).replace('1953-07-07T02:00:00','1953-07-07T02:00:00-04:00')))

    @classmethod
    def setUpClass(cls):
        candidate=os.environ.get('NOAA_1953_BANGOR_CSV')
        cls.uploaded=Path(candidate) if candidate else None
        if cls.uploaded and cls.uploaded.is_file():
            cls.real=analyze(cls.uploaded)
        else:
            cls.real=None

    def test_real_file_8760_hourly_obs(self):
        if self.real is None:self.skipTest('real NOAA user upload path not provided')
        self.assertEqual(self.real['rows'],8760)
        self.assertEqual(self.real['window_utc_counts'],{f'1953-07-{i:02d}':24 for i in range(5,10)})

    def test_real_file_upload_digest(self):
        if self.real is None:self.skipTest('real NOAA user upload path not provided')
        self.assertEqual(self.real['upload_sha256'],'2a3b048d620b320fb8d1cf548d4eb06fb2c49821faa54c4cc7f708649cdca9bd')

    def test_real_file_22h_original_weather_code(self):
        if self.real is None:self.skipTest('real NOAA user upload path not provided')
        self.assertEqual(self.real['first_rain_weather_in_window']['utc'],'1953-07-07T02:00:00Z')
        self.assertEqual(self.real['first_rain_weather_in_window']['local'],'1953-07-06T22:00:00-04:00')
        self.assertEqual(self.real['first_rain_weather_in_window']['quality'],'1')

    def test_real_file_24h_not_1h_totals(self):
        if self.real is None:self.skipTest('real NOAA user upload path not provided')
        dates={a['utc'][:10]:a for a in self.real['24h_precipitation_reports']}
        self.assertEqual([dates[f'1953-07-{i:02d}']['mm'] for i in (6,7,8)],[7,19,5])
        self.assertTrue(all(dates[f'1953-07-{i:02d}']['hours']==24 for i in (6,7,8)))
        self.assertFalse(self.real['limits']['AA1_24h_amount_equals_hourly_rain'])

if __name__ == '__main__': unittest.main()
