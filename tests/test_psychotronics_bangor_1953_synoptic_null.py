"""Tests exact NOAA field scaling and original uploaded-content synoptic receipts.
Original observing data NOAA/NCEI; Johl Brown investigation and assistant code.
"""
import sys
import tempfile
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from check_psychotronics_bangor_1953_synoptic_null import (
    quality_pair, wind_field, ceiling_field, analyze_csv, EXPECTED_SHA256)

DATA=Path('/mnt/data/72607114606.csv')

class NOAAOriginalSynopticTests(unittest.TestCase):
    def test_slp_scale_and_QC(self):
        self.assertEqual(quality_pair('10155,1',sentinel='99999',divisor=10),1015.5)
    def test_slp_missing_sentinel(self):
        self.assertIsNone(quality_pair('99999,1',sentinel='99999',divisor=10))
    def test_slp_wrong_qc_rejected(self):
        self.assertIsNone(quality_pair('10155,3',sentinel='99999',divisor=10))
    def test_slp_malformed_rejected(self):
        with self.assertRaises(ValueError):quality_pair('garbage',sentinel='99999',divisor=10)
    def test_wind_direction_and_speed_scaled_separately(self):
        d=wind_field('200,1,N,0077,1')
        self.assertEqual(d['direction_from_true_north_deg'],200)
        self.assertEqual(d['speed_mps'],7.7)
    def test_wind_calms_and_wrong_quality(self):
        self.assertIsNone(wind_field('999,1,C,0000,1')['direction_from_true_north_deg'])
        self.assertIsNone(wind_field('200,3,N,0077,3')['speed_mps'])
    def test_wind_format_rejected(self):
        with self.assertRaises(ValueError):wind_field('200,1,N,0077')
    def test_unlimited_ceiling_not_22000m_cloud_base(self):
        self.assertTrue(ceiling_field('22000,1,9,N')['unlimited_reported'])
        self.assertIsNone(ceiling_field('22000,1,9,N')['metres_agl'])
    def test_ceiling_real_height(self):
        self.assertEqual(ceiling_field('01800,1,9,N')['metres_agl'],1800)
    def test_ceiling_wrong_QC_rejected(self):
        self.assertIsNone(ceiling_field('01800,3,9,N'))
    def test_invalid_file_digest_fails_closed(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'fake.csv';p.write_text('not NOAA')
            with self.assertRaises(ValueError):analyze_csv(p)
    @unittest.skipUnless(DATA.exists(),'actual 1953 original user-supplied CSV unavailable on this machine')
    def test_original_sha_and_exact_row_count(self):
        result=analyze_csv(DATA)
        self.assertEqual(result['local_sha256_not_noaa_publisher_authenticated'],EXPECTED_SHA256)
        self.assertEqual(result['original_observation_hours'],8760)
    @unittest.skipUnless(DATA.exists(),'actual 1953 original user-supplied CSV unavailable on this machine')
    def test_real_pressure_drop_precedes_reported_shower(self):
        result=analyze_csv(DATA)
        self.assertEqual(result['quality_passing_pressure_deltas_hpa']['12h_before_observed_02Z_shower'],-6.7)
        self.assertEqual(result['quality_passing_pressure_deltas_hpa']['24h_before_observed_02Z_shower'],-9.5)
    @unittest.skipUnless(DATA.exists(),'actual 1953 original user-supplied CSV unavailable on this machine')
    def test_concurrent_bangor_winds_do_not_change_direction(self):
        result=analyze_csv(DATA)
        self.assertEqual([x['direction_from_true_north_deg'] for x in result['wind_at_bangor_during_UTC14_to16']],[200,200,200])
        self.assertFalse(result['limitations']['wind_at_bangor_same_as_Graham_Lake'])
    @unittest.skipUnless(DATA.exists(),'actual 1953 original user-supplied CSV unavailable on this machine')
    def test_control_windows_not_causal_pvalue(self):
        result=analyze_csv(DATA)
        r=result['july_1953_end_in_july_12h_pressure_control_windows']
        self.assertEqual(r['eligible_overlapping_hour_pairs'],744)
        self.assertEqual(r['pairs_with_drop_at_least_as_large_as_event'],46)
        self.assertFalse(r['independent_samples_or_permutation_p_value'])
        self.assertFalse(result['limitations']['barometric_change_is_proof_for_or_against_cloudbuster'])

if __name__=='__main__':unittest.main()
