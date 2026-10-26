"""Exact synthetic collision/adversarial revision tests, NOT 1953 experiment replay.

Run from repository root:
    python -m unittest discover -s tests -p test_psychotronics_daily_to_hourly_nogo_20261026.py -v
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_psychotronics_daily_to_hourly_nogo_20261026 import (
    hourly_allocation, noninjective_daily_projection, counterfactual_witness,
    case_report, self_test,
)


class DailyToHourlyNoGoTests(unittest.TestCase):
    def test_noninjective_early_late(self):
        for total in (1, 66, 130, 193):
            self.assertNotEqual(hourly_allocation(total, 1), hourly_allocation(total, 23))
            self.assertEqual(sum(hourly_allocation(total, 1)), total)
            self.assertEqual(sum(hourly_allocation(total, 23)), total)
            self.assertTrue(noninjective_daily_projection(total)["synthetic_only"])

    def test_zero_total_does_not_fake_positive_collision(self):
        with self.assertRaises(ValueError):
            noninjective_daily_projection(0)

    def test_negative_total_rejected(self):
        with self.assertRaises(ValueError):
            hourly_allocation(-2, 7)

    def test_out_of_range_hours_rejected(self):
        for hour in (-1, 24, 48):
            with self.subTest(hour=hour), self.assertRaises(ValueError):
                hourly_allocation(13, hour)

    def test_stipulated_treated_outcome_not_identifying(self):
        w = counterfactual_witness()
        self.assertTrue(w["synthetic_only"])
        self.assertEqual(w["compatible_causal_effects"], [0, 1])
        self.assertFalse(w["actual_1953_counterfactual_observed"])

    def test_original_NOAA_excerpt_join_and_scope(self):
        c = case_report()
        self.assertEqual((c["bangor_6_to_8_tenths_mm"],
                          c["bar_harbor_6_to_8_tenths_mm"],
                          c["between_site_difference_tenths_mm"]), (305, 130, 175))
        self.assertFalse(c["ellsworth_22h_local_rain_verified"])
        self.assertFalse(c["device_caused_rain_verified"])

    def test_withdrawal_adversarial_receipts(self):
        self.assertTrue(self_test()["passed"])


if __name__ == "__main__":
    unittest.main()
