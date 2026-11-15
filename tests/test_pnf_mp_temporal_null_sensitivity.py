"""Synthetic-only regression: iid-MP outlier need not survive a time-aware null."""
import unittest
import numpy as np
from scripts.pnf_mp_temporal_null_sensitivity import (
    columnwise_ar1, temporal_null_receipt,
)


class MPTemporalNullSensitivityTests(unittest.TestCase):
    def test_independent_persistent_columns_mimic_iid_outlier(self):
        panel = columnwise_ar1(n=120, p=24, rho=0.8, seed=20261111)
        receipt = temporal_null_receipt(
            panel, source="synthetic AR1 independent columns",
            window_label="t0..119", seed=20261111, surrogate_count=100)
        self.assertTrue(receipt.iid_above_edge)
        self.assertFalse(receipt.surrogate_above_empirical95)
        self.assertGreater(receipt.circular_shift_top_quantile95,
                           receipt.iid_mp_upper_edge)
        self.assertEqual(receipt.n, 120)
        self.assertEqual(receipt.p, 24)
        self.assertIn("synthetic", receipt.qualification)

    def test_fail_closed_parameters(self):
        with self.assertRaises(ValueError):
            columnwise_ar1(n=10, p=2, rho=1, seed=1)
        with self.assertRaises(ValueError):
            temporal_null_receipt(np.ones((10, 2)),
                source="", window_label="t0", surrogate_count=20)
        with self.assertRaises(ValueError):
            temporal_null_receipt(np.ones((10, 2)),
                source="synthetic", window_label="t0", surrogate_count=4)


if __name__ == "__main__":
    unittest.main()
