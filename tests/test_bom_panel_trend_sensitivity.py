"""Synthetic same-panel slope regression tests, not BOM trend observations."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import bom_panel_trend_sensitivity as panel


class PanelTests(unittest.TestCase):
    def test_known_slope_delta(self):
        rows=panel.parse('year,weight,before,after\n2000,1,0,0\n2010,1,0,1\n')
        result=panel.analyze(rows)
        self.assertEqual(result['trend_difference_C_per_decade'],1.0)
        self.assertEqual(result['exact_difference_C_per_decade'],'1')

    def test_intercept_no_slope(self):
        rows=panel.parse('year,weight,before,after\n2000,1,1,5\n2010,1,2,6\n')
        self.assertEqual(panel.analyze(rows)['trend_difference_C_per_decade'],0)

    def test_weighted_identity(self):
        rows=panel.parse('year,weight,before,after\n2000,1,2,3\n2010,2,3,1\n2020,1,3,5\n')
        r=panel.analyze(rows)
        self.assertLessEqual(abs(r['trend_difference_C_per_decade']),
                             r['absolute_change_bound_C_per_decade'])

    def test_no_missing_value_imputation(self):
        with self.assertRaises(ValueError):
            panel.parse('year,weight,before,after\n2000,1,,2\n2010,1,4,5\n')

    def test_reject_duplicate_year(self):
        with self.assertRaises(ValueError):
            panel.parse('year,weight,before,after\n2000,1,2,3\n2000,1,4,5\n')

    def test_reject_zero_weight(self):
        with self.assertRaises(ValueError):
            panel.parse('year,weight,before,after\n2000,0,2,3\n2010,1,4,5\n')

    def test_reject_single_year(self):
        with self.assertRaises(ValueError):
            panel.parse('year,weight,before,after\n2000,1,2,3\n')

    def test_scope_limits(self):
        rows=panel.parse('year,weight,before,after\n2000,1,0,1\n2010,1,1,1\n')
        r=panel.analyze(rows)
        self.assertFalse(r['national_trend_claim_authorised'])
        self.assertFalse(r['raw_archive_causation_established'])
        self.assertFalse(r['homogenisation_recomputed'])


if __name__=='__main__':
    unittest.main()
