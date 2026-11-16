"""Synthetic exact-streak tests only: never empirical BOM validation."""
from datetime import date, timedelta
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import bom_streak_negative_controls as mod


def rows(station, start, values, var='rain'):
    begin = date.fromisoformat(start)
    return {(station, (begin + timedelta(days=i)).isoformat(), var):
            {'value': str(v), 'flag': 'Y'} for i, v in enumerate(values)}


class ScanTests(unittest.TestCase):
    def test_within_station_repeat(self):
        d = {**rows('A', '1980-01-01', [0, 3, 5, 1, 0, 2, 0, 4, 0, 1, 0, 7, 8, 0, 5, 3]),
             **rows('A', '1998-01-01', [0, 3, 5, 1, 0, 2, 0, 4, 0, 1, 0, 7, 8, 0, 5, 3])}
        found = mod.scan(d, min_days=12)
        self.assertEqual(len(found['within']), 1)
        self.assertEqual(found['within'][0]['days'], 16)
        self.assertEqual(found['within'][0]['right_start'], '1998-01-01')

    def test_cross_station_repeat(self):
        v = [1, 0, 8, 3, 0, 2, 7, 1, 9, 4, 3, 2, 5, 4]
        d = {**rows('A', '1964-01-01', v), **rows('B', '1964-01-01', v)}
        self.assertEqual(len(mod.scan(d)['cross']), 1)
        self.assertEqual(mod.scan(d)['cross'][0]['station_independence'], 'NOT_VERIFIED')

    def test_long_zero_dry_spells_do_not_trigger(self):
        v = [0] * 200
        d = {**rows('A', '1980-01-01', v), **rows('A', '1982-01-01', v)}
        self.assertEqual(len(mod.scan(d)['within']), 0)

    def test_short_rain_zeros_insufficient(self):
        v = [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        d = {**rows('A', '1980-01-01', v), **rows('A', '1982-01-01', v)}
        self.assertEqual(len(mod.scan(d)['within']), 0)

    def test_missing_day_breaks_streak(self):
        v = [3, 5, 7, 0, 1, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16]
        d = {**rows('A', '1980-01-01', v), **rows('A', '1982-01-01', v)}
        del d[('A', '1982-01-07', 'rain')]
        self.assertEqual(len(mod.scan(d, min_days=12)['within']), 0)

    def test_numeric_format_equivalent(self):
        v = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
        d = {**rows('A', '1980-01-01', v, var='tmax'),
             **rows('A', '1982-01-01', [str(x) + '.0' for x in v], var='tmax')}
        self.assertEqual(len(mod.scan(d, min_days=12)['within']), 1)

    def test_rotation_preserves_nonmissing_mask_and_values(self):
        d = rows('A', '1980-01-01', [0, 2, 4, 7, 1, 0, 4, 3, 2, 8, 1, 0, 5])
        rotated = mod.rotate_months(d, 2)
        self.assertEqual(set(d), set(rotated))
        self.assertCountEqual([v['value'] for v in d.values()],
                              [v['value'] for v in rotated.values()])

    def test_candidate_budget_fail_closed(self):
        v = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
        d = {**rows('A', '1980-01-01', v, var='tmax'),
             **rows('A', '1981-01-01', v, var='tmax')}
        with self.assertRaises(ValueError):
            mod.scan(d, max_candidates=1)

    def test_no_intent_or_trend_inference(self):
        d = rows('A', '1980-01-01', [0, 2, 4, 5, 7, 1, 0, 4, 3, 2, 8, 1, 9])
        r = mod.audit(d, controls=2)
        self.assertFalse(r['copy_direction_established'])
        self.assertFalse(r['climate_effect_computed'])
        self.assertFalse(r['statistical_fdr_established'])
        self.assertEqual(len(r['control_counts']), 2)


if __name__ == '__main__':
    unittest.main()
