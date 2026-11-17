"""Cross-check ABC-hosted claimant table excerpts, not original BOM archive."""
import json
from datetime import date, timedelta
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import bom_streak_negative_controls as mod

raw = json.loads((ROOT / 'Docs/support/reference/bom_abc_mediawatch_station_excerpts_20261026.json').read_text(encoding='utf-8'))

def rows(case):
    data = {}
    for side in ('left', 'right'):
        start = date.fromisoformat(case[f'{side}_start'])
        for i, value in enumerate(case[side]):
            key = (raw['station_id'], (start+timedelta(days=i)).isoformat(), raw['variable'])
            data[key] = {'value': '' if value is None else str(value), 'flag': 'Y'}
    return data

class SourceTests(unittest.TestCase):
    def test_original_scope(self):
        self.assertFalse(raw['original_paper_records_authenticated'])
        self.assertIsNone(raw['original_CDO_export_sha256'])

    def test_1910_exact_repeat_below_default_detection_threshold(self):
        case = raw['cases'][0]
        self.assertEqual(len(case['left']), 7)
        self.assertEqual(case['left'], case['right'])
        self.assertEqual(len(mod.scan(rows(case), min_days=7, min_lag=7)['within']), 1)
        self.assertEqual(len(mod.scan(rows(case))['within']), 0)

    def test_1943_month_exact_and_bom_acknowledged(self):
        case = raw['cases'][1]
        self.assertEqual(len(case['left']), 30)
        self.assertEqual(case['left'], case['right'])
        self.assertEqual(len(mod.scan(rows(case))['within']), 1)
        self.assertIn('included', case['bom_2026_10_26_position'])

    def test_1935_seam_two_missing_days_no_imputation(self):
        case = raw['cases'][2]
        self.assertEqual(len(case['left']), 31)
        self.assertIsNone(case['left'][14])
        self.assertIsNone(case['left'][15])
        self.assertEqual(case['right'][14:16], [20, 21.1])
        self.assertEqual(case['left'][:14], case['right'][:14])
        self.assertEqual(case['left'][17:], case['right'][17:])
        matches = mod.scan(rows(case))['within']
        # Exact-match detector counts day 17 (same value, different accumulation
        # metadata) as one of 15 consecutive values, rather than 14 alone.
        self.assertEqual(sorted(x['days'] for x in matches), [14, 15])

if __name__ == '__main__':
    unittest.main()
