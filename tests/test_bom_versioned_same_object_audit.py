"""Synthetic fixtures only; no claim to reproduce any Australian BOM record."""
import importlib.util
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'scripts/bom_versioned_same_object_audit.py'
spec = importlib.util.spec_from_file_location('bom_audit', SCRIPT)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

HEADER = 'station_id,date,variable,value,flag\n'

def fixture(root, before, after):
    entries = {}
    for name, body in [('before', before), ('after', after)]:
        filename = f'{name}.csv'
        raw = (HEADER + body).encode('utf-8')
        (root / filename).write_bytes(raw)
        entries[name] = {'file': filename, 'sha256': sha256(raw).hexdigest(),
                         'source_url': f'https://example.org/{filename}',
                         'captured_utc': '2026-05-01T10:00:00Z' if name == 'before'
                                         else '2026-10-30T10:00:00Z'}
    return {'schema': 'dashi.bom.same_object_snapshot.v1', **entries}

class AuditTests(unittest.TestCase):
    def test_changed_deleted_added_and_flag_only_separately(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = fixture(root,
                'S1,1910-01-01,tmax,17.0,A\nS1,1910-01-02,tmax,18.0,A\n'
                'S1,1910-01-03,tmin,7.0,A\nS2,2025-01-01,rain,0.0,A\n',
                'S1,1910-01-01,tmax,,A\nS1,1910-01-02,tmax,19.0,A\n'
                'S1,1910-01-03,tmin,7.0,B\nS2,2025-01-01,rain,0.0,A\n'
                'S3,1960-02-01,rain,3.4,A\n')
            result = module.audit(manifest, root)
            self.assertEqual(result['counts'], {'value_removed': 1, 'value_changed': 1,
                                                'flag_changed': 1, 'row_added': 1})
            self.assertFalse(result['climate_trend_effect_computed'])
            self.assertFalse(result['intent_or_coordination_inferred'])

    def test_station_variable_date_join_is_exact(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            m = fixture(root, 'S1,1910-01-01,tmax,20,A\n',
                              'S2,1910-01-01,tmax,20,A\n')
            out = module.audit(m, root)
            self.assertEqual(out['counts'], {'row_removed': 1, 'row_added': 1})

    def test_duplicate_key_rejected(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            m = fixture(root, 'S1,1910-01-01,tmax,20,A\nS1,1910-01-01,tmax,21,A\n',
                              'S1,1910-01-01,tmax,20,A\n')
            with self.assertRaises(module.AuditError):
                module.audit(m, root)

    def test_hash_mutation_rejected(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            m = fixture(root, 'S1,1910-01-01,tmax,20,A\n',
                              'S1,1910-01-01,tmax,21,A\n')
            (root / 'before.csv').write_text(HEADER + 'S1,1910-01-01,tmax,22,A\n')
            with self.assertRaises(module.AuditError):
                module.audit(m, root)

    def test_precision_change_is_not_physical_change(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            m = fixture(root, 'S1,1910-01-01,tmax,20,A\n',
                              'S1,1910-01-01,tmax,20.0,A\n')
            self.assertEqual(module.audit(m, root)['counts'], {'numeric_format_changed': 1})

    def test_missing_value_is_not_missing_row(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            m = fixture(root, 'S1,1910-01-01,tmax,,A\n',
                              'S1,1910-01-01,tmax,20,A\n')
            self.assertEqual(module.audit(m, root)['counts'], {'value_added': 1})

    def test_escape_path_is_rejected(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            m = fixture(root, 'S1,1910-01-01,tmax,20,A\n',
                              'S1,1910-01-01,tmax,21,A\n')
            m['before']['file'] = '../outside.csv'
            with self.assertRaises(module.AuditError):
                module.audit(m, root)

    def test_unknown_variable_rejected(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            m = fixture(root, 'S1,1910-01-01,unknown,20,A\n',
                              'S1,1910-01-01,tmax,21,A\n')
            with self.assertRaises(module.AuditError):
                module.audit(m, root)

if __name__ == '__main__':
    unittest.main()
