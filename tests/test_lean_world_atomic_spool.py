"""Immutable queue publication: no visible partial finals and no silent overwrite."""
import concurrent.futures
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_world_atomic_spool import PublicationError, publish_immutable

class AtomicSpoolTests(unittest.TestCase):
    def test_idempotent(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "entry.json"
            self.assertTrue(publish_immutable(p, b'{"a":1}\n'))
            self.assertFalse(publish_immutable(p, b'{"a":1}\n'))
            self.assertEqual(p.read_bytes(), b'{"a":1}\n')
            self.assertEqual(list(Path(tmp).glob(".staging-*")), [])

    def test_conflicting_bytes_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "entry"
            publish_immutable(p, b"a")
            with self.assertRaises(PublicationError):
                publish_immutable(p, b"b")
            self.assertEqual(p.read_bytes(), b"a")

    def test_existing_partial_file_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "entry"
            p.write_bytes(b"partial")
            with self.assertRaises(PublicationError):
                publish_immutable(p, b"complete")
            self.assertEqual(p.read_bytes(), b"partial")

    def test_existing_symlink_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            target = root / "other"
            target.write_bytes(b"same")
            p = root / "entry"
            p.symlink_to(target)
            with self.assertRaises(PublicationError):
                publish_immutable(p, b"same")

    def test_empty_entry_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(PublicationError):
                publish_immutable(Path(tmp) / "entry", b"")

    def test_concurrent_identical_writers(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "entry"
            with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
                results = list(pool.map(lambda _: publish_immutable(p, b"complete"), range(64)))
            self.assertEqual(sum(results), 1)
            self.assertEqual(p.read_bytes(), b"complete")
            self.assertEqual(list(Path(tmp).glob(".staging-*")), [])

    def test_concurrent_competing_writers(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "entry"
            def submit(payload):
                try:
                    return publish_immutable(p, payload)
                except PublicationError:
                    return "conflict"
            with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
                results = list(pool.map(submit, [b"A", b"B"] * 20))
            self.assertIn(p.read_bytes(), (b"A", b"B"))
            self.assertIn("conflict", results)

if __name__ == "__main__":
    unittest.main()
