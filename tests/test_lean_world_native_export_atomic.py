"""Native export publication must never replace an immutable artifact."""
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_world_native_v3_export import NativeExportError, inspect_v3, store_native

RAW = b'{"meta":{"format":{"version":"3.1.0"}}}\n{"thm":{"type":1}}\n'

def store(root, raw=RAW):
    return store_native(raw, inspect_v3(raw), root,
        repository="org/repo", revision="a"*40, module="Target",
        declaration="Target.example",
        source_closure=[{"path":"Target.lean", "sha256":"b"*64}],
        toolchain="4.28.0", dependency_closure_id="")

class ExportAtomicTests(unittest.TestCase):
    def test_idempotent_existing_export(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            a = store(root)
            b = store(root)
            self.assertEqual(a["artifact_path"], b["artifact_path"])
            self.assertEqual(Path(a["artifact_path"]).read_bytes(), RAW)

    def test_preexisting_invalid_artifact_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / (hashlib.sha256(RAW).hexdigest() + ".ndjson")
            path.write_bytes(b"invalid")
            with self.assertRaises(NativeExportError):
                store(root)
            self.assertEqual(path.read_bytes(), b"invalid")

    def test_preexisting_symlink_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dest = root / "elsewhere"
            dest.write_bytes(RAW)
            path = root / (hashlib.sha256(RAW).hexdigest() + ".ndjson")
            path.symlink_to(dest)
            with self.assertRaises(NativeExportError):
                store(root)

if __name__ == "__main__":
    unittest.main()
