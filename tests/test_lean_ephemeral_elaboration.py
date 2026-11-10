#!/usr/bin/env python3
"""Offline mock subprocess tests for closure/cache logic (NOT a real Lean test)."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_ephemeral_elaboration import (
    EphemeralLeanWorker, ElaborationError, compiled_dependency_digest,
)

SOURCE = b"theorem test : True := trivial\n"


def receipt(source=SOURCE):
    return {
        "repository": "owner/leanproject",
        "revision": "a"*40, "path": "Test.lean",
        "git_blob": hashlib.sha1(
            b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest(),
        "sha256": hashlib.sha256(source).hexdigest(),
        "size": len(source), "status": "source-verified-not-elaborated",
    }


class Tests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.executable = self.root / "fake_lean.py"
        self.executable.write_text(
            "import pathlib,sys\n"
            "if '--version' in sys.argv:\n"
            " print('FAKE-LEAN-TEST-ONLY')\n"
            "else:\n"
            " out=pathlib.Path(sys.argv[sys.argv.index('-o')+1])\n"
            " source=pathlib.Path(sys.argv[-1]).read_bytes()\n"
            " out.write_bytes(b'MOCK-OLEAN:'+source)\n")
        self.closure = compiled_dependency_digest(None)
        self.worker = EphemeralLeanWorker(
            flake=self.root, cache=self.root/"cache",
            closure_digest=self.closure,
            command=(sys.executable, str(self.executable)))

    def test_compiled_bytes_cached_on_second_request(self):
        first = self.worker.elaborate(receipt(), SOURCE, "Test.lean")
        second = self.worker.elaborate(receipt(), SOURCE, "Test.lean")
        self.assertEqual(first.status, "lean-compiled-not-exported")
        self.assertFalse(first.reused)
        self.assertTrue(second.reused)
        self.assertEqual(first.cache_key, second.cache_key)
        self.assertEqual(first.olean_sha256, second.olean_sha256)

    def test_changed_source_never_reuses_olean(self):
        source = SOURCE + b"\n-- changed"
        self.worker.elaborate(receipt(), SOURCE, "Test.lean")
        another = self.worker.elaborate(receipt(source), source, "Test.lean")
        self.assertFalse(another.reused)

    def test_tampered_cache_is_not_trusted(self):
        result = self.worker.elaborate(receipt(), SOURCE, "Test.lean")
        output = self.root/"cache"/result.cache_key[:2]/result.cache_key/"module.olean"
        output.write_bytes(b"CORRUPTED")
        repaired = self.worker.elaborate(receipt(), SOURCE, "Test.lean")
        self.assertFalse(repaired.reused)

    def test_bad_source_hash_rejected_before_exec(self):
        forged = dict(receipt(), sha256="0"*64)
        with self.assertRaises(ValueError):
            self.worker.elaborate(forged, SOURCE, "Test.lean")

    def test_missing_dependency_closure_rejected(self):
        worker = EphemeralLeanWorker(
            flake=self.root, cache=self.root/"cache",
            closure_digest="f"*64, command=(sys.executable, str(self.executable)))
        with self.assertRaises(ElaborationError):
            worker.elaborate(receipt(), SOURCE, "Test.lean")

    def test_dependency_cache_digest_changes_with_compiled_bytes(self):
        dependency = self.root/"deps"
        dependency.mkdir()
        (dependency/"Foo.olean").write_bytes(b"one")
        first = compiled_dependency_digest(dependency)
        (dependency/"Foo.olean").write_bytes(b"two")
        self.assertNotEqual(first, compiled_dependency_digest(dependency))

    def test_unsafe_module_name_rejected(self):
        with self.assertRaises(ValueError):
            self.worker.elaborate(receipt(), SOURCE, "../escape.lean")


if __name__ == "__main__":
    unittest.main()
