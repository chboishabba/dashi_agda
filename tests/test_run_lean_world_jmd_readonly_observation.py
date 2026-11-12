#!/usr/bin/env python3
"""Synthetic JMD parser source pins: byte-correlated read-only receipt only."""
from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import run_lean_world_jmd_readonly_observation as publisher

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from run_lean_world_jmd_readonly_observation import (
    publish_jmd_readonly, JMDObservationError)


# A deliberately FAKE parser satisfying the mechanical interface.
# Running it in tests does not validate actual dashi_lean4 PR105 or Lean.
STUB_SOURCE = '''
from hashlib import sha256
import json

def nodes_from_export(path):
    raw = path.read_bytes()
    rows = [json.loads(x) for x in raw.splitlines()]
    return {"sha": sha256(raw).hexdigest(), "meta": rows[0]["meta"],
            "decls": [("thm", rows[-1]["thm"])],
            "names": {1: "Demo"}, "exprs": {0: ("sort", 0)},
            "levels": {0: ("zero",)}}

def reachable(root, exprs, names):
    return {root}, set()

def expression_fingerprint(root, exprs, names, levels):
    return "synthetic-nonproof-fingerprint"
'''


class JMDReadonlyObservationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.spool = self.root / "out"
        self.spool.mkdir()
        self.builder = self.root / "build_jmd_lean_ast_world.py"
        self.builder.write_text(STUB_SOURCE)
        self.native = self.root / "native.ndjson"
        rows = [
            {"meta": {"format": {"version": "3.1.0"},
                      "lean": {"githash": "f" * 40}}},
            {"str": {"pre": 0, "str": "Demo"}, "in": 1},
            {"sort": 0, "ie": 0},
            {"thm": {"name": 1, "type": 0, "value": 0,
                     "all": [], "levelParams": []}},
        ]
        self.raw = ("\n".join(json.dumps(x) for x in rows) + "\n").encode()
        self.native.write_bytes(self.raw)
        self.source_hash = sha256(self.builder.read_bytes()).hexdigest()
        self.native_hash = sha256(self.raw).hexdigest()
        # Synthetic parser is used ONLY in offline tests; production is
        # hard-pinned to the independently read-back original PR105 SHA.
        pinned = patch.object(publisher, "JMD_PR105_SOURCE_SHA256", self.source_hash)
        pinned.start()
        self.addCleanup(pinned.stop)

    def publish(self, **changes):
        options = dict(
            source_path=self.builder, source_sha256=self.source_hash,
            export_path=self.native, export_sha256=self.native_hash,
            declaration="Demo", spool=self.spool)
        options.update(changes)
        return publish_jmd_readonly(**options)

    def test_synthetic_identity_published_idempotently_without_authority(self):
        a = self.publish()
        b = self.publish()
        self.assertEqual(a, b)
        observed = json.loads(Path(a["path"]).read_bytes())
        self.assertEqual(observed["native_export_sha256"], self.native_hash)
        self.assertEqual(observed["builder_source_sha256"], self.source_hash)
        self.assertEqual(observed["original_lean_revision"], "f" * 40)
        self.assertTrue(observed["used_original_jmd_builder_parser"])
        self.assertIs(observed["world_admitted"], False)
        self.assertIs(observed["typechecked_by_lean_here"], False)
        self.assertIs(a["kernel_certified"], False)
        self.assertEqual(len(list(self.spool.glob("*.jmd-readonly-observation.json"))), 1)

    def test_wrong_original_parser_hash_rejected_before_import(self):
        with self.assertRaisesRegex(JMDObservationError, "changed"):
            self.publish(source_sha256="0" * 64)

    def test_wrong_native_hash_or_declaration_rejected(self):
        with self.assertRaises(JMDObservationError):
            self.publish(export_sha256="a" * 64)
        with self.assertRaises(JMDObservationError):
            self.publish(declaration="Other")

    def test_mutated_parser_source_and_native_bytes_rejected(self):
        self.builder.write_text(STUB_SOURCE + "\n# changed")
        with self.assertRaises(JMDObservationError):
            self.publish()
        self.builder.write_text(STUB_SOURCE)
        self.native.write_bytes(self.raw + b"\n")
        with self.assertRaises(JMDObservationError):
            self.publish()

    def test_unsafe_spool_and_source_symlink_rejected(self):
        with self.assertRaises(JMDObservationError):
            self.publish(spool=self.root / "not-created")
        linked = self.root / "links"
        linked.symlink_to(self.spool, target_is_directory=True)
        with self.assertRaises(JMDObservationError):
            self.publish(spool=linked)
        target = self.root / "original_source.py"
        self.builder.rename(target)
        self.builder.symlink_to(target)
        with self.assertRaises(JMDObservationError):
            self.publish()

    def test_preexisting_conflicting_immutable_file_rejected(self):
        first = self.publish()
        Path(first["path"]).write_bytes(b"tampered")
        with self.assertRaisesRegex(JMDObservationError, "conflicting"):
            self.publish()


if __name__ == "__main__":
    unittest.main()
