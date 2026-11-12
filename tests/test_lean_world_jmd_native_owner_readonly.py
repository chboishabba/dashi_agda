#!/usr/bin/env python3
"""Original JMD PR105 AST builder parity, without a second SQLite world."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from lean_world_jmd_native_owner_readonly import (
    read_only_check,JMDNativeOwnerError)

def export(rows):
    return ("\n".join(json.dumps(r) for r in rows)+"\n").encode()

def fixture(revision="a"*40,invalid=False):
    return export([
       {"meta":{"format":{"version":"3.1.0"}},
        "lean":{"githash":revision},"exporter":{"version":"v3"}},
       {"str":{"pre":0,"str":"Demo"},"in":1},
       {"sort":0,"ie":0},
       {"thm":{"name":1,"levelParams":[],"type":0,
               "value":999 if invalid else 0,"all":[]}}
    ])

@unittest.skipUnless(os.environ.get("DASHI_JMD_AST_BUILDER_SOURCE"),
                     "requires actual JMD PR105 builder source")
class JMDReadOnlyOwner(unittest.TestCase):
    def setUp(self):
        self.root=tempfile.TemporaryDirectory()
        self.addCleanup(self.root.cleanup)
        self.path=Path(self.root.name)/"native.ndjson"
        self.owner=Path(os.environ["DASHI_JMD_AST_BUILDER_SOURCE"])

    def test_selected_native_type_and_proof_roots(self):
        raw=fixture()
        self.path.write_bytes(raw)
        result=read_only_check(
            source_path=self.owner,export_path=self.path,
            declaration="Demo",expected_export_sha=sha256(raw).hexdigest())
        self.assertTrue(result["used_original_jmd_builder_parser"])
        self.assertFalse(result["wrote_another_world_database"])
        self.assertFalse(result["world_admitted"])
        self.assertEqual(result["selected_type_reachable_nodes"],1)
        self.assertEqual(result["selected_proof_reachable_nodes"],1)

    def test_missing_proof_expr_fails(self):
        raw=fixture(invalid=True)
        self.path.write_bytes(raw)
        with self.assertRaises(ValueError):
            read_only_check(
                source_path=self.owner,export_path=self.path,
                declaration="Demo",expected_export_sha=sha256(raw).hexdigest())

    def test_wrong_digest_and_declaration_fail_closed(self):
        raw=fixture()
        self.path.write_bytes(raw)
        with self.assertRaisesRegex(JMDNativeOwnerError,"digest mismatch"):
            read_only_check(
                source_path=self.owner,export_path=self.path,
                declaration="Demo",expected_export_sha="c"*64)
        with self.assertRaisesRegex(JMDNativeOwnerError,"missing/ambiguous"):
            read_only_check(
                source_path=self.owner,export_path=self.path,
                declaration="NotDemo",expected_export_sha=sha256(raw).hexdigest())

if __name__=="__main__":
    unittest.main()
