#!/usr/bin/env python3
"""Immutable native handoff to type observation: never world admission."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import json
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
sys.path.insert(0,str(ROOT/"tests"))
from test_lean_world_native_admission_queue import sample
from lean_world_native_admission_queue import enqueue
from run_lean_world_native_v3_projection import project,ProjectionError


def fixture(root):
    receipt=sample(root)
    lines=[
        {"meta":{"format":{"version":"3.1.0"}}},
        {"str":{"pre":0,"str":"yes"},"in":1},
        {"sort":0,"ie":1},
        {"thm":{"name":1,"levelParams":[],"type":1,"value":1,"all":[]}}
    ]
    raw=("\n".join(json.dumps(x) for x in lines)+"\n").encode()
    artifact=root/"source.ndjson"
    artifact.write_bytes(raw)
    digest=sha256(raw).hexdigest()
    receipt["artifact_path"]=str(artifact)
    receipt["artifact_sha256"]=digest
    receipt["validation"]["export_sha256"]=digest
    receipt["validation"]["ndjson_records"]=len(lines)
    receipt["validation"]["declaration_records"]=1
    handoff=enqueue(receipt,root/"queue")
    return Path(handoff["manifest"])


class ProjectionObservation(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.manifest=fixture(self.root)

    def test_pinned_original_type_observation_is_idempotent(self):
        first=project(self.manifest,"yes",self.root/"queue")
        second=project(self.manifest,"yes",self.root/"queue")
        self.assertEqual(first,second)
        item=json.loads(Path(first["path"]).read_text())
        self.assertEqual(item["declaration"],"yes")
        self.assertEqual(item["canonical_type_sha256"],
                         sha256(__import__("base64").b64decode(
                             item["canonical_type_b64"])).hexdigest())
        for field in ("kernel_certified","world_admitted",
                      "native_dag_complete","imported_dependencies_resolved"):
            self.assertIs(item[field],False)

    def test_wrong_original_declaration_rejected(self):
        with self.assertRaisesRegex(ProjectionError,"differs"):
            project(self.manifest,"someoneElse",self.root/"queue")

    def test_original_export_tamper_rejected(self):
        source=next((self.root/"queue").glob("*.ndjson"))
        source.write_bytes(b"malicious")
        with self.assertRaises(ValueError):
            project(self.manifest,"yes",self.root/"queue")

if __name__=="__main__":
    unittest.main()
