#!/usr/bin/env python3
"""Adversarial #1495/#1484 observation binding; synthetic receipts prove no checker success."""
from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "tests"))

from test_lean_world_native_admission_queue import sample
from lean_world_native_admission_queue import enqueue
from run_lean_world_native_v3_projection import project
from lean_world_builder_contract import pending_from_manifest
from lean_world_cross_pr_observation_join import join, ObservationJoinError


def canonical(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()


def emit(root, suffix, obj):
    raw = canonical(obj)
    path = root / (sha256(raw).hexdigest() + suffix)
    path.write_bytes(raw)
    return path


class CrossPrObservationJoinTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.spool = self.root / "queue"
        self.revision = "f" * 40
        original = sample(self.root)
        # Valid native-v3 STRUCTURE, but the fixture's "thm" value is
        # intentionally NOT asserted as a valid Lean proof. No binary runs.
        rows = [
            {"meta": {"format": {"version": "3.1.0"},
                      "lean": {"githash": self.revision}}},
            {"str": {"pre": 0, "str": "yes"}, "in": 1},
            {"sort": 0, "ie": 1},
            {"thm": {"name": 1, "levelParams": [],
                     "type": 1, "value": 1, "all": []}},
        ]
        raw = canonical(rows[0]) + canonical(rows[1]) + canonical(rows[2]) + canonical(rows[3])
        original_file = Path(original["artifact_path"])
        original_file.write_bytes(raw)
        original["artifact_sha256"] = sha256(raw).hexdigest()
        original["validation"]["export_sha256"] = original["artifact_sha256"]
        original["validation"]["ndjson_records"] = 4
        original["validation"]["declaration_records"] = 1
        handoff = enqueue(original, self.spool)
        self.manifest = Path(handoff["manifest"])
        self.pending = pending_from_manifest(self.manifest)
        self.projection = Path(project(self.manifest, "yes", self.spool)["path"])
        self.checker_obj = {
            "schema": "dashi-lean-external-check-observation-v1",
            "status": "rust-nanoda-exit-zero-uncertified",
            "checker_kind": "rust-nanoda",
            "native_manifest_key": self.pending.handoff_key,
            "handoff_key": self.pending.handoff_key,
            "artifact_sha256": self.pending.artifact_sha256,
            "executable_sha256": "c" * 64,
            "executable_path": "/synthetic/not-a-real-binary",
            "argv": ["nanoda-config", "d" * 64],
            "stdout_sha256": "e" * 64,
            "stderr_sha256": "b" * 64,
            "world_admitted": False,
            "kernel_certified": False,
        }
        self.checker = emit(
            self.spool, ".checker-observation.json", self.checker_obj)

    def invoke(self, projection=None, checker=None, **kwargs):
        return join(self.manifest, projection or self.projection,
                    checker or self.checker, self.spool, **kwargs)

    def test_same_native_identity_is_observed_not_certified(self):
        a = self.invoke()
        b = self.invoke()
        self.assertEqual(a, b)
        record = json.loads(Path(a["path"]).read_bytes())
        self.assertEqual(record["exact_type_sha256"],
                         json.loads(self.projection.read_bytes())[
                             "canonical_type_sha256"])
        for key in ("world_admitted", "kernel_certified",
                    "candidate_admission_authorized", "native_dag_complete",
                    "checker_semantics_authenticated",
                    "builder_authority_authenticated"):
            self.assertIs(record[key], False)

    def test_mutated_handoff_revision_is_rejected(self):
        original = json.loads(self.projection.read_bytes())
        original["revision"] = "0" * 40
        changed = emit(self.spool, ".native-type-observation.json", original)
        with self.assertRaisesRegex(ObservationJoinError, "revision"):
            self.invoke(projection=changed)

    def test_forged_projection_type_bytes_rejected_even_with_rehashed_file(self):
        original = json.loads(self.projection.read_bytes())
        original["canonical_type_b64"] = "ZmFrZQ=="
        original["canonical_type_sha256"] = sha256(b"fake").hexdigest()
        changed = emit(self.spool, ".native-type-observation.json", original)
        with self.assertRaises(ObservationJoinError):
            self.invoke(projection=changed)

    def test_forged_source_closure_rejected(self):
        original = json.loads(self.projection.read_bytes())
        original["source_closure"] = [["Target.lean", "0" * 64]]
        changed = emit(self.spool, ".native-type-observation.json", original)
        with self.assertRaisesRegex(ObservationJoinError, "source_closure"):
            self.invoke(projection=changed)

    def test_checker_for_different_native_export_is_rejected(self):
        other = dict(self.checker_obj)
        other["artifact_sha256"] = "a" * 64
        changed = emit(self.spool, ".checker-observation.json", other)
        with self.assertRaisesRegex(ObservationJoinError, "artifact_sha256"):
            self.invoke(checker=changed)

    def test_checker_promotion_or_wrong_policy_rejected(self):
        for change in (
            {"kernel_certified": True},
            {"world_admitted": True},
            {"argv": ["other-checker", "d" * 64]},
            {"native_manifest_key": "wrong"},
        ):
            with self.subTest(change=change):
                obj = {**self.checker_obj, **change}
                changed = emit(self.spool, ".checker-observation.json", obj)
                with self.assertRaises(ObservationJoinError):
                    self.invoke(checker=changed)

    def test_content_address_tamper_and_symlink_rejected(self):
        with tempfile.TemporaryDirectory() as other:
            target = Path(other) / self.projection.name
            target.write_bytes(self.projection.read_bytes())
            with self.assertRaisesRegex(ObservationJoinError, "outside"):
                self.invoke(projection=target)
        link = self.spool / "unsafe.native-type-observation.json"
        link.symlink_to(self.projection)
        with self.assertRaises(ObservationJoinError):
            self.invoke(projection=link)

    def fake_jmd(self):
        return {
            "status": "jmd-native-builder-readonly-roots-validated",
            "builder_source_sha256": "1" * 64,
            "native_export_sha256": self.pending.artifact_sha256,
            "selected_declaration": self.pending.declaration,
            "declaration_kind": "thm",
            "original_lean_revision": self.revision,
            "direct_type_constants": [],
            "direct_proof_constants": [],
            "used_original_jmd_builder_parser": True,
            "wrote_another_world_database": False,
            "typechecked_by_lean_here": False,
            "world_admitted": False,
        }

    def test_pinned_jmd_readonly_correlates_without_promotion(self):
        # This fixture is fabricated and says nothing about real JMD success.
        data = canonical(self.fake_jmd())
        path = self.root / "synthetic-jmd.json"
        path.write_bytes(data)
        result = self.invoke(
            jmd_path=path, jmd_sha256=sha256(data).hexdigest(),
            jmd_source_sha256="1" * 64)
        record = json.loads(Path(result["path"]).read_bytes())
        self.assertEqual(record["jmd_observation_sha256"],
                         sha256(data).hexdigest())
        self.assertFalse(record["world_admitted"])
        self.assertFalse(record["kernel_certified"])

    def test_jmd_mismatched_lean_revision_or_source_is_rejected(self):
        for key, value in (
            ("original_lean_revision", "f" * 39 + "e"),
            ("direct_type_constants", ["Fake"]),
            ("builder_source_sha256", "2" * 64),
            ("native_export_sha256", "3" * 64),
        ):
            with self.subTest(key=key):
                jmd = self.fake_jmd()
                jmd[key] = value
                raw = canonical(jmd)
                path = self.root / ("jmd-" + key + ".json")
                path.write_bytes(raw)
                with self.assertRaises(ObservationJoinError):
                    self.invoke(
                        jmd_path=path, jmd_sha256=sha256(raw).hexdigest(),
                        jmd_source_sha256="1" * 64)

    def test_jmd_without_independent_source_pin_is_rejected(self):
        raw = canonical(self.fake_jmd())
        path = self.root / "jmd.json"
        path.write_bytes(raw)
        with self.assertRaises(ObservationJoinError):
            self.invoke(jmd_path=path, jmd_sha256=sha256(raw).hexdigest())


if __name__ == "__main__":
    unittest.main()
