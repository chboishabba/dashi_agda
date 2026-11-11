"""Negative controls for the read-only authoritative builder interface."""
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_world_builder_contract import (
    ContractError, BuilderResult, pending_from_manifest, validate_through_builder,
)

class BuilderContractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.raw = b'{"meta":{"format":{"version":"3.0"}}}\n{"thm":{}}\n'
        h = hashlib.sha256(self.raw).hexdigest()
        self.artifact = self.root / (h + ".ndjson")
        self.artifact.write_bytes(self.raw)
        self.record = {
            "schema": "dashi-lean-world-native-handoff-v1",
            "status": "pending-authoritative-dag-validation",
            "world_admitted": False, "kernel_proof_certified": False,
            "repository": "org/repo", "revision": "a" * 40,
            "module": "Foo", "declaration": "Foo.bar",
            "toolchain": "lean4", "dependency_closure_id": "closure",
            "source_closure": [["Foo.lean", "b" * 64]],
            "export_sha256": h, "artifact_path": str(self.artifact),
            "ndjson_records": 2, "declaration_records": 1,
        }
        self.write_manifest()

    def write_manifest(self):
        identity = {k:v for k,v in self.record.items() if k != "artifact_path"}
        h = hashlib.sha256(json.dumps(identity, sort_keys=True,
                                     separators=(",", ":")).encode()).hexdigest()
        self.manifest = self.root / (h + ".json")
        self.manifest.write_text(json.dumps(self.record))

    def test_valid_unadmitted_source(self):
        self.assertEqual(pending_from_manifest(self.manifest).artifact, self.raw)

    def test_reject_promoted_queue(self):
        self.record["world_admitted"] = True
        self.write_manifest()
        with self.assertRaises(ContractError): pending_from_manifest(self.manifest)

    def test_reject_tampered_artifact(self):
        self.artifact.write_bytes(b"bad")
        with self.assertRaises(ContractError): pending_from_manifest(self.manifest)

    def test_reject_changed_identity(self):
        self.record["module"] = "Changed"
        self.manifest.write_text(json.dumps(self.record))
        with self.assertRaises(ContractError): pending_from_manifest(self.manifest)

    def test_reject_symlink_artifact(self):
        target = self.root / "target.ndjson"
        self.artifact.rename(target)
        self.artifact.symlink_to(target)
        with self.assertRaises(ContractError): pending_from_manifest(self.manifest)

    def test_reject_duplicate_closure_source(self):
        self.record["source_closure"].append(["Foo.lean", "c"*64])
        self.write_manifest()
        with self.assertRaises(ContractError): pending_from_manifest(self.manifest)

    def test_external_builder_must_validate(self):
        class Rejected:
            def validate(self, p):
                return BuilderResult(p.handoff_key,p.artifact_sha256,"validator",
                                     "c"*64,("n1",),(),False,False)
        with self.assertRaises(ContractError):
            validate_through_builder(pending_from_manifest(self.manifest), Rejected())

    def test_external_builder_binding_required(self):
        class Mismatch:
            def validate(self, p):
                return BuilderResult("wrong",p.artifact_sha256,"validator",
                                     "c"*64,("n1",),(),True,False)
        with self.assertRaises(ContractError):
            validate_through_builder(pending_from_manifest(self.manifest), Mismatch())

    def test_unresolved_edges_rejected(self):
        class Unresolved:
            def validate(self, p):
                return BuilderResult(p.handoff_key,p.artifact_sha256,"validator",
                                     "c"*64,("n1",),(("n1","missing"),),True,False)
        with self.assertRaises(ContractError):
            validate_through_builder(pending_from_manifest(self.manifest), Unresolved())

    def test_shape_acceptance_never_certifies(self):
        class Stub:
            def validate(self, p):
                return BuilderResult(p.handoff_key,p.artifact_sha256,"stub",
                                     "c"*64,("n1",),(),True,False)
        result = validate_through_builder(pending_from_manifest(self.manifest), Stub())
        self.assertFalse(result.kernel_certified)
        self.assertFalse(self.record["world_admitted"])

if __name__ == "__main__":
    unittest.main()
