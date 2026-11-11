"""Queue-to-read-only-builder contract integration, with no admission promotion."""
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_world_native_admission_queue import enqueue
from lean_world_builder_contract import pending_from_manifest, validate_through_builder, BuilderResult, ContractError
from test_lean_world_native_admission_queue import sample

class HandoffIntegrationTests(unittest.TestCase):
    def test_real_queue_manifest_roundtrip(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            receipt = sample(root)
            # Old receipts legitimately use an empty dependency closure ID.
            handoff = enqueue(receipt, root / "queue")
            export = pending_from_manifest(Path(handoff["manifest"]))
            self.assertEqual(export.handoff_key, handoff["handoff_key"])
            self.assertEqual(export.dependency_closure_id, "")

    def test_nonempty_closure_id_roundtrip(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            receipt = sample(root)
            receipt["dependency_closure_id"] = "pinned-local-imports"
            handoff = enqueue(receipt, root / "queue")
            export = pending_from_manifest(Path(handoff["manifest"]))
            self.assertEqual(export.handoff_key, handoff["handoff_key"])
            self.assertEqual(export.artifact_sha256, handoff["artifact_sha256"])
            self.assertFalse(receipt["world_admitted"])
            class FakeBuilder:
                def validate(self, p):
                    return BuilderResult(p.handoff_key, p.artifact_sha256,
                                         "stub", "c" * 64, ("node",), (), True, True)
            with self.assertRaises(ContractError):
                validate_through_builder(export, FakeBuilder())

if __name__ == "__main__":
    unittest.main()
