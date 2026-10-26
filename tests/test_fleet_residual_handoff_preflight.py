"""Offline regression for the fleet residual handoff preflight.

Run: python -m unittest discover -s tests -p 'test_fleet_residual_handoff_preflight.py'
"""
import importlib.util
from pathlib import Path
import unittest

PATH = Path(__file__).resolve().parents[1] / "scripts" / "fleet_residual_handoff_preflight.py"
spec = importlib.util.spec_from_file_location("fleet_residual_handoff_preflight", PATH)
import sys
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)


class PreflightTests(unittest.TestCase):
    def sample(self, **overrides):
        data = dict(canonical_thread_id="canonical-123", consumer_ref="DASHI.consumer",
                    residual_ref="collision-1", task_atom="Discriminate observer collision",
                    source_revision_ref="revision-1", source_digest="sha256:abc")
        data.update(overrides)
        return module.ResidualCandidate(**data)

    def test_review_only_never_promotes(self):
        result = module.operator_candidate(self.sample(), canonical_ids={"canonical-123"})
        self.assertEqual(result["state"], "candidate_only")
        self.assertFalse(result["preflight"]["promotion"])
        self.assertFalse(result["preflight"]["proof_verified"])
        self.assertFalse(result["preflight"]["dispatch_performed"])

    def test_unknown_canonical_id_held(self):
        result = module.operator_candidate(self.sample(), canonical_ids=set())
        self.assertEqual(result["state"], "held")
        self.assertIn("canonical_thread_unresolved", result["preflight"]["held_reasons"])

    def test_incomplete_source_held(self):
        result = module.operator_candidate(self.sample(source_digest=""), canonical_ids={"canonical-123"})
        self.assertEqual(result["state"], "held")

    def test_task_not_exposed_in_receipt(self):
        candidate = self.sample(task_atom="private task payload")
        receipt = module.preflight(candidate, canonical_ids={"canonical-123"})
        self.assertNotIn("private task payload", str(receipt))
        self.assertEqual(receipt, module.preflight(candidate, canonical_ids={"canonical-123"}))

    def test_oversize_task_held(self):
        result = module.operator_candidate(self.sample(task_atom="x" * 513), canonical_ids={"canonical-123"})
        self.assertEqual(result["state"], "held")


if __name__ == "__main__":
    unittest.main()
