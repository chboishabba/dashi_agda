"""Fail-closed source-receipt adversarial tests; no invented physical samples."""
import hashlib
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from check_smith_filsinger_original_gate_evidence import ALL_ROLES, ROLES, check


class EvidenceGateTests(unittest.TestCase):
    def setUp(self):
        self.work = TemporaryDirectory()
        self.addCleanup(self.work.cleanup)
        self.root = Path(self.work.name)
        (self.root / "sample.dat").write_text("placeholder-data-is-not-a-physical-certificate", encoding="utf-8")
        self.digest = hashlib.sha256((self.root / "sample.dat").read_bytes()).hexdigest()
        self.original = "original-earth-reel-a"

    def rec(self, role):
        return {"role": role, "original_id": self.original, "kind": "raw_measurement",
                "producer": "source-a", "clock_id": "clock-a", "file": "sample.dat", "sha256": self.digest}

    def test_empty_is_fail_closed(self):
        r = check({"original_id": self.original, "records": []}, self.root)
        self.assertTrue(all(v["status"] == "AWAITING_ORIGINAL_EVIDENCE" for v in r["gates"].values()))
        self.assertFalse(r["physical_claim_closed"])

    def test_rejects_model_for_every_role(self):
        r = check({"original_id": self.original, "records": [
            {**self.rec(role), "kind": "model"} for role in ALL_ROLES
        ]}, self.root)
        self.assertTrue(all(g["raw_records_verified"] == 0 for g in r["gates"].values()))

    def test_rejects_wrong_original(self):
        rec = {**self.rec("field_flux"), "original_id": "another-machine"}
        r = check({"original_id": self.original, "records": [rec]}, self.root)
        self.assertIn("field_flux", r["gates"]["F10"]["missing_roles"])

    def test_rejects_bad_hash(self):
        rec = {**self.rec("field_flux"), "sha256": "0" * 64}
        self.assertTrue(check({"original_id": self.original, "records": [rec]}, self.root)["errors"])

    def test_rejects_escaping_tree(self):
        rec = {**self.rec("field_flux"), "file": "../outside.dat"}
        self.assertTrue(check({"original_id": self.original, "records": [rec]}, self.root)["errors"])

    def test_rejects_missing_clock(self):
        rec = {**self.rec("field_flux"), "clock_id": ""}
        self.assertTrue(check({"original_id": self.original, "records": [rec]}, self.root)["errors"])

    def test_duplicate_record_cannot_mask_missing_role(self):
        rec = self.rec("field_flux")
        r = check({"original_id": self.original, "records": [rec, rec]}, self.root)
        self.assertTrue(r["errors"])

    def test_valid_hash_is_only_readiness_not_acceptance(self):
        r = check({"original_id": self.original, "records": [
            self.rec(role) for role in ALL_ROLES
        ]}, self.root)
        self.assertTrue(all(v["status"] == "READY_FOR_INDEPENDENT_REVIEW_NOT_CLOSED" for v in r["gates"].values()))
        self.assertFalse(r["physical_claim_closed"])
        self.assertFalse(r["kernel_acceptance_established"])

    def test_all_gates_require_distinct_roles(self):
        self.assertEqual(len(ALL_ROLES), sum(map(len, ROLES.values())))
        r = check({"original_id": self.original, "records": [self.rec("field_flux")]}, self.root)
        self.assertEqual(r["gates"]["F10"]["raw_records_verified"], 1)
        self.assertEqual(r["gates"]["F15"]["raw_records_verified"], 0)

    def test_placeholder_original_is_rejected(self):
        r = check({"original_id": "hypothetical source", "records": []}, self.root)
        self.assertTrue(r["errors"])


if __name__ == "__main__":
    unittest.main()
