"""Regression of the Zhang/Pais non-promotion and bounded-force consumer."""
import json
import math
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check_zhang2025_em_gravity_bidi as m


def bound(n=0.0, u=0.0):
    # A fixture receipt proves nothing about the apparatus; it makes zeros explicit.
    return {"nominal_N": n, "bound_N": u, "evidence_receipt": "SYNTHETIC/fixture-only"}


def run(mode: str, reading: float):
    return {
        "source_mode": mode,
        "apparatus_id": "SYNTHETIC/rig-A",
        "target_id": "SYNTHETIC/polymer-ball",
        "force_axis": "SYNTHETIC/x-axis",
        "configuration_id": "SYNTHETIC/cfg-1",
        "calibration_id": "SYNTHETIC/cal-1",
        "instrument_id": "SYNTHETIC/meter-1",
        "run_id": "fixture-run-" + mode,
        "raw_data_sha256": ("a" if mode == "ON" else "b") * 64,
        "channel": "signed_force_N",
        "measurement": bound(reading, 1e-10),
        "force_classes": {c: bound() for c in m.REQUIRED_FORCE_CLASSES},
    }


def case():
    on = run("ON", 2e-9)
    off = run("OFF", 0.0)
    on["force_classes"]["charge_force"] = bound(2e-9, 1e-10)
    return {
        "patent_reference": m.PATENT_US,
        "data_kind": "synthetic",
        "on": on,
        "off": off,
    }


class ZhangPatentForceAuditTests(unittest.TestCase):
    def test_committed_json_fixture_is_synthetic_only(self):
        fixture = Path(__file__).resolve().parent / "fixtures" / "zhang2025_synthetic_pair.json"
        result = m.evaluate(json.loads(fixture.read_text(encoding="utf-8")))
        self.assertEqual(result["status"], "synthetic_fixture_only")
        self.assertFalse(result["gravity_identified"])

    def test_patent_power_nominal_not_metric(self):
        self.assertEqual(m.nominal_input_power(50000, 1e-5), 0.5)

    def test_coulomb_and_dep_signs(self):
        self.assertAlmostEqual(m.linear_electric_force(1e-12, 500), 5e-10)
        self.assertAlmostEqual(m.linear_dielectrophoresis(2e-20, 1e8), 1e-12)
        self.assertAlmostEqual(m.linear_dielectrophoresis(2e-20, -1e8), -1e-12)

    def test_magnetic_gradient_has_correct_sign(self):
        self.assertGreater(m.linear_magnetic_gradient(0.01, 1e-6, 2), 0)
        self.assertLess(m.linear_magnetic_gradient(-0.01, 1e-6, 2), 0)

    def test_interval_subtracts_extrema(self):
        v = m.Interval(1, 3) - m.Interval(4, 6)
        self.assertEqual((v.lo, v.hi), (-5, -1))

    def test_complete_synthetic_is_never_empirical_anomaly(self):
        result = m.evaluate(case())
        self.assertEqual(result["status"], "synthetic_fixture_only")
        self.assertFalse(result["gravity_identified"])
        self.assertFalse(result["metric_or_TT_strain_established"])
        self.assertFalse(result["nonzero_residual_interval"])

    def test_missing_class_is_not_zero_default(self):
        sample = case()
        del sample["on"]["force_classes"]["dielectrophoresis"]
        result = m.evaluate(sample)
        self.assertEqual(result["status"], "incomplete_ordinary_force_comparator")
        self.assertEqual(result["missing_force_classes"], ["dielectrophoresis"])
        self.assertNotIn("unexplained_signed_force_N", result)

    def test_identity_mismatch_rejected(self):
        sample = case()
        sample["off"]["target_id"] = "other-target"
        with self.assertRaisesRegex(ValueError, "same-object mismatch"):
            m.evaluate(sample)

    def test_rotation_is_not_a_force_reading(self):
        sample = case()
        sample["on"]["channel"] = "ball_rotation_radians"
        with self.assertRaisesRegex(ValueError, "signed_force_N"):
            m.evaluate(sample)

    def test_all_classes_require_evidence_receipts(self):
        sample = case()
        sample["on"]["force_classes"]["suspension_and_support"]["evidence_receipt"] = ""
        with self.assertRaisesRegex(ValueError, "evidence_receipt"):
            m.evaluate(sample)

    def test_real_unverified_candidate_is_not_gravity(self):
        sample = case()
        sample["data_kind"] = "real_unverified"
        sample["on"]["measurement"] = bound(1e-7, 1e-10)
        result = m.evaluate(sample)
        self.assertEqual(result["status"], "candidate_unexplained_signed_force_residual")
        self.assertTrue(result["nonzero_residual_interval"])
        self.assertFalse(result["gravity_identified"])
        self.assertFalse(result["independent_replication_established"])

    def test_overlapping_interval_not_candidate(self):
        sample = case()
        sample["data_kind"] = "real_unverified"
        sample["on"]["measurement"] = bound(2e-9, 1e-9)
        result = m.evaluate(sample)
        self.assertEqual(result["status"], "ordinary_force_interval_compatible")

    def test_nan_and_negative_bound_rejected(self):
        sample = case()
        sample["on"]["measurement"]["nominal_N"] = math.nan
        with self.assertRaisesRegex(ValueError, "nonfinite"):
            m.evaluate(sample)
        sample = case()
        sample["on"]["measurement"]["bound_N"] = -1.0
        with self.assertRaisesRegex(ValueError, "negative uncertainty"):
            m.evaluate(sample)

    def test_different_modes_and_duplicate_run_ids_rejected(self):
        sample = case()
        sample["off"]["source_mode"] = "ON"
        with self.assertRaisesRegex(ValueError, "source_mode"):
            m.evaluate(sample)
        sample = case()
        sample["off"]["run_id"] = sample["on"]["run_id"]
        with self.assertRaisesRegex(ValueError, "distinct runs"):
            m.evaluate(sample)

    def test_invalid_hash_rejected(self):
        sample = case()
        sample["off"]["raw_data_sha256"] = "not-a-hash"
        with self.assertRaisesRegex(ValueError, "64-character"):
            m.evaluate(sample)


if __name__ == "__main__":
    unittest.main()
