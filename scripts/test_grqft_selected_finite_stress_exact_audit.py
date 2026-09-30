#!/usr/bin/env python3
"""Regression tests for exact-fraction selected finite stress calculations."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "finite_stress", ROOT / "grqft_selected_finite_stress_exact_audit.py")
assert spec and spec.loader
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def fixture(*, derivative00="1", insertion00="1"):
    slots = list(module.SLOTS)
    ds = {slot: "0" for slot in slots}
    d_o = {slot: "0" for slot in slots}
    ds["00"], ds["11"] = derivative00, "-" + derivative00
    d_o["00"] = insertion00
    return {
        "provenance": {
            "source_identifier": "DASHI-internal-test-only",
            "revision": "toy-test-not-CMP119",
            "selected_action": "finite-test-Wilson-variation",
            "measure_identifier": "single-config-Haar-test",
            "cutoff": "toy",
            "metric_frame": "orthonormal-signature-test-only",
            "observable_identifier": "test-insertion",
            "normalization": "exact-fraction-test",
            "haar_metric_independent": True,
            "gibbs_logarithmic_derivative": "d_rho=-rho*dS"
        },
        "slots": slots,
        "configurations": [{
            "id": "only-configuration",
            "haar_weight": "1",
            "density": "2",
            "insertion": "3",
            "d_action": ds,
            "d_insertion": d_o
        }]
    }


class SelectedFiniteStressAuditTest(unittest.TestCase):
    def test_action_derivative_cancels_in_single_state_connected_source(self):
        out = module.audit(fixture())
        self.assertEqual(out["Z"], "2")
        self.assertEqual(out["A"], "6")
        self.assertEqual(out["connected_cross_numerator"]["00"], "4")
        self.assertEqual(out["connected_cross_numerator"]["11"], "0")
        self.assertEqual(out["four_diagonal_sum"], "4")
        self.assertEqual(out["gibbs_trace_insertion"], "2")
        self.assertEqual(out["connected_normalized_derivative"]["00"], "1")
        self.assertFalse(out["physical_source_identification_proved"])

    def test_negative_trace_is_diagnostic_not_a_physical_claim(self):
        out = module.audit(fixture(insertion00="-1"))
        self.assertEqual(out["four_diagonal_sum"], "-4")
        self.assertFalse(out["weak_coupling_nonnegative_active_compatible"])
        self.assertFalse(out["renormalized_continuum_stress_proved"])

    def test_trace_silent_insertion_has_zero_diagonal_sum(self):
        out = module.audit(fixture(insertion00="0"))
        self.assertEqual(out["four_diagonal_sum"], "0")
        self.assertEqual(out["trace_identity_rhs"], "0")

    def test_rejects_action_weyl_trace_violation(self):
        f = fixture()
        f["configurations"][0]["d_action"]["11"] = "0"
        with self.assertRaisesRegex(ValueError, "classical d=4 Wilson action trace"):
            module.audit(f)

    def test_requires_all_ten_slots(self):
        f = fixture()
        del f["configurations"][0]["d_insertion"]["23"]
        with self.assertRaisesRegex(ValueError, "ten canonical slots"):
            module.audit(f)

    def test_rejects_nonpositive_partition(self):
        f = fixture()
        f["configurations"][0]["density"] = "0"
        with self.assertRaisesRegex(ValueError, "not strictly positive"):
            module.audit(f)

    def test_rejects_implicit_haar_assumption(self):
        f = fixture()
        del f["provenance"]["haar_metric_independent"]
        with self.assertRaisesRegex(ValueError, "Metric independence"):
            module.audit(f)


    def test_same_frame_geometry_residual_detects_wrong_source(self):
        f = fixture()
        f["geometry_diagnostic"] = {
            "metric_frame": f["provenance"]["metric_frame"],
            "geometry_revision": "finite-test-only",
            "source_to_geometry_normalization": "1",
            "einstein_tensor": {slot: ("1" if slot == "00" else "0")
                                for slot in module.SLOTS}
        }
        self.assertTrue(module.audit(f)["geometry_diagnostic"]["all_ten_residuals_zero"])
        f["geometry_diagnostic"]["einstein_tensor"]["11"] = "1"
        observed = module.audit(f)["geometry_diagnostic"]
        self.assertFalse(observed["all_ten_residuals_zero"])
        self.assertEqual(observed["ten_slot_residual"]["11"], "1")
        self.assertFalse(observed["physical_same_object_identification_proved"])

    def test_different_geometry_frame_is_rejected(self):
        f = fixture()
        f["geometry_diagnostic"] = {
            "metric_frame": "other-signature",
            "geometry_revision": "toy-test",
            "source_to_geometry_normalization": "1",
            "einstein_tensor": {slot: "0" for slot in module.SLOTS}
        }
        with self.assertRaisesRegex(ValueError, "different metric frame"):
            module.audit(f)


if __name__ == "__main__":
    unittest.main()
