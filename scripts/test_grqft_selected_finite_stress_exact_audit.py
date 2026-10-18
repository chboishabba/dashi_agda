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
        self.assertFalse(out["candidate_sign_compatible_with_weak_coupling_nonnegative_active_if_physically_identified"])
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
            "selected_source_identifier": f["provenance"]["source_identifier"],
            "cutoff": f["provenance"]["cutoff"],
            "normalization_origin": "independent-toy-value",
            "factor_fitted_to_this_geometry": False,
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
            "selected_source_identifier": f["provenance"]["source_identifier"],
            "cutoff": f["provenance"]["cutoff"],
            "normalization_origin": "independent-toy-value",
            "factor_fitted_to_this_geometry": False,
            "source_to_geometry_normalization": "1",
            "einstein_tensor": {slot: "0" for slot in module.SLOTS}
        }
        with self.assertRaisesRegex(ValueError, "different metric frame"):
            module.audit(f)


    def selected_lorentzian(self, f, rho):
        f["lorentzian_timelike"] = {
            "selected_source_identifier": f["provenance"]["source_identifier"],
            "cutoff": f["provenance"]["cutoff"],
            "metric_frame": f["provenance"]["metric_frame"],
            "continuation_revision": "explicit-toy-not-a-proof",
            "continuation_method": "toy-input-no-Wick-theorem",
            "counterterm_revision": "none-toy",
            "value_fitted_to_target_gravity": False,
            "timelike_numerator": rho
        }

    def test_lorentzian_timelike_correction_is_not_euclidean_label(self):
        f = fixture(insertion00="-1")
        self.selected_lorentzian(f, "0")
        d = module.audit(f)["lorentzian_timelike_diagnostic"]
        self.assertEqual(d["euclidean_time_numerator"], "-4")
        self.assertEqual(d["timelike_continuation_correction"], "4")
        self.assertEqual(d["continued_active_numerator"], "0")
        self.assertFalse(d["source_selected_continuation_proved"])

    def test_weak_YM_comparison_cannot_use_euclidean_time_implicitly(self):
        f = fixture(insertion00="-1")
        self.selected_lorentzian(f, "-4")
        f["weak_coupling_reference"] = {"reference_revision": "toy"}
        with self.assertRaisesRegex(ValueError, "requires separate continued timelike"):
            module.audit(f)

    def test_weak_coupling_reference_quantifies_missing_source(self):
        f = fixture(insertion00="-1")
        f["weak_coupling_reference"] = {
            "selected_source_identifier": f["provenance"]["source_identifier"],
            "metric_frame": f["provenance"]["metric_frame"],
            "cutoff": f["provenance"]["cutoff"],
            "reference_revision": "test-only",
            "normalization_origin": "fixed-toy-scale",
            "factor_fitted_to_this_source": False,
            "kappa": "1", "margin": "0",
            "electric_square": "1", "magnetic_square": "0",
            "connected_to_physical_active_factor": "1"
        }
        d = module.audit(f)["weak_coupling_diagnostic"]
        self.assertEqual(d["weak_coupling_baseline"], "4")
        self.assertEqual(d["candidate_active"], "-1")
        self.assertEqual(d["required_additional_active_source"], "-5")
        self.assertTrue(
            d["negative_candidate_requires_extra_more_negative_than_baseline"])
        self.assertFalse(d["weak_coupling_ym_only_compatible"])
        self.assertFalse(d["physical_same_tensor_identification_proved"])

    def test_weak_coupling_reference_requires_nonnegative_EB_squares(self):
        f = fixture()
        self.selected_lorentzian(f, "4")
        f["weak_coupling_reference"] = {
            "selected_source_identifier": f["provenance"]["source_identifier"],
            "metric_frame": f["provenance"]["metric_frame"],
            "cutoff": f["provenance"]["cutoff"],
            "reference_revision": "test-only",
            "normalization_origin": "fixed-toy-scale",
            "factor_fitted_to_this_source": False,
            "kappa": "1", "margin": "0",
            "electric_square": "-1", "magnetic_square": "0",
            "connected_to_physical_active_factor": "1"
        }
        with self.assertRaisesRegex(ValueError, "nonnegative coefficient"):
            module.audit(f)


if __name__ == "__main__":
    unittest.main()
