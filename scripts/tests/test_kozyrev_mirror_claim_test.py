"""Executable regressions for the Kozyrev mirror claim-testing assay.

Only synthetic fixtures are used. They are NOT observations or evidence.
"""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "kozyrev_mirror_claim_test.py"
SPEC = importlib.util.spec_from_file_location("kozyrev_mirror_claim_test", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
assay = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(assay)


def synthetic_manifest(n=6, claim="KM-SCATTER"):
    return {
        "study_id": "SYNTHETIC-ONLY",
        "claim_id": claim,
        "source_uri": "https://patents.google.com/patent/RU2122446C1/en",
        "primary_outcome": "instrument response",
        "outcome_unit": "arbitrary fixture units",
        "n_pairs": n,
        "direction": "positive",
        "minimum_effect": 0.5,
        "alpha": 0.05,
        "preregistration_uri": "https://example.invalid/NOT-REGISTERED",
        "preregistration_timestamp_utc": "2026-10-27T00:00:00Z",
        "randomization_method": "fixture: permuted balanced pair order",
        "blinding_policy": "fixture only",
        "sham_description": "geometry-matched passive dummy",
        "calibration_reference": "fixture only",
        "negative_controls": ["empty chamber", "equilibrium"],
        "confound_controls": ["temperature", "radiofrequency interference"],
        "analysis_plan": "exact paired sign-flip, fixed direction",
        "safety_approval_status": "not_applicable_nonhuman",
        "independent_replication_plan": "external laboratory required",
    }


class KozyrevMirrorAssayTests(unittest.TestCase):
    def test_validation_rejects_unoperationalised_and_no_controls(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "plan.json"
            plan = synthetic_manifest()
            plan["claim_id"] = "KM-TORSION"
            path.write_text(json.dumps(plan))
            with self.assertRaises(assay.InvalidEvidence):
                assay.parse_manifest(path)
            plan["claim_id"] = "KM-SCATTER"
            plan["negative_controls"] = []
            path.write_text(json.dumps(plan))
            with self.assertRaises(assay.InvalidEvidence):
                assay.parse_manifest(path)

    def test_human_claim_requires_recorded_approval(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "plan.json"
            plan = synthetic_manifest(claim="KM-CLINICAL")
            path.write_text(json.dumps(plan))
            with self.assertRaises(assay.InvalidEvidence):
                assay.parse_manifest(path)

    def test_exact_signflip_symmetric_null(self):
        self.assertEqual(assay.exact_sign_flip([0, 0, 0, 0], "two-sided"), 1)
        self.assertEqual(assay.exact_sign_flip([1, 1, 1, 1], "positive"), 1 / 16)
        self.assertEqual(assay.exact_sign_flip([1, 1, 1, 1], "two-sided"), 2 / 16)

    def test_csv_guards_and_fail_closed_verdict(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "results.csv"
            path.write_text(
                "pair_id,condition,outcome\n"
                + "".join(
                    f"{i},active,1\n{i},sham,0\n" for i in range(6)
                ), encoding="utf-8"
            )
            result = assay.analyze(synthetic_manifest(), path)
            self.assertEqual(result["exact_sign_flip_p"], 1 / 64)
            self.assertEqual(result["paired_active_minus_sham_mean"], 1)
            self.assertEqual(
                result["signal_status"], "candidate_statistical_signal_requires_audit"
            )
            self.assertFalse(result["physical_effect_established"])
            self.assertFalse(result["clinical_efficacy_established"])
            path.write_text(
                "pair_id,condition,outcome\n"
                "1,active,2\n1,active,3\n1,sham,0\n"
            )
            with self.assertRaises(assay.InvalidEvidence):
                assay.paired_differences(path, 1)

    def test_hash_mismatch_never_reaches_analysis(self):
        with tempfile.TemporaryDirectory() as tmp:
            plan_path = Path(tmp) / "plan.json"
            data_path = Path(tmp) / "data.csv"
            plan_path.write_text(json.dumps(synthetic_manifest()))
            data_path.write_text(
                "pair_id,condition,outcome\n"
                + "".join(f"{i},active,1\n{i},sham,0\n" for i in range(6))
            )
            from contextlib import redirect_stdout
            from io import StringIO
            output = StringIO()
            with redirect_stdout(output):
                code = assay.main(
                    ["--plan", str(plan_path), "--data", str(data_path),
                     "--frozen-plan-sha256", "0" * 64,
                     "--frozen-data-sha256", assay.sha256(data_path)]
                )
            self.assertEqual(code, 2)
            self.assertFalse(json.loads(output.getvalue())["empirical_promotion"])


if __name__ == "__main__":
    unittest.main()
