"""Executable reduced-data R2P2 diagnostics (all fixtures synthetic)."""
import sys
import tempfile
import json
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from r2p2_clock_comparison_diagnostic import (  # noqa: E402
    comb_frequency,
    load_reduced_input,
    ReducedClockComparison,
    synthetic_demonstration,
    validate_covariance,
    TwoBaselineComparison,
    load_two_baseline_input,
)


class R2P2ClockComparisonDiagnosticTest(unittest.TestCase):
    def test_two_signed_comb_branches(self):
        self.assertEqual(comb_frequency(3, Fraction(10), Fraction(2), Fraction(4)), 36)
        self.assertEqual(comb_frequency(3, Fraction(10), Fraction(2), Fraction(-4)), 28)
        for n, rep, offset in [(-1, 10, 2), (2, 0, 0), (2, 10, 10)]:
            with self.subTest((n, rep, offset)), self.assertRaises(ValueError):
                comb_frequency(n, Fraction(rep), Fraction(offset), Fraction(4))

    def test_exact_synthetic_null_and_never_promotes(self):
        result = synthetic_demonstration().analyze()
        self.assertEqual(result["residual_fractional"], "0")
        self.assertEqual(result["residual_variance_fractional_squared"], str(Fraction(201, 10**38)))
        self.assertEqual(result["source_kind"], "synthetic")
        self.assertIs(result["external_measurement_authority_verified"], False)
        self.assertIs(result["gravity_deviation_claimed"], False)
        self.assertIs(result["quantum_gravity_claimed"], False)

    def test_correlation_signs(self):
        sigma = Fraction(1, 100)
        c = (
            (sigma, Fraction(1, 200), Fraction(0)),
            (Fraction(1, 200), sigma, Fraction(0)),
            (Fraction(0), Fraction(0), sigma),
        )
        result = ReducedClockComparison(Fraction(1), Fraction(0), Fraction(0), c).analyze()
        # For (1,-1,-1), covariance 0,1 contribution is -2*(1/200).
        self.assertEqual(result["residual_variance_fractional_squared"], str(Fraction(1, 50)))

    def test_reject_non_covariance_inputs(self):
        with self.assertRaises(ValueError):
            validate_covariance(((Fraction(1), Fraction(2), Fraction(0)),
                                 (Fraction(2), Fraction(1), Fraction(0)),
                                 (Fraction(0), Fraction(0), Fraction(1))))
        with self.assertRaises(ValueError):
            validate_covariance(((Fraction(1), Fraction(2), Fraction(0)),
                                 (Fraction(0), Fraction(1), Fraction(0)),
                                 (Fraction(0), Fraction(0), Fraction(1))))

    def test_two_baselines_separate_slope_and_bias_if_shared(self):
        # Two independent synthetic potential lever arms, NOT two clock sites.
        observation = TwoBaselineComparison(
            x1=Fraction(3), x2=Fraction(9),
            measured1=Fraction(9), measured2=Fraction(15),
            transfer1=Fraction(0), transfer2=Fraction(0),
            corrected_covariance=(
                (Fraction(1, 100), Fraction(0)),
                (Fraction(0), Fraction(1, 100)),
            ),
        )
        result = observation.analyze()
        self.assertEqual(result["conditional_slope"], "1")
        self.assertEqual(result["conditional_bias"], "6")
        self.assertEqual(result["slope_variance_if_potentials_exact"], str(Fraction(1, 1800)))
        self.assertFalse(result["same_bias_across_baselines_proven"])
        self.assertFalse(result["geopotential_calibrated_here"])
        self.assertFalse(result["external_measurement_authority_verified"])

    def test_two_baseline_zero_lever_arm_and_invalid_covariance_rejected(self):
        def fixture(x2=Fraction(9), covariance=((Fraction(1), Fraction(0)), (Fraction(0), Fraction(1)))):
            return TwoBaselineComparison(
                x1=Fraction(3), x2=x2,
                measured1=Fraction(9), measured2=Fraction(15),
                transfer1=Fraction(0), transfer2=Fraction(0),
                corrected_covariance=covariance,
            )
        with self.assertRaises(ValueError):
            fixture(x2=Fraction(3)).analyze()
        with self.assertRaises(ValueError):
            fixture(covariance=((Fraction(1), Fraction(2)), (Fraction(2), Fraction(1)))).analyze()
        with self.assertRaises(ValueError):
            fixture(covariance=((Fraction(1), Fraction(1)), (Fraction(0), Fraction(1)))).analyze()

    def test_two_baseline_file_is_unverified(self):
        payload = {
            "potential_ratio_1": "3", "potential_ratio_2": "9",
            "measured_fractional_ratio_1": "9", "measured_fractional_ratio_2": "15",
            "transfer_correction_1": "0", "transfer_correction_2": "0",
            "corrected_covariance": [["1/100", "0"], ["0", "1/100"]],
            "source_kind": "externally_supplied_unverified",
        }
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "two.json"
            path.write_text(json.dumps(payload), encoding="utf-8")
            result = load_two_baseline_input(path).analyze()
        self.assertEqual(result["conditional_slope"], "1")
        self.assertFalse(result["external_measurement_authority_verified"])

    def test_external_json_does_not_claim_verification(self):
        fixture = {
            "source_kind": "externally_supplied_unverified",
            "measured_fractional_ratio": "2/10",
            "transfer_fractional_correction": "1/10",
            "predicted_gr_fractional_ratio": "1/10",
            "covariance": [
                ["1/100", "0", "0"],
                ["0", "1/100", "0"],
                ["0", "0", "1/100"],
            ],
        }
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "reduced.json"
            path.write_text(json.dumps(fixture), encoding="utf-8")
            observed = load_reduced_input(path).analyze()
        self.assertEqual(observed["residual_fractional"], "0")
        self.assertFalse(observed["external_measurement_authority_verified"])
        self.assertEqual(observed["source_kind"], "externally_supplied_unverified")


if __name__ == "__main__":
    unittest.main()
