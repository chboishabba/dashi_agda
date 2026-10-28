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
