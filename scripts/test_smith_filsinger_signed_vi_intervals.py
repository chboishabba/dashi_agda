"""Tests are deliberately synthetic arithmetic fixtures, NEVER original evidence."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from check_smith_filsinger_signed_vi_intervals import (
    PORTS, calculate, fraction, integrate_trapezoid, minus_interval, mul_interval,
)


class SignedWorkIntervalTests(unittest.TestCase):
    def setUp(self):
        self.tmp = TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.meta = {"original_id": "fixture-not-original-evidence",
                     "clock_id": "scope-clock-a",
                     "port_orientation": "positive_in_port_direction",
                     "integration_rule": "piecewise_linear_power_trapezoid",
                     "ports": {}}
        values = {
            "natural_incident": ("5", "1"),
            "natural_outgoing": ("2", "1"),
            "controller_incident": ("4", "1/2"),
            "controller_outgoing": ("1", "1"),
            "load_output": ("1", "2"),
        }
        for role, (v, i) in values.items():
            f = self.root / (role + ".csv")
            f.write_text(
                "time_s,voltage_V,current_A,voltage_error_V,current_error_A\n"
                f"0,{v},{i},0,0\n1,{v},{i},0,0\n", encoding="utf-8")
            self.meta["ports"][role] = {
                "file": f.name, "sha256": hashlib.sha256(f.read_bytes()).hexdigest(),
                "clock_id": "scope-clock-a"}

    def assert_reject(self, altered, error_piece):
        with self.assertRaisesRegex(ValueError, error_piece):
            calculate(altered, self.root)

    def test_exact_signed_five_port_work(self):
        receipt = calculate(self.meta, self.root)
        self.assertEqual(receipt["net_environmental_work"], {"lower_J": "3", "upper_J": "3"})
        self.assertEqual(receipt["net_controller_work"], {"lower_J": "1", "upper_J": "1"})
        self.assertEqual(receipt["useful_load_work"], {"lower_J": "2", "upper_J": "2"})
        self.assertEqual(receipt["unassigned_loss_or_storage_change"], {"lower_J": "2", "upper_J": "2"})
        self.assertFalse(receipt["physical_claim_closed"])
        self.assertFalse(receipt["f15_closed"])

    def test_exact_rational_product_enclosure_with_sign(self):
        self.assertEqual(mul_interval((Fraction(-2), Fraction(-1)),
                                      (Fraction(3), Fraction(5))),
                         (Fraction(-10), Fraction(-3)))

    def test_signed_difference_interval(self):
        self.assertEqual(minus_interval((Fraction(1), Fraction(3)),
                                        (Fraction(4), Fraction(6))),
                         (Fraction(-5), Fraction(-1)))

    def test_trapezoid_exact_half(self):
        self.assertEqual(integrate_trapezoid([Fraction(0), Fraction(1)],
                          [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(1))]),
                         (Fraction(1, 2), Fraction(1, 2)))

    def test_reject_clock_mismatch(self):
        self.meta["ports"]["load_output"]["clock_id"] = "different-clock"
        self.assert_reject(self.meta, "clock mismatch")

    def test_reject_duplicate_port_data(self):
        self.meta["ports"]["load_output"] = dict(self.meta["ports"]["natural_outgoing"])
        self.assert_reject(self.meta, "duplicate file")

    def test_reject_hash_mismatch(self):
        self.meta["ports"]["natural_incident"]["sha256"] = "0" * 64
        self.assert_reject(self.meta, "wrong SHA256")

    def test_reject_wrong_time_grid(self):
        f = self.root / "load_output.csv"
        f.write_text(f.read_text().replace("1,1,2,0,0", "2,1,2,0,0"))
        self.meta["ports"]["load_output"]["sha256"] = hashlib.sha256(f.read_bytes()).hexdigest()
        self.assert_reject(self.meta, "nonidentical original time grid")

    def test_reject_negative_uncertainty_radius(self):
        f = self.root / "natural_incident.csv"
        f.write_text(f.read_text().replace(",0,0\n", ",-1,0\n"))
        self.meta["ports"]["natural_incident"]["sha256"] = hashlib.sha256(f.read_bytes()).hexdigest()
        self.assert_reject(self.meta, "negative uncertainty")

    def test_reject_unknown_orientation(self):
        self.meta["port_orientation"] = "unsigned_power"
        self.assert_reject(self.meta, "explicit signed")

    def test_reject_incomplete_port_coverage(self):
        del self.meta["ports"]["natural_outgoing"]
        self.assert_reject(self.meta, "five original port")

    def test_reject_nonexact_floats(self):
        with self.assertRaises(ValueError):
            fraction(1.0)

    def test_reject_repeated_times(self):
        f = self.root / "natural_incident.csv"
        f.write_text(f.read_text().replace("1,5,1,0,0", "0,5,1,0,0"))
        self.meta["ports"]["natural_incident"]["sha256"] = hashlib.sha256(f.read_bytes()).hexdigest()
        self.assert_reject(self.meta, "nonincreasing")


if __name__ == "__main__":
    unittest.main()
