"""Original-file replay adversarial suite; fixtures are NOT physical evidence."""
import hashlib
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from check_smith_filsinger_signed_vi_intervals import calculate
from check_smith_filsinger_restored_cycle_intervals import analyze_from_original_files


def I(x):
    return {"lower_J": str(x), "upper_J": str(x)}


class FirstLawRawReplayTests(unittest.TestCase):
    def setUp(self):
        self.temporary = TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.meta = {
            "original_id": "synthetic-fixture-not-original",
            "clock_id": "scope-1",
            "port_orientation": "positive_in_port_direction",
            "integration_rule": "piecewise_linear_power_trapezoid",
            "ports": {},
        }
        for role, volts, amps in (
            ("natural_incident", 5, 1),
            ("natural_outgoing", 2, 1),
            ("controller_incident", 2, 1),
            ("controller_outgoing", 1, 1),
            ("load_output", 2, 1),
        ):
            csv = self.root / (role + ".csv")
            csv.write_text(
                "time_s,voltage_V,current_A,voltage_error_V,current_error_A\n"
                f"0,{volts},{amps},0,0\n1,{volts},{amps},0,0\n",
                encoding="utf-8",
            )
            cert = self.root / (role + ".error.txt")
            cert.write_text(f"synthetic assumption zero intersample error for {role}\n",
                            encoding="utf-8")
            self.meta["ports"][role] = {
                "file": csv.name, "sha256": hashlib.sha256(csv.read_bytes()).hexdigest(),
                "clock_id": "scope-1",
                "integration_error_bound_J": "0",
                "integration_error_certificate": cert.name,
                "integration_error_certificate_sha256":
                    hashlib.sha256(cert.read_bytes()).hexdigest(),
            }
        self.work = calculate(self.meta, self.root)
        self.ind = {
            "original_id": self.meta["original_id"],
            "clock_id": self.meta["clock_id"],
            "all_dissipative_and_outgoing_loss_J": I(2),
            "total_stored_energy_final_minus_initial_J": I(0),
        }

    def test_exact_replay_compatible_not_physical_acceptance(self):
        r = analyze_from_original_files(self.work, self.ind, self.meta, self.root)
        self.assertTrue(r["zero_in_first_law_residual"])
        self.assertFalse(r["f15_closed"])
        self.assertFalse(r["physical_claim_closed"])

    def test_reject_self_consistent_forged_natural_ports_and_summary(self):
        # Update *both* JSON port data and summaries to hide the forgery:
        # the preceding five-port-only check would accept this.
        self.work["conditional_port_work"]["natural_incident"] = I(7)
        self.work["net_environmental_work"] = I(5)
        self.work["unassigned_loss_or_storage_change"] = I(4)
        with self.assertRaisesRegex(ValueError, "original raw V/I files"):
            analyze_from_original_files(self.work, self.ind, self.meta, self.root)

    def test_reject_changed_raw_csv_with_stale_sha(self):
        file = self.root / "natural_incident.csv"
        file.write_text(file.read_text().replace("0,5,1", "0,8,1"))
        with self.assertRaisesRegex(ValueError, "SHA256"):
            analyze_from_original_files(self.work, self.ind, self.meta, self.root)

    def test_reject_inconsistent_original_manifest_clock(self):
        self.meta["ports"]["natural_incident"]["clock_id"] = "other"
        with self.assertRaisesRegex(ValueError, "clock mismatch"):
            analyze_from_original_files(self.work, self.ind, self.meta, self.root)

    def test_reject_missing_original_error_certificate(self):
        (self.root / "natural_incident.error.txt").unlink()
        with self.assertRaises((FileNotFoundError, ValueError)):
            analyze_from_original_files(self.work, self.ind, self.meta, self.root)

    def test_reject_wrong_apparatus_in_independent_receipt(self):
        self.ind["original_id"] = "other-apparatus"
        with self.assertRaisesRegex(ValueError, "apparatus"):
            analyze_from_original_files(self.work, self.ind, self.meta, self.root)

    def test_reject_tampered_loaded_work_only(self):
        self.work["useful_load_work"] = I(0)
        with self.assertRaisesRegex(ValueError, "original raw V/I files"):
            analyze_from_original_files(self.work, self.ind, self.meta, self.root)


if __name__ == "__main__":
    unittest.main()
