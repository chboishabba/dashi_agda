"""Source-file integrity acceptance tests; temporary bytes are synthetic."""
import copy
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check_zhang2025_evidence_packets as e


def sha(data):
    return hashlib.sha256(data).hexdigest()


class EvidencePacketTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        records = {
            "on.csv": b"t,x\n0,0\n1,1\n",
            "off.csv": b"t,x\n0,0\n1,0\n",
            "calibration.txt": b"synthetic calibration scale=1\n",
        }
        for name, data in records.items():
            (self.root / name).write_bytes(data)
        def run(mode):
            name = "on.csv" if mode == "ON" else "off.csv"
            return {
                "source_mode": mode, "run_id": "SYNTHETIC/" + mode,
                "lab_id": "SYNTHETIC/lab1", "apparatus_id": "SYNTHETIC/device1",
                "instrument_id": "SYNTHETIC/camera1",
                "calibration_revision": "SYNTHETIC/v1",
                "operator_source": "SYNTHETIC/fixture",
                "recorded_epoch_utc": "2026-11-06T00:00:00Z",
                "raw_file": name, "raw_sha256": sha(records[name]),
                "calibration_file": "calibration.txt",
                "calibration_sha256": sha(records["calibration.txt"]),
            }
        self.m = {
            "schema": "Zhang2025EvidencePacket/v1",
            "data_kind": "synthetic",
            "source_class": "zhang2025_toroid",
            "observable": "position_m",
            "protocol_id": "SYNTHETIC/protocol",
            "declared_regime_fingerprint": "SYNTHETIC/frequency-power-material",
            "blocks": [{
                "block_id": "SYNTHETIC/block1",
                "lab_id": "SYNTHETIC/lab1",
                "apparatus_id": "SYNTHETIC/device1",
                "pair": [run("ON"), run("OFF")],
            }],
        }

    def test_verified_packet_receipt_is_deterministic(self):
        a = e.verify_manifest(self.m, self.root)
        b = e.verify_manifest(self.m, self.root)
        self.assertEqual(a["verified_manifest_receipt_sha256"],
                         b["verified_manifest_receipt_sha256"])
        self.assertEqual(len(a["verified_manifest_receipt_sha256"]), 64)
        self.assertFalse(a["calibration_correctness_independently_authenticated"])

    def test_real_file_hashes_are_checked(self):
        r = e.verify_manifest(self.m, self.root)
        self.assertTrue(r["byte_integrity_checked"])
        self.assertEqual(r["verified_block_count"], 1)
        self.assertFalse(r["lab_identity_independently_authenticated"])
        self.assertFalse(r["gravity_anomaly_established"])

    def test_tampered_file_fails_digest(self):
        (self.root / "on.csv").write_bytes(b"modified")
        with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
            e.verify_manifest(self.m, self.root)

    def test_tampered_calibration_fails(self):
        (self.root / "calibration.txt").write_bytes(b"modified calibration")
        with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
            e.verify_manifest(self.m, self.root)

    def test_on_off_target_instrument_identity_mismatch(self):
        self.m["blocks"][0]["pair"][1]["instrument_id"] = "other-camera"
        with self.assertRaisesRegex(ValueError, "same-apparatus"):
            e.verify_manifest(self.m, self.root)

    def test_on_off_calibration_mismatch(self):
        self.m["blocks"][0]["pair"][1]["calibration_revision"] = "v2"
        with self.assertRaisesRegex(ValueError, "same-apparatus"):
            e.verify_manifest(self.m, self.root)

    def test_duplicate_raw_bytes_rejected_even_if_filename_differs(self):
        (self.root / "off.csv").write_bytes((self.root / "on.csv").read_bytes())
        self.m["blocks"][0]["pair"][1]["raw_sha256"] = self.m["blocks"][0]["pair"][0]["raw_sha256"]
        with self.assertRaisesRegex(ValueError, "duplicate"):
            e.verify_manifest(self.m, self.root)

    def test_same_run_ids_rejected(self):
        self.m["blocks"][0]["pair"][1]["run_id"] = self.m["blocks"][0]["pair"][0]["run_id"]
        with self.assertRaisesRegex(ValueError, "duplicate"):
            e.verify_manifest(self.m, self.root)

    def test_source_mode_duplicate_rejected(self):
        self.m["blocks"][0]["pair"][1]["source_mode"] = "ON"
        with self.assertRaisesRegex(ValueError, "one ON and one OFF"):
            e.verify_manifest(self.m, self.root)

    def test_manifest_apparatus_identity_rejected(self):
        self.m["blocks"][0]["apparatus_id"] = "other-physical-rig"
        with self.assertRaisesRegex(ValueError, "block apparatus"):
            e.verify_manifest(self.m, self.root)

    def test_unknown_gravity_channel_rejected(self):
        self.m["observable"] = "gravitational_metric_directly_observed"
        with self.assertRaisesRegex(ValueError, "unsupported"):
            e.verify_manifest(self.m, self.root)

    def test_nonexistent_source_rejected(self):
        self.m["blocks"][0]["pair"][0]["raw_file"] = "missing.csv"
        with self.assertRaises(FileNotFoundError):
            e.verify_manifest(self.m, self.root)

    def test_outside_root_file_access_rejected(self):
        # The existing relative directory is accessible; the file isn't
        # allowed, regardless of whether the SHA is correct.
        outside = self.root.parent / (self.root.name + ".outside")
        outside.write_bytes(b"outside")
        self.addCleanup(lambda: outside.unlink(missing_ok=True))
        rel = "../" + outside.name
        self.m["blocks"][0]["pair"][0]["raw_file"] = rel
        self.m["blocks"][0]["pair"][0]["raw_sha256"] = sha(b"outside")
        with self.assertRaisesRegex(ValueError, "inside the evidence root"):
            e.verify_manifest(self.m, self.root)

    def test_explicit_data_kind_required(self):
        self.m["data_kind"] = "experimental_gravity_verified"
        with self.assertRaisesRegex(ValueError, "calibrated/replicated"):
            e.verify_manifest(self.m, self.root)

    def test_empty_source_file_rejected(self):
        (self.root / "on.csv").write_bytes(b"")
        self.m["blocks"][0]["pair"][0]["raw_sha256"] = sha(b"")
        with self.assertRaisesRegex(ValueError, "empty evidence"):
            e.verify_manifest(self.m, self.root)

    def test_multiple_blocks_require_distinct_experimental_files(self):
        self.m["blocks"].append(copy.deepcopy(self.m["blocks"][0]))
        self.m["blocks"][1]["block_id"] = "SYNTHETIC/block2"
        with self.assertRaisesRegex(ValueError, "duplicate run"):
            e.verify_manifest(self.m, self.root)


if __name__ == "__main__":
    unittest.main()
