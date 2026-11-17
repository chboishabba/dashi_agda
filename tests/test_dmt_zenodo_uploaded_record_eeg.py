"""Exact, synthetic-only schema and MD5 joins for Niedernhuber source metadata."""
import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from scripts.audit_dmt_zenodo_uploaded_record_eeg import (
    read_original_record, compare_transcription, verify_uploaded_subset, audit)


def fixture():
    files = []
    pairs = []
    for n in range(1001, 1026):
        source_pair = []
        for ext in ("set", "fdt"):
            name = f"{n}_equalised.{ext}"
            data = ("synthetic:" + name).encode()
            md5 = hashlib.md5(data).hexdigest()
            files.append({"key": name, "size": len(data), "checksum": "md5:" + md5})
            source_pair.append({"name": name, "md5": md5})
        pairs.append({"file_prefix": str(n), "files": source_pair})
    record = {
        "id": 18850897, "doi": "10.5281/zenodo.18850897",
        "links": {"self": "https://zenodo.org/api/records/18850897"},
        "metadata": {"license": {"id": "cc-by-4.0"}}, "files": files,
    }
    return record, {"file_pairs": pairs}


class UploadedZenodoRootTests(unittest.TestCase):
    def test_full_synthetic_record_joins(self):
        with tempfile.TemporaryDirectory() as d:
            record, manifest = fixture()
            rp = Path(d) / "source.json"
            rp.write_text(json.dumps(record))
            actual, sha = read_original_record(rp)
            self.assertEqual(len(actual), 50)
            self.assertEqual(len(sha), 64)
            self.assertEqual(compare_transcription(actual, manifest), [])

    def test_exact_upload_subset_hash(self):
        with tempfile.TemporaryDirectory() as d:
            record, manifest = fixture()
            rp = Path(d) / "source.json"
            rp.write_text(json.dumps(record))
            sub = Path(d) / "files"
            sub.mkdir()
            (sub / "1001_equalised.fdt.bin").write_bytes(b"synthetic:1001_equalised.fdt")
            actual, _ = read_original_record(rp)
            inspected = verify_uploaded_subset(actual, sub)
            self.assertEqual(len(inspected), 1)
            self.assertEqual(inspected[0]["name"], "1001_equalised.fdt")

    def test_changed_uploaded_byte_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            record, _ = fixture()
            rp = Path(d) / "source.json"
            rp.write_text(json.dumps(record))
            sub = Path(d) / "files"
            sub.mkdir()
            (sub / "1001_equalised.fdt.bin").write_bytes(b"tampered")
            actual, _ = read_original_record(rp)
            with self.assertRaises(ValueError):
                verify_uploaded_subset(actual, sub)

    def test_manifest_digest_typo_detected(self):
        with tempfile.TemporaryDirectory() as d:
            record, manifest = fixture()
            rp = Path(d) / "source.json"
            rp.write_text(json.dumps(record))
            actual, _ = read_original_record(rp)
            manifest["file_pairs"][0]["files"][0]["md5"] = "0" * 32
            self.assertEqual(compare_transcription(actual, manifest),
                             ["1001_equalised.set"])

    def test_wrong_record_version_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            record, _ = fixture()
            record["id"] = 18850896
            rp = Path(d) / "source.json"
            rp.write_text(json.dumps(record))
            with self.assertRaises(ValueError):
                read_original_record(rp)

    def test_rights_source_does_not_silently_change(self):
        with tempfile.TemporaryDirectory() as d:
            record, _ = fixture()
            record["metadata"]["license"]["id"] = "unverified"
            rp = Path(d) / "source.json"
            rp.write_text(json.dumps(record))
            with self.assertRaises(ValueError):
                read_original_record(rp)

    def test_missing_source_pair_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            record, _ = fixture()
            record["files"][-1]["key"] = "1025_equalised.fdt"
            rp = Path(d) / "source.json"
            rp.write_text(json.dumps(record))
            with self.assertRaises(ValueError):
                read_original_record(rp)

    def test_status_ceiling_remains_no_g1(self):
        with tempfile.TemporaryDirectory() as d:
            record, manifest = fixture()
            rp = Path(d) / "source.json"
            mp = Path(d) / "manifest.json"
            rp.write_text(json.dumps(record))
            mp.write_text(json.dumps(manifest))
            response = audit(rp, mp)
            self.assertEqual(response["original_manifest_md5_matches_record"], 50)
            self.assertFalse(response["eeg_signal_or_microstate_results_reproduced"])
            self.assertTrue(response["user_supplied_record_not_authenticated_live_fetch"])


if __name__ == "__main__":
    unittest.main()
