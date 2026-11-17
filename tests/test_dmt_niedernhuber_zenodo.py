"""Zenodo source audit contracts: synthetic fixtures only, no EEG data accessed."""
import copy
import hashlib
import tempfile
import unittest
from pathlib import Path

from scripts.audit_dmt_niedernhuber_zenodo import (
    audit, git_blob_sha, load_source, validate_rights_review, validate_source,
    verify_local_file_hashes, EXPECTED_MANIFEST_GIT_BLOB, MANIFEST)


def review():
    return {
        "schema": "dashi-niedernhuber-human-data-review-v1",
        "version_doi": "10.5281/zenodo.18850897",
        "reviewer_reference": "SYNTHETIC TEST reviewer only",
        "rights_basis_reference": "SYNTHETIC TEST rights",
        "human_data_approval_reference": "SYNTHETIC TEST ethics",
        "local_integrity_processing_allowed": True}


class TestNiedernhuberZenodo(unittest.TestCase):
    def setUp(self):
        self.source = load_source()

    def assert_bad(self, edit):
        source = copy.deepcopy(self.source)
        edit(source)
        with self.assertRaises(ValueError):
            validate_source(source)

    def test_pinned_git_object(self):
        self.assertEqual(git_blob_sha(MANIFEST.read_bytes()), EXPECTED_MANIFEST_GIT_BLOB)

    def test_manifest_admission(self):
        files = validate_source(self.source)
        self.assertEqual(len(files), 50)
        self.assertEqual(len(self.source["file_pairs"]), 25)
        self.assertIn("1028_equalised.fdt", files)
        self.assertRegex(files["1028_equalised.fdt"], r"^[0-9a-f]{32}$")
        self.assertFalse(self.source["consumer_ceiling"]["authoritative_zenodo_md5_listing_verified"])

    def test_listing_is_not_participant_or_condition_replay(self):
        result = audit(self.source)
        self.assertEqual(result["hash_matched_local_files"], 0)
        self.assertTrue(result["original_author_code_declares_prefixes_as_participant_ids"])
        self.assertFalse(result["participant_and_condition_mapping_independently_replayed"])
        self.assertFalse(result["published_microstate_statistic_reproduced"])

    def test_primary_doi_mismatch(self):
        self.assert_bad(lambda s: s["source_root"].update(paper_doi="10.0/not-original"))

    def test_version_doi_mismatch(self):
        self.assert_bad(lambda s: s["deposition"].update(version_doi="10.5281/zenodo.18850896"))

    def test_cannot_promote_license(self):
        self.assert_bad(lambda s: s["deposition"].update(license_status="cc-by-4.0"))

    def test_cannot_promote_participants(self):
        self.assert_bad(lambda s: s["consumer_ceiling"].update(original_transition_reproduced=True))

    def test_author_original_source_code_identity(self):
        self.assertEqual(self.source["original_analysis_code"]["commit"],
                         "c5c064d109563e97127403a8fbb340009ba1e88b")
        self.assertTrue(self.source["consumer_ceiling"]["source_code_g1_export_identified"])

    def test_different_source_author_participant_list(self):
        self.assert_bad(lambda s: s["file_pairs"][0].update(file_prefix="9999"))

    def test_missing_original_matlab_blob(self):
        self.assert_bad(lambda s: s["original_analysis_code"]["source_files"][0].update(
            git_blob_sha1="0" * 40))

    def test_duplicate_file(self):
        def edit(s):
            s["file_pairs"][1]["files"] = copy.deepcopy(s["file_pairs"][0]["files"])
        self.assert_bad(edit)

    def test_partial_pair(self):
        self.assert_bad(lambda s: s["file_pairs"][0]["files"].pop())

    def test_nonhex_digest(self):
        self.assert_bad(lambda s: s["file_pairs"][0]["files"][0].update(md5="ZZ"))

    def test_rights_required_before_bytes(self):
        with self.assertRaises(ValueError):
            audit(self.source, "/tmp/not_a_dataset")

    def test_review_wrong_version(self):
        r = review(); r["version_doi"] = "10.0/incorrect"
        with self.assertRaises(ValueError):
            validate_rights_review(r, self.source)

    def test_review_missing_scope(self):
        r = review(); r["local_integrity_processing_allowed"] = False
        with self.assertRaises(ValueError):
            validate_rights_review(r, self.source)

    def test_receipt_alone_not_dataset(self):
        with self.assertRaises(ValueError):
            audit(self.source, rights_receipt=review())

    def test_synthetic_tiny_file_hashes(self):
        with tempfile.TemporaryDirectory() as d:
            mock = copy.deepcopy(self.source)
            for pair in mock["file_pairs"]:
                for entry in pair["files"]:
                    data = ("synthetic:" + entry["name"]).encode()
                    (Path(d) / entry["name"]).write_bytes(data)
                    entry["md5"] = hashlib.md5(data).hexdigest()
            with self.assertRaisesRegex(ValueError, "not authenticated"):
                audit(mock, d, review())
            self.assertEqual(verify_local_file_hashes(d, validate_source(mock)), 50)

    def test_unverified_digest_promotion_rejected(self):
        self.assert_bad(lambda s: s["consumer_ceiling"].update(authoritative_zenodo_md5_listing_verified=True))

    def test_synthetic_hash_mismatch(self):
        with tempfile.TemporaryDirectory() as d:
            mock = copy.deepcopy(self.source)
            for pair in mock["file_pairs"]:
                for entry in pair["files"]:
                    data = entry["name"].encode()
                    (Path(d) / entry["name"]).write_bytes(data)
                    entry["md5"] = hashlib.md5(data).hexdigest()
            (Path(d) / "1001_equalised.fdt").write_bytes(b"changed")
            with self.assertRaises(ValueError):
                verify_local_file_hashes(d, validate_source(mock))

    def test_missing_file_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(ValueError):
                verify_local_file_hashes(d, validate_source(self.source))


if __name__ == "__main__":
    unittest.main()
