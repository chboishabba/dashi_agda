"""Synthetic-only archive admission regressions; no human TET rows bundled."""
import hashlib
import tempfile
import unittest
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED

from scripts.extract_dmt_tet_source_subset import prepare, members, checksum


def case(folder, names=None):
    original = Path(folder) / "original.zip"
    with ZipFile(original, "w", compression=ZIP_DEFLATED) as z:
        for name, data in (names or {"data/original/reports/resampled/s01_DMT_Session1_DMT.mat": b"synthetic-mat",
                                    "data/original/physiology/raw.edf": b"synthetic-phys"}).items():
            z.writestr(name, data)
    sha = hashlib.sha256(original.read_bytes()).hexdigest()
    sums = Path(folder) / "sha256sums.txt"
    sums.write_text(f"{sha} *original.zip\n" + "0"*64 + " *derivatives.zip\n")
    return original, sums


class TestSourceSubset(unittest.TestCase):
    def test_exact_sha256_and_one_mat_source(self):
        with tempfile.TemporaryDirectory() as d:
            src, sums = case(d)
            out = prepare(src, sums)
            self.assertTrue(out["original_full_zip_sha256_verified"])
            self.assertEqual(out["source_mat_files"], 1)
            self.assertEqual(out["subset_uncompressed_bytes"], len(b"synthetic-mat"))

    def test_opt_in_archive_emits_only_mat(self):
        with tempfile.TemporaryDirectory() as d:
            src, sums = case(d)
            output = Path(d)/"tet-only.zip"
            report = prepare(src, sums, output)
            self.assertEqual(report["output_zip_sha256"], checksum(output))
            with ZipFile(output) as z:
                self.assertEqual(z.namelist(), ["data/original/reports/resampled/s01_DMT_Session1_DMT.mat"])
                self.assertEqual(z.read(z.namelist()[0]), b"synthetic-mat")

    def test_wrong_source_hash_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            src, sums = case(d)
            sums.write_text("0"*64 + " *original.zip\n")
            with self.assertRaises(ValueError):
                prepare(src, sums)

    def test_absent_tet_fails_closed(self):
        with tempfile.TemporaryDirectory() as d:
            src, sums = case(d, {"data/original/raw/random.edf": b"not-tet"})
            with self.assertRaises(ValueError):
                prepare(src, sums)

    def test_path_traversal_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            src, sums = case(d, {"../data/original/reports/resampled/s01.mat": b"bad"})
            with self.assertRaises(ValueError):
                prepare(src, sums)

    def test_duplicate_tet_names_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            src, sums = case(d)
            with ZipFile(src, "a") as z:
                z.writestr("data/original/reports/resampled/s01_DMT_Session1_DMT.mat", b"duplicate")
            sums.write_text(hashlib.sha256(src.read_bytes()).hexdigest() + " *original.zip\n")
            with self.assertRaises(ValueError):
                prepare(src, sums)

    def test_no_implicit_overwrite(self):
        with tempfile.TemporaryDirectory() as d:
            src, sums = case(d)
            dst = Path(d)/"no-overwrite.zip"
            dst.write_bytes(b"existing")
            with self.assertRaises(ValueError):
                prepare(src, sums, dst)


if __name__ == "__main__":
    unittest.main()
