#!/usr/bin/env python3
"""Synthetic unit tests for MIRACLE intake; NOT measured acoustic validation."""
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check_goodman_measured_acoustics_manifest as gate


class IntakeTest(unittest.TestCase):
    def archives(self, root):
        scenarios = []
        for name in sorted(gate.SCENARIOS):
            data = ("synthetic-negative-test-" + name).encode()
            (root / (name + ".h5")).write_bytes(data)
            scenarios.append({"id": name, "sha256": hashlib.sha256(data).hexdigest()})
        return {"dataset_doi": gate.LATEST_DOI,
                "license": "CC BY-NC-SA 4.0", "scenarios": scenarios}

    def test_manifest_requires_current_version_and_real_digest(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            manifest = self.archives(root)
            self.assertTrue(gate.validate_manifest(manifest, root))
            manifest["dataset_doi"] = "10.14279/depositonce-20106"
            with self.assertRaises(ValueError):
                gate.validate_manifest(manifest, root)
            manifest["dataset_doi"] = gate.LATEST_DOI
            (root / "A1.h5").write_bytes(b"modified")
            with self.assertRaises(ValueError):
                gate.validate_manifest(manifest, root)

    def test_duplicate_scenario_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            manifest = self.archives(root)
            manifest["scenarios"].append(manifest["scenarios"][0])
            with self.assertRaises(ValueError):
                gate.validate_manifest(manifest, root)

    def test_position_group_never_crosses_blocks(self):
        rows = [
            {"scenario": "A1", "position_id": "p", "spatial_block": "left"},
            {"scenario": "A1", "position_id": "p", "spatial_block": "right"},
        ]
        with self.assertRaises(ValueError):
            gate.split_blocks(rows, "fixed-seed")

    def test_separation_gate_rejects_leakage(self):
        rows = [
            {"scenario": "A1", "position_id": "p0",
             "spatial_block": "b0", "xyz_m": [0.0, 0.0, 0.0]},
            {"scenario": "A1", "position_id": "p1",
             "spatial_block": "b1", "xyz_m": [0.01, 0.0, 0.0]},
        ]
        assignments = [
            {"scenario": "A1", "spatial_block": "b0", "partition": "train"},
            {"scenario": "A1", "spatial_block": "b1", "partition": "test"},
        ]
        with self.assertRaises(ValueError):
            gate.enforce_spatial_buffer(rows, assignments, 0.05)
        gate.enforce_spatial_buffer(rows, assignments, 0.005)

    def test_source_identities_and_position_manifest_provenance(self):
        # A valid archive manifest is not sufficient: a partial or
        # duplicated position table is not a held-out benchmark.
        from collections import Counter
        expected = {"A1": 4096, "A2": 4096, "D1": 1089, "R2": 4096}
        good = [(sc, str(i)) for sc, n in expected.items() for i in range(n)]
        self.assertEqual(len(good), 13377)
        self.assertEqual(dict(Counter(sc for sc, _ in good)), expected)
        duplicated = good + [good[0]]
        self.assertEqual(len(set(duplicated)), 13377)
        self.assertNotEqual(len(duplicated), len(set(duplicated)))
        self.assertNotEqual(len(set(good[:-1])), 13377)

    def test_paired_correlation_is_not_discarded(self):
        pairs = [(0.0, 0.0), (1.0, 1.0), (2.0, 2.0)]
        got = gate.correlated_error_budget(pairs, 3)
        self.assertAlmostEqual(got["cov_recovered"][1][1], 0)
        self.assertAlmostEqual(got["cov_recovered"][0][0], 1)
        self.assertEqual(got["n_independent_units"], 3)
        with self.assertRaises(ValueError):
            gate.correlated_error_budget([(0.0, 1.0)], 3)


if __name__ == "__main__":
    unittest.main()
