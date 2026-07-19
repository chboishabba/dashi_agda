from __future__ import annotations

import importlib.util
import random
import sys
import tempfile
import unittest
from pathlib import Path

MODULE_PATH = Path(__file__).resolve().parents[1] / "musical_symmetry_basin_diagnostic.py"
SPEC = importlib.util.spec_from_file_location("musical_symmetry_basin_diagnostic", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class MusicalSymmetryDiagnosticTests(unittest.TestCase):
    def test_symmetric_generator_has_zero_reverse_inversion_defect(self) -> None:
        rng = random.Random(7)
        for _ in range(20):
            melody = MODULE.generate_symmetric_melody(8, rng)
            self.assertEqual(MODULE.reverse_inversion_defect(melody), 0)

    def test_generic_generator_excludes_symmetric_class(self) -> None:
        rng = random.Random(11)
        for _ in range(20):
            melody = MODULE.generate_generic_melody(8, rng)
            self.assertGreater(MODULE.reverse_inversion_defect(melody), 0)

    def test_exact_two_bit_witness(self) -> None:
        witness = MODULE.exact_two_bit_witness()
        self.assertEqual(witness["state_count"], 4)
        self.assertEqual(witness["basin_volumes"], {"00": 2, "11": 2})
        self.assertTrue(witness["all_repaired_states_are_symmetric"])
        self.assertTrue(witness["repair_is_idempotent"])

    def test_report_is_fail_closed_for_cognitive_claim(self) -> None:
        report = MODULE.run_experiment(sample_count=100, trials=2, seed=23)
        boundary = report["claim_boundary"]
        self.assertTrue(boundary["algebraic_dynamical_extension_demonstrated"])
        self.assertFalse(boundary["direct_asymmetry_reward_used"])
        self.assertTrue(boundary["compression_prior_assumed"])
        self.assertFalse(boundary["human_perception_data_present"])
        self.assertFalse(boundary["cognitive_explanation_promoted"])

        for summary in report["symmetric_basin_share"].values():
            self.assertGreaterEqual(summary["mean"], 0.0)
            self.assertLessEqual(summary["mean"], 1.0)

    def test_svg_output_is_created(self) -> None:
        report = MODULE.run_experiment(sample_count=50, trials=1, seed=29)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "diagnostic.svg"
            MODULE.write_svg(report, path)
            content = path.read_text(encoding="utf-8")
            self.assertIn("Musical symmetry basin diagnostic", content)
            self.assertIn("no cognitive promotion", content)


if __name__ == "__main__":
    unittest.main()
