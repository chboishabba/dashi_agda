"""Quadratic Fourier index Pareto tests, *not* FFT or physical NS proof."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from r2p2_27x27_four_grid_pareto_diagnostic import (  # noqa: E402
    audit, check_finite_index_pareto, cyclotomic_bilinear_audit, fold,
)

AGDA = [
    ROOT / "DASHI/Physics/Closure/R2P227729FourGridRetainedQuadraticParetoExact.agda",
    ROOT / "DASHI/Physics/Closure/R2P227729BilinearCyclotomicPadCutExact.agda",
]
ROOTS = [
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
]


class FourGridParetoTests(unittest.TestCase):
    def test_independent_signed_rational_profiles(self):
        result = check_finite_index_pareto()
        self.assertEqual(len(result), 6)
        self.assertTrue(all(r["four_retained_matches_exact"] for r in result))
        self.assertTrue(all(r["five_full_matches_exact"] for r in result))
        self.assertFalse(result[3]["three_retained_matches_exact"])

    def test_original_cyclotomic_field_bilinear(self):
        result = cyclotomic_bilinear_audit()
        self.assertEqual(result["number_of_input_mode_pairs"], 729)
        self.assertEqual(result["four_grid_retained_modes_checked"], 27)
        self.assertEqual(result["five_grid_full_modes_checked"], 125)
        self.assertTrue(result["two_independent_complex_like_inputs"])

    def test_four_grid_not_full_output_injection(self):
        self.assertEqual(fold(-2, 4), fold(2, 4))
        self.assertNotEqual(fold(-2, 5), fold(2, 5))
        self.assertEqual(fold(2, 3), -1)
        summary = audit()
        self.assertEqual(
            [summary[k] for k in ("three_grid_capacity", "four_grid_capacity", "five_grid_capacity")],
            [27, 64, 125])
        self.assertTrue(summary["four_grid_retained_exact"])
        self.assertFalse(summary["four_grid_full_output_injective"])
        self.assertFalse(summary["full_four_or_five_grid_DFT_proved"])
        self.assertFalse(summary["navier_stokes_regular_or_r2p2_empirical"])
        self.assertFalse(summary["monster_same_object_representation"])

    def test_source_written_theorem_surfaces(self):
        four = AGDA[0].read_text(encoding="utf-8")
        bilinear = AGDA[1].read_text(encoding="utf-8")
        for token in (
            "fourGridRetainedMembership",
            "fourGridRetainedCubeMembership",
            "fourGridMatchesExactRetainedForAllCoefficients",
            "outerFrequencyCollisionAtFour",
            "threeGridFalseRetainedNegativeFrequency",
            "fourGridSampleCount",
            "fiveGridSampleCount",
        ):
            self.assertIn(token, four)
        for token in (
            "sumUsingCong",
            "fourGridBilinearRecoversAllRetainedCoefficients",
            "fiveGridBilinearRecoversAllFullCoefficients",
            "cyclotomicFourGridRetainedBilinearExact",
            "cyclotomicFiveGridFullBilinearExact",
            "C3CubeCyclotomicFourierExact",
        ):
            self.assertIn(token, bilinear)
        for source in (four, bilinear):
            self.assertNotIn("{!!}", source)
            self.assertNotIn("postulate\n", source)
            self.assertNotIn("{-# TERMINATING #-}", source)

    def test_toe_owner_linkage(self):
        for p in ROOTS:
            src = p.read_text(encoding="utf-8")
            self.assertIn("R2P227729FourGridRetainedQuadraticParetoExact", src)
            self.assertIn("R2P227729BilinearCyclotomicPadCutExact", src)
            self.assertIn("FourGridBilinearRetained", src)
            self.assertIn("FiveGridBilinearFull", src)


if __name__ == "__main__":
    unittest.main()
