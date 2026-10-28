"""Three-node optical-clock ratio-loop synthetic integrity regression.

Zero closure tests link consistency only, never curvature or quantum gravity.
"""
from fractions import Fraction
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Physics/Closure/R2P2ThreeClockLoopClosure369Exact.agda"
ARCH = ROOT / "DASHI/Physics/Closure/R2P2369AtomicQuantumDiamondArchitectureExact.agda"
ROOTS = (
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
)


class ThreeClockLoopTests(unittest.TestCase):
    def test_three_exact_frequency_ratios_form_unit_cycle(self):
        a, b, c = Fraction(3), Fraction(6), Fraction(9)
        self.assertEqual((a / b) * (b / c) * (c / a), Fraction(1))
        self.assertEqual(3 * 6 * 9, 6 * 9 * 3)

    def test_corrupt_edge_causes_nonclosure_not_curvature(self):
        a, b, c = Fraction(3), Fraction(6), Fraction(9)
        corrupted_edge = Fraction(10, 3)
        self.assertEqual((a / b) * (b / c) * corrupted_edge, Fraction(10, 9))
        self.assertNotEqual(3 * 6 * 10, 6 * 9 * 3)

    def test_source_and_nonpromotion(self):
        content = MODULE.read_text(encoding="utf-8")
        for symbol in (
            "10.1364/OPTICA.575770",
            "Fortier, Luiten",
            "syntheticCycleCloses",
            "syntheticBadEdgeDoesNotClose",
            "canonicalThreeClockLoopSourceBoundary",
            "r2p2ThirdRealClockProvidedIsFalse",
            "threeClockLoopNullImpliesCurvatureIsFalse",
            "finiteModelIsObservedFrequencyNetworkIsFalse",
        ):
            with self.subTest(symbol=symbol):
                self.assertIn(symbol, content)
        self.assertNotIn("postulate", content)
        self.assertIn("R2P2ThreeClockLoopClosure369Exact", ARCH.read_text(encoding="utf-8"))
        for path in ROOTS:
            with self.subTest(path=str(path)):
                self.assertIn(
                    "import DASHI.Physics.Closure.R2P2ThreeClockLoopClosure369Exact as R2P2Loop",
                    path.read_text(encoding="utf-8"),
                )


if __name__ == "__main__":
    unittest.main()
