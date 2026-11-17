"""R2P2 finite model-identifiability regression; synthetic-only.

Checks source presence and exact finite arithmetic. This is not an Agda kernel
run or validation of a real quantum-gravity/metric comparison.
"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Physics/Closure/R2P2ClockBiasIdentifiabilityMaxCutExact.agda"
ARCH = ROOT / "DASHI/Physics/Closure/R2P2369AtomicQuantumDiamondArchitectureExact.agda"
ROOTS = (
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
)


class TestR2P2BiasIdentifiability(unittest.TestCase):
    def test_one_height_is_not_identifiable(self):
        first = 6 + 1 * 3
        second = 3 + 2 * 3
        self.assertEqual(first, second)
        self.assertEqual(first, 9)

    def test_second_height_can_separate_selected_pair(self):
        first = 6 + 1 * 9
        second = 3 + 2 * 9
        self.assertEqual((first, second), (15, 21))
        self.assertNotEqual(first, second)

    def test_requires_shared_bias_and_external_data(self):
        contents = MODULE.read_text(encoding="utf-8")
        for symbol in (
            "sameRefinementIndexDoesNotRemoveBias",
            "oneHeightCannotDiscriminate",
            "secondHeightDiscriminatesTheseCandidates",
            "canonicalR2P2BiasIdentifiabilityMaxCut",
            "stableBiasAcrossRealApparatusEstablishedIsFalse",
            "realMultiHeightR2P2DataIngestedIsFalse",
            "physicalQuantumGravityIdentifiedIsFalse",
        ):
            with self.subTest(symbol=symbol):
                self.assertIn(symbol, contents)
        self.assertNotIn("postulate", contents)
        self.assertIn("R2P2ClockBiasIdentifiabilityMaxCutExact", ARCH.read_text(encoding="utf-8"))
        for p in ROOTS:
            with self.subTest(root=str(p)):
                self.assertIn(
                    "import DASHI.Physics.Closure.R2P2ClockBiasIdentifiabilityMaxCutExact as R2P2Bias",
                    p.read_text(encoding="utf-8"),
                )


if __name__ == "__main__":
    unittest.main()
