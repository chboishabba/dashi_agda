"""R2P2 x original Base369 wave proof owner: source and synthetic arithmetic audit.

These tests do not replace Agda kernel checks or optical metrology receipts.
"""
from fractions import Fraction
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
WAVE = ROOT / "DASHI/Physics/Closure/R2P2369WaveOpticalCombInformationCutExact.agda"
ARCH = ROOT / "DASHI/Physics/Closure/R2P2369AtomicQuantumDiamondArchitectureExact.agda"
ROOTS = (
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
)


class R2P2369WaveCutTests(unittest.TestCase):
    def test_frequency_comb_above_below_are_distinct(self):
        tooth = 3 * 10 + 2
        beat = 4
        self.assertEqual(tooth, 32)
        self.assertEqual((tooth + beat, tooth - beat), (36, 28))
        self.assertNotEqual(tooth + beat, tooth - beat)

    def test_absolute_beat_observer_collides(self):
        # A constant trit over both branches cannot reconstruct the sign.
        state = (("above", 36), ("below", 28))
        coarse_trit = lambda _: 0
        self.assertEqual(coarse_trit(state[0]), coarse_trit(state[1]))
        self.assertNotEqual(state[0][1], state[1][1])
        # Full-state fibre retains the original branch, without claiming
        # the trit itself is a reversible physical optical phase.
        encoded = [(branch, coarse_trit((branch, hz)), hz) for branch, hz in state]
        self.assertEqual([(branch, hz) for branch, _, hz in encoded], list(state))

    def test_existing_proof_owners_reused_not_forked(self):
        src = WAVE.read_text(encoding="utf-8")
        for owner in (
            "Base369WaveContinuousSymbolicCodingExact",
            "Base369SymmetryWaveRound9Validation",
            "IndexedRelationalHyperfabricSpineExact",
            "IndexedRelationalPadicWaveContinuousAdaptersExact",
            "IntersectionalNonFactorability",
            "ShiftWaveRefinementSeam",
            "WaveAlgorithmLift",
            "Base369PolyphaseKernelBoundary",
            "QuantumClockDimensionlessObservableLaw",
            "R2P2MountainOpticalClockComparisonExact",
        ):
            with self.subTest(owner=owner):
                self.assertIn(owner, src)

    def test_source_new_theorems_and_analytic_nonpromotion(self):
        src = WAVE.read_text(encoding="utf-8")
        for symbol in (
            "beatSignInformationCollision",
            "absoluteBeatTritCannotRecoverOpticalHz",
            "renamingTritCannotRestoreBeatSign",
            "signedBeatEncodeDecode",
            "fullBeatWaveFibreDeterminesOpticalHz",
            "waveEncodedStateIsSufficient",
            "shiftFiniteWaveFineProjectsToCoarse",
            "finiteC3OneStepIsAdditive",
            "clockPhaseIsDimensionless",
            "redshiftIsDimensionless",
            "finiteWaveAlgorithmTritInvolution",
            "waveBridgeDoesNotCalibratePhysicalPhase",
            "waveBridgeDoesNotObserveQuantumGravity",
        ):
            with self.subTest(symbol=symbol):
                self.assertIn(symbol, src)
        self.assertNotIn("postulate", src)
        self.assertNotIn("TERMINATING", src)
        self.assertIn("R2P2369WaveOpticalCombInformationCutExact", ARCH.read_text(encoding="utf-8"))
        for root in ROOTS:
            with self.subTest(root=root):
                root_text = root.read_text(encoding="utf-8")
                self.assertIn(
                    "import DASHI.Physics.Closure.R2P2369WaveOpticalCombInformationCutExact as R2P2Wave",
                    root_text,
                )
                self.assertIn("R2P2WaveSignedBeatRetained", root_text)
                self.assertIn("R2P2WaveNoPhysicalPhasePromotion", root_text)


if __name__ == "__main__":
    unittest.main()
