"""Source and exact-arithmetic regression for the R2P2 attributed adapter.

This is NOT an Agda kernel check, an experiment replay, or GR validation.
"""
from fractions import Fraction
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Physics/Closure/R2P2MountainOpticalClockComparisonExact.agda"
DOC = ROOT / "Docs/papers/R2P2MountainOpticalClockComparison.md"
ROOTS = (
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
)
IMPORT = "import DASHI.Physics.Closure.R2P2MountainOpticalClockComparisonExact"


class TestR2P2MountainOpticalClock(unittest.TestCase):
    def test_video_rate_exact_conversion_not_observation(self):
        fractional_rate = Fraction(2885, 10**16)
        daily_seconds = fractional_rate * 86400
        self.assertEqual(daily_seconds, Fraction(249264000, 10**16))
        self.assertEqual(daily_seconds * 10**9, Fraction(249264, 10000))

    def test_both_comb_beat_orientations(self):
        mode, rep, offset, beat = 3, 10, 2, 4
        tooth = mode * rep + offset
        self.assertEqual(tooth, 32)
        self.assertEqual(tooth + beat, 36)
        self.assertEqual(28 + beat, tooth)

    def test_source_and_promotion_boundaries(self):
        module = MODULE.read_text(encoding="utf-8")
        doc = DOC.read_text(encoding="utf-8")
        for string in (
            "QuantumClockProperTimeRedshiftBridge",
            "QuantumClockEmpiricalRedshiftReceiptRequest",
            "canonicalR2P2PrimarySource",
            "carrierEnvelopeOffsetHz",
            "exampleAboveCombTooth",
            "exampleBelowCombTooth",
            "transcriptDailyGainExact",
            "r2p2HasNoClaimedQGDiscovery",
            "r2p2HasNoAcceptedClockRatio",
            "transcriptNumericsPromotedToRawDataIsFalse",
            "2026-06-03",
        ):
            self.assertIn(string, module)
        self.assertIn("https://meetings-archive.aps.org/damop/2026/g07/7/", module)
        self.assertIn("24.9264 nanoseconds/day", doc)
        self.assertIn("not been checked by the Agda kernel", doc)

    def test_toe_roots_reach_adapter(self):
        for root in ROOTS:
            with self.subTest(root=root):
                self.assertIn(IMPORT, root.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
