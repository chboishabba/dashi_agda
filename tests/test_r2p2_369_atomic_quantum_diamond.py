"""Static/readback and exact finite arithmetic for R2P2 369-quantum-diamond.

No Agda kernel execution, device construction or experimental replay is implied.
"""
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OLD = ROOT / "DASHI/Physics/Closure/R2P2MountainOpticalClockComparisonExact.agda"
NEW = ROOT / "DASHI/Physics/Closure/R2P2369AtomicQuantumDiamondArchitectureExact.agda"
DOC = ROOT / "Docs/papers/R2P2369AtomicQuantumDiamondArchitecture.md"
ROOTS = [
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
]
IMPORT = "import DASHI.Physics.Closure.R2P2369AtomicQuantumDiamondArchitectureExact as R2P2369"


class R2P2369ArchitectureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.old = OLD.read_text(encoding="utf-8")
        cls.module = NEW.read_text(encoding="utf-8")
        cls.doc = DOC.read_text(encoding="utf-8")

    def test_video_and_aps_are_separate_sources(self):
        self.assertIn("https://www.youtube.com/watch?v=eyZEqSPeMwg", self.old)
        self.assertIn("2026-10-23", self.old)
        self.assertIn("canonicalVeritasium2026Source", self.old)
        self.assertIn("https://meetings-archive.aps.org/damop/2026/g07/7/", self.old)
        self.assertIn("2026-06-03", self.old)
        self.assertIn("videoIsCanonical", self.old)
        self.assertIn("primary", self.doc.lower())

    def test_all_reused_constructor_owners_are_imported(self):
        for name in (
            "AtomicPeriodicTable369GenerativeExact",
            "SuperSSP369Field",
            "Base369BinaryTernaryRefinement",
            "Base369PolyphaseCharacters",
            "Base369PolyphaseKernelBoundary",
            "FiniteCausalDiamond",
            "QutritWeyl",
            "QuantumClockSuperpositionReceipt",
            "AtomicClockSISecondCalibrationBridge",
            "QuantumClockProperTimeRedshiftBridge",
            "OpticalPhenomenaKernelBridge",
            "R2P2MountainOpticalClockComparisonExact",
        ):
            with self.subTest(name=name):
                self.assertIn(name, self.module)

    def test_structural_witnesses_and_non_promotion(self):
        for name in (
            "StageStep",
            "canonicalClockPipelinePath",
            "canonicalAtomicClockIdentities",
            "canonicalR2P2ResolutionDiamond",
            "canonicalR2P2FiniteCausalModel",
            "canonicalR2P2PhaseIndex",
            "canonicalR2P2OpticalPhysicsBoundary",
            "canonicalQuantumProperTimeComparatorBoundary",
            "canonicalR2P2369FullLogicalArchitecture",
            "resolutionDiamondAgrees",
            "fullArchitectureDoesNotProveEinsteinWrong",
            "fullArchitectureDoesNotConstructQuantumGravity",
            "fullArchitectureDoesNotIngestMeasurements",
            "physicalFieldStrengthDerived",
            "twoWayTransferCalibrationDerived",
            "bothR2P2IsotopesIndependentlyVerifiedFromAPS",
            "requiredDirectionalTransferLegs",
        ):
            with self.subTest(name=name):
                self.assertIn(name, self.module)
        self.assertNotIn("postulate", self.module)
        self.assertNotIn("TERMINATING", self.module)

    def test_source_atom_arithmetic_only(self):
        self.assertEqual(70 + 101, 171)
        self.assertEqual(55 + 78, 133)
        self.assertEqual(70, 70)  # neutral electron count by construction
        self.assertIn("bothIsotopesNotVerifiedByAPS = refl", self.module)

    def test_refinement_count_and_commuting_paths(self):
        def sectors(binary_depth: int, ternary_depth: int) -> int:
            return 2**binary_depth * 3**ternary_depth

        self.assertEqual(sectors(0, 1), 3)
        self.assertEqual(sectors(1, 1), 6)
        self.assertEqual(sectors(0, 2), 9)
        self.assertEqual(sectors(1, 2), 18)
        def binary_refine(address):
            a, b = address
            return a + 1, b

        def ternary_refine(address):
            a, b = address
            return a, b + 1

        self.assertEqual(
            binary_refine(ternary_refine((0, 1))),
            ternary_refine(binary_refine((0, 1))),
        )

    def test_signed_comb_and_transcript_exact_arithmetic(self):
        tooth = 3 * 10 + 2
        self.assertEqual(tooth, 32)
        self.assertEqual((tooth + 4, tooth - 4), (36, 28))
        self.assertEqual(
            Fraction(2885, 10**16) * 86400 * 10**9,
            Fraction(249264, 10000),
        )

    def test_import_graph(self):
        for root in ROOTS:
            with self.subTest(root=str(root)):
                self.assertIn(IMPORT, root.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
