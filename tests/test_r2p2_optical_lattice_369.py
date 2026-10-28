"""Three-site optical-lattice operator source/regression checks.

The 3-site adjacency and potential are exact synthetic toy maps only. They
must not be used as a numerical model of AA localization or R2P2 Yb data.
"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Physics/Closure/R2P2OpticalLattice369HamiltonianCutExact.agda"
ARCH = ROOT / "DASHI/Physics/Closure/R2P2369AtomicQuantumDiamondArchitectureExact.agda"
ROOTS = [
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
]


def hop(v):
    x, y, z = v
    return (y, x + z, y)


def potential(v):
    x, y, z = v
    return (0, y, 2*z)


class OpticalLattice369Tests(unittest.TestCase):
    def test_exact_noncommutation_is_not_zero(self):
        left = (1, 0, 0)
        self.assertEqual(hop(left), (0, 1, 0))
        self.assertEqual(potential(left), (0, 0, 0))
        self.assertEqual(hop(potential(left)), (0, 0, 0))
        self.assertEqual(potential(hop(left)), (0, 1, 0))
        self.assertNotEqual(hop(potential(left)), potential(hop(left)))

    def test_three_site_operator_is_not_a_fitted_aa_hamiltonian(self):
        content = MODULE.read_text(encoding="utf-8")
        for owner in (
            "AtomicPeriodicTable369GenerativeExact",
            "WolfPrize2026UltracoldControlBridge",
            "BothwellYe2022MillimetreRedshiftReceipt",
            "R2P2MountainOpticalClockComparisonExact",
            "R2P2369WaveOpticalCombInformationCutExact",
        ):
            with self.subTest(owner=owner):
                self.assertIn(owner, content)
        for symbol in (
            "finiteLatticeOperatorsFailToCommute",
            "strontium87Neutral",
            "maIsNotTheR2P2Clock",
            "yeIsNotTheMaClock",
            "latticeCannotProveInfiniteAAThreshold",
            "latticeDoesNotConflateClockExperiments",
            "latticeDoesNotObserveQuantumGravity",
            "finiteP3ProvesInfiniteAAThresholdIsFalse",
            "maPublishedCoherenceDataIngestedIsFalse",
            "actualR2P2TrapDepthMeasuredHereIsFalse",
        ):
            with self.subTest(symbol=symbol):
                self.assertIn(symbol, content)
        self.assertNotIn("postulate", content)
        self.assertNotIn("{!!}", content)

    def test_toe_roots_and_architecture_import_same_owner(self):
        module_path = "import DASHI.Physics.Closure.R2P2OpticalLattice369HamiltonianCutExact as "
        self.assertIn(module_path + "Lattice", ARCH.read_text(encoding="utf-8"))
        self.assertIn("fullArchitectureLatticeIsNotInfiniteAAProof", ARCH.read_text(encoding="utf-8"))
        for path in ROOTS:
            content = path.read_text(encoding="utf-8")
            with self.subTest(root=str(path)):
                self.assertIn(module_path + "R2P2Lattice", content)
                self.assertIn("R2P2FiniteLatticeNoncommuting", content)
                self.assertIn("R2P2NoInfiniteAAFromFinite3", content)


if __name__ == "__main__":
    unittest.main()
