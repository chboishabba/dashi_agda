"""Three-site optical-lattice operator source/regression checks.

The 3-site adjacency and potential are exact synthetic toy maps only. They
must not be used as a numerical model of AA localization or R2P2 Yb data.
"""
from pathlib import Path
import unittest
from fractions import Fraction
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from r2p2_optical_lattice_3site_diagnostic import (  # noqa: E402
    analyze, make_matrix, characteristic_coefficients, expected_coefficients,
    polynomial_eval, nominal_supercell_pareto,
)
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

    def test_signed_hamiltonian_characteristic_polynomial_exact(self):
        for hopping, gradient in ((1, 2), (1, 0), (0, 2), (3, 6), (2, 9), (-2, -3)):
            with self.subTest(hopping=hopping, gradient=gradient):
                J, D = Fraction(hopping), Fraction(gradient)
                matrix = make_matrix(J, D)
                coefficients = characteristic_coefficients(matrix)
                self.assertEqual(coefficients, expected_coefficients(J, D))
                self.assertEqual(polynomial_eval(coefficients, D), 0)
                result = analyze(J, D)
                self.assertFalse(result["experimental_aubry_andre_transition_proven"])
                self.assertFalse(result["quasiperiodicity_constructed"])
                self.assertFalse(result["r2p2_yb_clock_observed"])

    def test_exact_cubic_example_at_j1_d2(self):
        self.assertEqual(characteristic_coefficients(make_matrix(Fraction(1), Fraction(2))),
                         (Fraction(1), Fraction(-6), Fraction(6), Fraction(4)))
        self.assertEqual(polynomial_eval((Fraction(1), Fraction(-6), Fraction(6), Fraction(4)), 2), 0)

    def test_ma_source_supercell_five_rational_approximants(self):
        rows = nominal_supercell_pareto()["rows"]
        self.assertEqual([(x["periods_497"], x["periods_813"]) for x in rows],
                         [(18, 11), (85, 52), (139, 85), (175, 107), (265, 162)])
        self.assertEqual([x["nominal_mismatch_nm"] for x in rows],
                         [3, 31, 22, 16, 1])
        self.assertEqual(rows[0]["relative_nominal_mismatch"], str(Fraction(1, 2981)))
        self.assertEqual(rows[4]["relative_nominal_mismatch"], str(Fraction(1, 131706)))

    def test_nominal_497_813_pareto_does_not_claim_physical_optimality(self):
        result = nominal_supercell_pareto()
        self.assertTrue(result["nominal_wavelengths_not_actual_magic_calibrations"])
        self.assertTrue(result["finite_rational_approximants_do_not_prove_irrational_AA_transition"])
        rows = result["rows"]
        self.assertEqual(
            [r["dominated_in_declared_nominal_2d_cut"] for r in rows],
            [False, True, False, False, False],
        )

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
            "maFirstNominalSupercellOffset",
            "maFifthNominalSupercellOffset",
            "maSupercell18IsNotAnIdentifiedC18PhysicsRealization",
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
                self.assertIn("MaSupercell18NotPhysicalC18", content)


if __name__ == "__main__":
    unittest.main()
