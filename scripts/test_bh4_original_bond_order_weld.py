"""Exact negative and positive controls for the 54-bond order weld."""
import unittest
from fractions import Fraction
from check_bh4_original_bond_order_weld import (
    AGDA_EDGES, SOLVER_EDGES, SOLVER_INDEX_OF_AGDA, AGDA_INDEX_OF_SOLVER,
    agda_to_solver_flux, solver_to_agda_flux, divergence, certify_order_weld,
)

class OriginalBondOrderWeldTests(unittest.TestCase):
    def test_bijective_and_nonidentity(self):
        self.assertEqual(len(set(AGDA_EDGES)), 54)
        self.assertEqual(set(AGDA_EDGES), set(SOLVER_EDGES))
        self.assertNotEqual(AGDA_EDGES, SOLVER_EDGES)
        self.assertEqual(sorted(SOLVER_INDEX_OF_AGDA), list(range(54)))
        self.assertEqual(sorted(AGDA_INDEX_OF_SOLVER), list(range(54)))
        self.assertEqual(certify_order_weld()["basis_checks"], 54)

    def test_exact_signed_rational_flux_divergence(self):
        native = [Fraction((i - 23) * 7, i + 4) for i in range(54)]
        solver = agda_to_solver_flux(native)
        self.assertEqual(solver_to_agda_flux(solver), tuple(native))
        self.assertEqual(divergence(AGDA_EDGES, native),
                         divergence(SOLVER_EDGES, solver))
        self.assertEqual(sum(divergence(AGDA_EDGES, native)), 0)

    def test_untranslated_flux_can_change_observations(self):
        native = [0] * 54
        native[1] = 1
        self.assertNotEqual(divergence(AGDA_EDGES, native),
                            divergence(SOLVER_EDGES, native))

    def test_invalid_dimensions_rejected(self):
        with self.assertRaises(ValueError):
            agda_to_solver_flux([0] * 53)
        with self.assertRaises(ValueError):
            solver_to_agda_flux([0] * 55)

if __name__ == "__main__":
    unittest.main()
