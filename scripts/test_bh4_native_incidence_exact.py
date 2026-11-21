"""Exact-arithmetic tests for P0.03 native-incidence certificate.

Tests use deliberately synthetic values and cannot certify source physics.
"""
import unittest
from fractions import Fraction
from check_bh4_native_incidence_exact import (
    EDGES, POINTS, incidence_columns, verify_native_incidence,
    total_species_change, signed_charge_change,
    stoichiometric_charge_defects, charge_balance_receipt,
)


class NativeIncidenceExactTests(unittest.TestCase):
    def test_369_native_geometry(self):
        self.assertEqual((len(POINTS), len(EDGES)), (27, 54))
        self.assertTrue(verify_native_incidence())
        self.assertEqual(len(set(EDGES)), 54)
        self.assertTrue(all(sum(c) == 0 for c in incidence_columns()))

    def test_arbitrary_signed_rational_bond_flows_cancel(self):
        currents = [
            [Fraction((e + 1) * (s - 4), e + s + 1)
             for s in range(29)]
            for e in range(54)
        ]
        self.assertEqual(total_species_change(currents), (0,) * 29)
        self.assertEqual(
            signed_charge_change(currents, list(range(-14, 15))), 0
        )

    def test_nonzero_boundary_current_remains_visible(self):
        flows = [[0, 0, 0] for _ in range(54)]
        boundary = [[0, 0, 0] for _ in range(27)]
        boundary[0] = [Fraction(2, 3), Fraction(1, 3), 0]
        receipt = charge_balance_receipt(
            flows, [1, -1, 0], [[1, 1, 0]], [[0, 0, 1]],
            [[0] for _ in range(27)], boundary
        )
        self.assertEqual(receipt["internal"], 0)
        self.assertEqual(receipt["reaction"], 0)
        self.assertEqual(receipt["boundary"], Fraction(1, 3))
        self.assertEqual(receipt["total"], Fraction(1, 3))

    def test_charged_reaction_does_not_disappear(self):
        defects = stoichiometric_charge_defects(
            [[1, 0]], [[0, 1]], [1, 0]
        )
        self.assertEqual(defects, (-1,))
        receipt = charge_balance_receipt(
            [[0, 0] for _ in range(54)], [1, 0],
            [[1, 0]], [[0, 1]], [[2] for _ in range(27)]
        )
        self.assertEqual(receipt["reaction"], -54)
        self.assertEqual(receipt["total"], -54)

    def test_wrong_dimensions_fail_closed(self):
        with self.assertRaises(ValueError):
            total_species_change([[0]] * 53)
        with self.assertRaises(ValueError):
            stoichiometric_charge_defects([[1]], [[1, 0]], [1])
        with self.assertRaises(ValueError):
            charge_balance_receipt(
                [[0] for _ in range(54)], [1],
                [], [], [[0]] * 26
            )


if __name__ == "__main__":
    unittest.main()
