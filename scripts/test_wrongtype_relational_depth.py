"""Executable finite-depth property regressions for the grid/hypervoxel lane."""
from itertools import product
import unittest
from scripts.wrongtype_relational_depth import (
    cube, minimum_width, collision_for_axes
)


class DepthTests(unittest.TestCase):
    def test_grid_query_uses_two_axes(self):
        states = list(cube(4))
        result = minimum_width(states, lambda s: s[:2])
        self.assertEqual(result.width, 2)
        self.assertEqual(result.sufficient_sets, ((0, 1),))

    def test_identity_requires_all_four(self):
        states = list(cube(4))
        result = minimum_width(states, lambda s: s)
        self.assertEqual(result.width, 4)
        self.assertEqual(result.sufficient_sets, ((0, 1, 2, 3),))
        self.assertEqual(len(result.failing), 15)

    def test_last_only_requires_one(self):
        states = list(cube(4))
        result = minimum_width(states, lambda s: s[-1])
        self.assertEqual(result.width, 1)
        self.assertEqual(result.sufficient_sets, ((3,),))

    def test_nonfactorability_witness_is_a_real_collision(self):
        states = list(cube(4))
        answers = [s for s in states]
        witness = collision_for_axes(states, answers, (0, 1, 2))
        self.assertIsNotNone(witness)
        self.assertEqual(witness.left[:3], witness.right[:3])
        self.assertNotEqual(witness.left_answer, witness.right_answer)

    def test_parity_really_needs_every_coordinate(self):
        states = list(cube(5))
        result = minimum_width(states, lambda s: sum(x == "P" for x in s) % 2)
        self.assertEqual(result.width, 5)

    def test_empty_axes_allowed_for_constant_query(self):
        result = minimum_width(list(cube(3)), lambda s: "constant")
        self.assertEqual(result.width, 0)


if __name__ == "__main__":
    unittest.main()
