"""Finite tests of generic observers and sampled p-adic/wave/stream interfaces."""
from itertools import product
import unittest

from scripts.indexed_relational_observer_search import (
    finite_product, minimum_coordinate_width, minimum_observers,
    coordinate_observers, first_collision,
)


class GenericObserverSearchTests(unittest.TestCase):
    def test_heterogeneous_product(self):
        states = list(finite_product([("care","transaction","power"), ("no","yes")]))
        self.assertEqual(len(states), 6)
        answer = minimum_coordinate_width(states, lambda x: x)
        self.assertEqual(answer.width, 2)

    def test_ternary_grid_query(self):
        states = list(product("CTP", repeat=4))
        result = minimum_coordinate_width(states, lambda s: s[:2])
        self.assertEqual(result.width, 2)
        self.assertEqual(result.sufficient_observers, (("axis:0", "axis:1"),))

    def test_full_four_takes_four(self):
        states = list(product("CTP", repeat=4))
        result = minimum_coordinate_width(states, lambda s: s)
        self.assertEqual(result.width, 4)
        self.assertEqual(len(result.rejected), 15)

    def test_padic_prefix_observer(self):
        # Finite prefixes of an infinite 3-adic stream; this is EXACT
        # for the enumerated depth-five cylinder carrier.
        states = list(product((0,1,2), repeat=5))
        views = {f"prefix:{j}": lambda s, j=j: s[:j] for j in (1,2,3)}
        result = minimum_observers(states, lambda s: s[:3], views)
        self.assertEqual(result.width, 1)
        self.assertEqual(result.sufficient_observers, (("prefix:3",),))
        witness = first_collision(states, lambda s: s[:3], views, ("prefix:2",))
        self.assertIsNotNone(witness)
        self.assertEqual(witness.same_view, witness.left_state[:2])
        self.assertNotEqual(witness.left_answer, witness.right_answer)

    def test_sampled_wave_quantisation_loss(self):
        # This example intentionally does NOT prove any continuum-wide
        # theorem; exact amplitudes are symbolic values in this sample.
        wave_states = (-0.75, -0.25, 0.25, 0.75)
        q = lambda amplitude: "neg" if amplitude < 0 else "pos"
        views = {"symbolic": q, "exact": lambda amplitude: amplitude}
        self.assertIsNone(minimum_observers(wave_states, lambda a: a, {"symbolic": q}))
        result = minimum_observers(wave_states, lambda a: a, views)
        self.assertEqual(result.width, 1)
        self.assertEqual(result.sufficient_observers, (("exact",),))

    def test_empty_projection_for_constant(self):
        states = list(product((0,1,2), repeat=3))
        self.assertEqual(minimum_coordinate_width(states, lambda _: 0).width, 0)

    def test_missing_observers_detected(self):
        states = (("x",0), ("x",1))
        views = {"same": lambda s: s[0]}
        self.assertIsNone(minimum_observers(states, lambda s: s[1], views))

    def test_nonhashable_states_rejected(self):
        with self.assertRaises(TypeError):
            minimum_observers([[0], [1]], lambda s: s[0], {})


if __name__ == "__main__":
    unittest.main()
