import unittest

from scripts.monster_albert_f4_action_discriminator import compare_actions


class TestActionDiscriminator(unittest.TestCase):
    def setUp(self):
        self.states = ["removed", "a", "b"]
        self.residual = ["a", "b"]
        self.actors = ["g"]
        self.monster = {
            "g": {"removed": "removed", "a": "b", "b": "a"}
        }

    def test_identical_tables_have_zero_action_mismatch(self):
        result = compare_actions(
            self.states,
            self.residual,
            "removed",
            self.actors,
            self.monster,
            self.monster,
        )
        self.assertEqual(result["action_mismatch_count"], 0)
        self.assertEqual(result["residual_mismatch_count"], 0)
        self.assertTrue(result["removed_invariant_preserved_both"])
        self.assertTrue(result["extensionally_equal_on_supplied_actors"])
        self.assertFalse(result["classical_f4_recognition"])

    def test_corruption_is_detected(self):
        f4 = {
            "g": {"removed": "removed", "a": "a", "b": "b"}
        }
        result = compare_actions(
            self.states,
            self.residual,
            "removed",
            self.actors,
            self.monster,
            f4,
        )
        self.assertEqual(result["action_mismatch_count"], 2)
        self.assertEqual(result["residual_mismatch_count"], 2)
        self.assertFalse(result["extensionally_equal_on_supplied_actors"])
        self.assertFalse(result["classical_f4_recognition"])


if __name__ == "__main__":
    unittest.main()
