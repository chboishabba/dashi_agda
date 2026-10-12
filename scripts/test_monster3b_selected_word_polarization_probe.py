import unittest

from scripts.monster3b_selected_word_polarization_probe import verify


class Monster3BPolarizationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_full_block_mixing(self):
        self.assertEqual(self.out["block_ranks_A_B_C_D"], (6, 6, 6, 6))

    def test_transverse_images(self):
        self.assertTrue(self.out["image_X6_transverse_to_X6"])
        self.assertTrue(self.out["image_X6dual_transverse_to_X6dual"])

    def test_fixed_role_chart_not_invariant(self):
        self.assertFalse(self.out["fixed_6_15_6_role_chart_invariant"])
        self.assertTrue(self.out["polarization_chart_transition_required"])


if __name__ == "__main__":
    unittest.main()
