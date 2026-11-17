import unittest

from scripts.exceptional_gravity_ternary36_refinement_probe import verify


class Ternary36GravityRefinementTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_depth36_matches_gr_scale(self):
        self.assertLess(abs(float(self.out["theory_ratio"]) - 1.0), 0.05)

    def test_depth36_inside_published_bands(self):
        self.assertLessEqual(abs(float(self.out["corrected_sigma_offset"])), 1.0)
        self.assertLessEqual(abs(float(self.out["synchronous_sigma_offset"])), 1.0)

    def test_depth36_beats_neighbors(self):
        t = float(self.out["theory_gradient_per_mm"])
        g = float(self.out["predicted_gradient_per_mm"])
        self.assertLess(abs(g - t), abs(float(self.out["depth35_gradient"]) - t))
        self.assertLess(abs(g - t), abs(float(self.out["depth37_gradient"]) - t))


if __name__ == "__main__":
    unittest.main()
