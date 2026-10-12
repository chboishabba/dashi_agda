import unittest

from scripts.exceptional_metric_quadratic_laplacian_probe import verify


class IntrinsicQuadraticLaplacianTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = verify()

    def test_symmetry_repair(self):
        self.assertEqual(self.out["q_isometry_group_order"], 144)
        self.assertEqual(self.out["torus_adjacency_isometry_count"], 8)
        self.assertEqual(self.out["intrinsic_adjacency_isometry_count"], 144)

    def test_intrinsic_poisson(self):
        self.assertEqual(self.out["intrinsic_degree"], 24)
        self.assertEqual(self.out["intrinsic_potential"], "phi = rho/27")

    def test_old_depth36_match_not_robust(self):
        self.assertLess(float(self.out["depth36_theory_ratio"]), 0.30)
        self.assertLess(
            abs(float(self.out["depth35_gradient"]) - 1.09e-19),
            abs(float(self.out["depth36_gradient"]) - 1.09e-19),
        )


if __name__ == "__main__":
    unittest.main()
