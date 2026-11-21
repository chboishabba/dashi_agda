"""Independent exact-arithmetic P0.01 Dirichlet regressions (no physical data)."""
import unittest
from fractions import Fraction
from check_bh4_grounded_poisson_exact import (
    FACE_MULTIPLICITIES, grounded_matrix, quadratic_energy,
    direct_quadratic, exact_ldlt_pivots, exact_poisson_solve,
    certify_grounded_poisson,
)


class GroundedPoissonExactTests(unittest.TestCase):
    def test_native_spd_and_boundary_faces(self):
        self.assertEqual(sum(FACE_MULTIPLICITIES), 54)
        self.assertEqual(certify_grounded_poisson()["strictly_positive_pivots"], 27)

    def test_quadratic_square_identity(self):
        A = grounded_matrix(Fraction(2, 3), Fraction(5, 7))
        v = [Fraction((i % 5) - 2, i + 2) for i in range(27)]
        self.assertEqual(direct_quadratic(v, A),
                         quadratic_energy(v, Fraction(2, 3), Fraction(5, 7)))
        self.assertGreater(quadratic_energy(v), 0)
        self.assertEqual(quadratic_energy([0] * 27), 0)

    def test_exact_nonconstant_poisson_solution(self):
        rho = [Fraction(i - 13, 2 * i + 3) for i in range(27)]
        solution = exact_poisson_solve(rho, Fraction(3, 2), Fraction(7, 5))
        A = grounded_matrix(Fraction(3, 2), Fraction(7, 5))
        for i in range(27):
            self.assertEqual(sum(A[i][j] * solution[j] for j in range(27)), rho[i])

    def test_negative_controls(self):
        with self.assertRaises(ValueError):
            grounded_matrix(0, 1)
        with self.assertRaises(ValueError):
            grounded_matrix(1, -1)
        with self.assertRaises(ValueError):
            exact_poisson_solve([0] * 26)


if __name__ == "__main__":
    unittest.main()
