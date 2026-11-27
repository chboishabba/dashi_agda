"""Finite donor regression for ORIGINAL TSVF/OS resolvent cut.

Mirrors ONLY the exact diag(2,5) spectrum already selected by
DASHI.Mathematics.LinearAlgebra.RationalTwoByTwoSelfAdjointSpectralExact.
No physical observer/OS Hilbert or finite-to-continuum claim.
"""
import cmath
from fractions import Fraction as Q
from math import exp
import unittest

I = ((Q(1), Q(0)), (Q(0), Q(1)))
H = ((Q(2), Q(0)), (Q(0), Q(5)))
U = ((Q(0), Q(1)), (Q(1), Q(0)))

def matmul(a, b):
    return tuple(tuple(sum(x * y for x, y in zip(row, col))
                       for col in zip(*b)) for row in a)

def transpose(a):
    return tuple(zip(*a))

def matrix_equal(a, b, tol=1e-12):
    return all(abs(x - y) < tol for rowa, rowb in zip(a, b)
               for x, y in zip(rowa, rowb))

def shifted_inverse_diagonal(h, z):
    assert h[0][1] == 0 and h[1][0] == 0
    if z in (h[0][0], h[1][1]):
        raise ValueError("shift lies in finite spectrum")
    return ((1 / (h[0][0] - z), 0), (0, 1 / (h[1][1] - z)))

def conjugate(a):
    return matmul(matmul(U, a), transpose(U))

class SelectedTwoModeSpectralRegression(unittest.TestCase):
    def test_same_operator_graph_and_conjugacy(self):
        hos = conjugate(H)
        self.assertTrue(matrix_equal(matmul(U, H), matmul(hos, U)))
        self.assertTrue(matrix_equal(conjugate(hos), H))

    def test_nonreal_resolvent(self):
        hos = conjugate(H)
        for z in (1j, 0.3 + 1.5j, -2j):
            robs = shifted_inverse_diagonal(H, z)
            ros = conjugate(robs)
            self.assertTrue(matrix_equal(
                matmul(ros, tuple(tuple(hos[i][j] - (z if i == j else 0)
                                         for j in range(2)) for i in range(2))), I))
            self.assertTrue(matrix_equal(matmul(U, robs), matmul(ros, U)))

    def test_spectral_projections_and_heat(self):
        # P_2=(5 I-H)/3 and P_5=(H-2I)/3 on the actual donor.
        p2 = ((Q(1), Q(0)), (Q(0), Q(0)))
        p5 = ((Q(0), Q(0)), (Q(0), Q(1)))
        self.assertEqual(matmul(p2, p5), ((Q(0), Q(0)), (Q(0), Q(0))))
        for t in (0, 0.1, 1, 5):
            eobs = ((exp(-2*t), 0), (0, exp(-5*t)))
            self.assertTrue(matrix_equal(matmul(U,eobs),matmul(conjugate(eobs),U)))

    def test_spectral_zeta_and_heat_trace(self):
        for s in (1.5, 2, 3):
            self.assertAlmostEqual(2**(-s) + 5**(-s),
                                   sum(e**(-s) for e in (2,5)))
        for t in (0.1,1):
            self.assertAlmostEqual(exp(-2*t)+exp(-5*t),
                                   sum(exp(-t*e) for e in (2,5)))

    def test_negative_controls(self):
        self.assertRaises(ValueError,shifted_inverse_diagonal,H,Q(2))
        self.assertRaises(ValueError,shifted_inverse_diagonal,H,Q(5))
        # Equality on selected first eigenmode does not imply a full
        # two-mode Hamiltonian identification.
        other=((Q(2),Q(0)),(Q(0),Q(6)))
        self.assertEqual(H[0][0],other[0][0])
        self.assertNotEqual(H,other)

if __name__ == "__main__":
    unittest.main()
