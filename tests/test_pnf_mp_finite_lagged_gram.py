"""Exact synthetic temporal operators for the MP/static-Gram negative controls.

G1 = X[:-1].T @ X[1:] (non-cyclic, uncentred). Static covariance
and singular spectra are separate from the ordered lag operator.
No circular-law, Brown-measure, causality or MP-calibrated dynamic
null is claimed. The two full-rank examples are also lag-*isospectral*.
"""
import unittest
import numpy as np


def lag_one(x):
    return x[:-1].T @ x[1:]


def delay2(x):
    return np.concatenate((x[:-1], x[1:]), axis=1)


class MPFiniteLaggedGramTests(unittest.TestCase):
    def setUp(self):
        self.singular_a = np.array([(0, 1), (1, 0), (0, 1), (1, 0)], dtype=np.int64)
        self.singular_b = np.array([(0, 1), (0, 1), (1, 0), (1, 0)], dtype=np.int64)
        self.full_a = np.array([(0, 0), (1, 0), (0, 1), (1, 1)], dtype=np.int64)
        self.full_b = np.array([(0, 0), (0, 1), (1, 0), (1, 1)], dtype=np.int64)

    def test_singular_lag_is_observable_while_static_covariance_collides(self):
        a, b = self.singular_a, self.singular_b
        np.testing.assert_array_equal(a.T @ a, b.T @ b)
        np.testing.assert_array_equal(np.cov(a, rowvar=False), np.cov(b, rowvar=False))
        np.testing.assert_array_equal(lag_one(a), [[0, 1], [2, 0]])
        np.testing.assert_array_equal(lag_one(b), [[1, 0], [1, 1]])
        self.assertEqual(int(lag_one(a)[0, 0]), 0)
        self.assertEqual(int(lag_one(b)[0, 0]), 1)
        np.testing.assert_allclose(np.sort(np.linalg.eigvals(lag_one(a))), [-np.sqrt(2), np.sqrt(2)])
        np.testing.assert_allclose(np.linalg.eigvals(lag_one(b)), [1, 1])
        self.assertEqual((np.diff(a[:, 0]) != 0).sum(), 3)
        self.assertEqual((np.diff(b[:, 0]) != 0).sum(), 1)

    def test_full_rank_lag_operators_differ_but_eigenvalues_collide(self):
        a, b = self.full_a, self.full_b
        np.testing.assert_array_equal(a.T @ a, b.T @ b)
        np.testing.assert_allclose(np.cov(a, rowvar=False), np.eye(2) / 3)
        np.testing.assert_array_equal(np.cov(a, rowvar=False), np.cov(b, rowvar=False))
        np.testing.assert_array_equal(lag_one(a), [[0, 1], [1, 1]])
        np.testing.assert_array_equal(lag_one(b), [[1, 1], [1, 0]])
        self.assertNotEqual(int(lag_one(a)[0, 0]), int(lag_one(b)[0, 0]))
        np.testing.assert_allclose(np.sort(np.linalg.eigvals(lag_one(a))),
                                   np.sort(np.linalg.eigvals(lag_one(b))))
        self.assertEqual(round(float(np.linalg.det(lag_one(a)))), -1)
        self.assertEqual(round(float(np.linalg.det(lag_one(b)))), -1)
        self.assertEqual(int(np.trace(lag_one(a))), 1)
        self.assertEqual(int(np.trace(lag_one(b))), 1)
        # Even the complete delay2 Gram spectra collide for this
        # particular reversed pair; a dynamic *spectral* summary alone
        # is not a universal chronology decoder.
        np.testing.assert_allclose(
            np.linalg.eigvalsh(delay2(a).T @ delay2(a)),
            np.linalg.eigvalsh(delay2(b).T @ delay2(b)),
            atol=1e-12,
        )

    def test_signed_area_is_not_universal_order_decoder(self):
        # Both singular pair lag operators have same antisymmetric
        # cross-correlation G[0,1]-G[1,0] = -1, despite different lag11.
        l1, l2 = lag_one(self.singular_a), lag_one(self.singular_b)
        self.assertEqual(int(l1[0, 1] - l1[1, 0]), -1)
        self.assertEqual(int(l2[0, 1] - l2[1, 0]), -1)
        # For full rank pair cross-lag antisymmetry is zero.
        for x in (self.full_a, self.full_b):
            g = lag_one(x)
            self.assertEqual(int(g[0, 1] - g[1, 0]), 0)


if __name__ == "__main__":
    unittest.main()
