"""Deterministic, finite, full-rank MP-observer negative control."""
import unittest
import numpy as np


class FullRankTemporalNonidentification(unittest.TestCase):
    def test_same_positive_definite_covariance_different_lag(self):
        first = np.asarray([(0, 0), (1, 0), (0, 1), (1, 1)], dtype=np.int64)
        second = np.asarray([(0, 0), (0, 1), (1, 0), (1, 1)], dtype=np.int64)
        np.testing.assert_array_equal(first.sum(axis=0), second.sum(axis=0))
        np.testing.assert_array_equal(first.T @ first, second.T @ second)
        np.testing.assert_array_equal(first.T @ first, [[2, 1], [1, 2]])
        c1, c2 = np.cov(first, rowvar=False), np.cov(second, rowvar=False)
        np.testing.assert_array_equal(c1, c2)
        np.testing.assert_allclose(c1, np.eye(2) / 3)
        self.assertGreater(np.linalg.eigvalsh(c1).min(), 0)
        np.testing.assert_allclose(np.linalg.eigvalsh(c1), [1/3, 1/3])
        lag = [int(np.dot(z[:-1, 0], z[1:, 0])) for z in (first, second)]
        self.assertEqual(lag, [0, 1])


if __name__ == "__main__":
    unittest.main()
