"""Deterministic synthetic 4x2 same-covariance/different-time-order control.

No clinical, financial, or causal conclusion; MP null validity is not assumed.
"""
import unittest
import numpy as np


class StaticGramTemporalTests(unittest.TestCase):
    def test_same_covariance_same_spectrum_different_lag(self):
        alternating = np.array([[0, 1], [1, 0], [0, 1], [1, 0]], dtype=float)
        clustered = np.array([[0, 1], [0, 1], [1, 0], [1, 0]], dtype=float)
        self.assertTrue(np.array_equal(alternating.sum(axis=0),
                                       clustered.sum(axis=0)))
        self.assertTrue(np.array_equal(alternating.T @ alternating,
                                       clustered.T @ clustered))
        covariances = [np.cov(x, rowvar=False, ddof=1)
                       for x in (alternating, clustered)]
        self.assertTrue(np.array_equal(covariances[0], covariances[1]))
        self.assertTrue(np.allclose(covariances[0], [[1/3, -1/3], [-1/3, 1/3]]))
        self.assertTrue(np.allclose(np.linalg.eigvalsh(covariances[0]),
                                    [0, 2/3]))
        self.assertTrue(np.array_equal(
            np.linalg.eigvalsh(covariances[0]),
            np.linalg.eigvalsh(covariances[1])))
        lag = [int(x[:-1, 0] @ x[1:, 0]) for x in (alternating, clustered)]
        self.assertEqual(lag, [0, 1])


if __name__ == "__main__":
    unittest.main()
