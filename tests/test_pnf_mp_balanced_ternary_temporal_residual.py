"""Synthetic, exact signed-ternary temporal residual cross-domain check.

The signs correspond to DASHI.Combinatorics.TriadicVideoCodecObservationQuotient's
negTrit / zeroTrit / posTrit values; this is NOT the sibling codec's
actual compressed payload, entropy model, or measured rate-distortion.
"""
import unittest
import numpy as np


def delta(x):
    out = np.diff(x.astype(np.int64), axis=0)
    assert np.isin(out, (-1, 0, 1)).all()
    return out


def reconstruct(initial, residual):
    return np.concatenate((initial[None, :],
                           initial[None, :] + np.cumsum(residual, axis=0)),
                          axis=0)


class PNFTemporalTernaryResidual(unittest.TestCase):
    def test_two_singular_static_indistinguishable_histories(self):
        a = np.array([[0, 1], [1, 0], [0, 1], [1, 0]])
        b = np.array([[0, 1], [0, 1], [1, 0], [1, 0]])
        np.testing.assert_array_equal(np.cov(a, rowvar=False),
                                      np.cov(b, rowvar=False))
        for x in (a, b):
            np.testing.assert_array_equal(reconstruct(x[0], delta(x)), x)
        self.assertEqual(int(np.count_nonzero(delta(a[:, :1]))), 3)
        self.assertEqual(int(np.count_nonzero(delta(b[:, :1]))), 1)
        # Signed residuals do not automatically give a general-purpose
        # compression win; a header, entropy coder, side bits are payable.
        self.assertFalse(np.array_equal(delta(a[:, :1]), delta(b[:, :1])))

    def test_full_rank_example_simple_total_variation_collision(self):
        a = np.array([[0, 0], [1, 0], [0, 1], [1, 1]])
        b = np.array([[0, 0], [0, 1], [1, 0], [1, 1]])
        np.testing.assert_array_equal(np.cov(a, rowvar=False),
                                      np.cov(b, rowvar=False))
        for x in (a, b):
            np.testing.assert_array_equal(reconstruct(x[0], delta(x)), x)
        self.assertEqual(int(np.abs(delta(a)).sum()), 4)
        self.assertEqual(int(np.abs(delta(b)).sum()), 4)
        # Even identical simple residual costs do not imply identical history.
        self.assertFalse(np.array_equal(delta(a), delta(b)))


if __name__ == "__main__":
    unittest.main()
