#!/usr/bin/env python3
from __future__ import annotations
import unittest
import numpy as np

from common import (
    PeriodicLattice, adjoint_matrix, block_average_matrix,
    conditional_covariance, constrained_hessian, gauge_fixed_hessian,
    identity_links, qmul, qconj, wilson_action,
)


class FiniteOneStepTests(unittest.TestCase):
    def test_quaternion_inverse(self) -> None:
        q = np.array([0.5, 0.5, 0.5, 0.5])
        self.assertTrue(np.allclose(qmul(q, qconj(q)), [1, 0, 0, 0]))
        self.assertTrue(np.allclose(adjoint_matrix(q).T @ adjoint_matrix(q), np.eye(3)))

    def test_identity_wilson_action(self) -> None:
        lat = PeriodicLattice(2)
        self.assertAlmostEqual(wilson_action(lat, identity_links(lat)), 0.0)

    def test_q_hessian_covariance_vertical_slice(self) -> None:
        lat = PeriodicLattice(2)
        coarse, Q = block_average_matrix(lat, 2)
        self.assertEqual(coarse.L, 1)
        self.assertEqual(Q.shape, (3*coarse.n_bonds, 3*lat.n_bonds))
        H = gauge_fixed_hessian(lat, average=Q)
        K, HK = constrained_hessian(H, Q)
        self.assertGreater(float(np.linalg.eigvalsh(HK)[0]), 0.0)
        _, CK, C = conditional_covariance(H, Q)
        self.assertLess(np.linalg.norm(CK@HK-np.eye(HK.shape[0]), ord=np.inf), 1e-10)
        self.assertLess(np.linalg.norm(Q@C, ord=np.inf), 1e-10)


if __name__ == '__main__':
    unittest.main()
