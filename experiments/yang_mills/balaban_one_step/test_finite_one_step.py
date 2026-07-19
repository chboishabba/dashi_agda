#!/usr/bin/env python3
from __future__ import annotations
import unittest
import numpy as np

from common import (
    PeriodicLattice, adjoint_matrix, block_average_matrix,
    conditional_covariance, constrained_hessian, gauge_fixed_hessian,
    identity_links, qmul, qconj, wilson_action,
)
from frontier_search import (
    canonical_section,
    corrected_background_section,
    hodge_poincare_diagnostic,
    run_search,
)
from local_parametrix_search import run_search as run_parametrix_search
from su2_ad_functional_calculus import (
    ad_matrix,
    dexp_matrix,
    inverse_dexp_matrix,
    run as run_ad_calculus,
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

    def test_constructed_zero_background_section(self) -> None:
        lat = PeriodicLattice(2)
        _, Q0 = block_average_matrix(lat, 2)
        S0, residual = canonical_section(Q0)
        self.assertLess(residual, 1e-10)
        corrected = corrected_background_section(Q0, Q0, S0)
        self.assertTrue(corrected["corrected_section_exists"])
        self.assertLess(corrected["corrected_section_residual"], 1e-10)
        self.assertAlmostEqual(corrected["perturbation_section_norm"], 0.0)

    def test_zero_background_hodge_diagnostic(self) -> None:
        lat = PeriodicLattice(2)
        _, Q0 = block_average_matrix(lat, 2)
        H0 = gauge_fixed_hessian(lat, average=Q0)
        report = hodge_poincare_diagnostic(H0)
        self.assertTrue(report["coercive_on_full_finite_space"])
        self.assertGreater(report["smallest_eigenvalue"], 0.0)

    def test_frontier_search_keeps_finite_scope(self) -> None:
        report = run_search(L=2, block=2, radii=[0.0, 0.01], seeds=1)
        self.assertEqual(report["claim_scope"], "finite_lattice_only")
        self.assertTrue(report["zero_background_section"]["constraints_independent"])
        self.assertTrue(report["all_background_sections_closed"])

    def test_axis_slabs_close_trivial_background_parametrix(self) -> None:
        report = run_parametrix_search(
            L=2,
            average_block=2,
            local_sides=[1, 2],
            slab_thicknesses=[2],
            ball_radii=[],
            mus=[0.0],
            radii=[0.0],
            seeds=1,
            relaxations=[1.0],
        )
        self.assertTrue(report["has_strict_weighted_remainder_bound"])
        self.assertTrue(report["has_strict_proper_local_weighted_remainder_bound"])
        self.assertFalse(report["global_inverse_only"])
        proper = report["proper_local_convergent_candidates"]
        self.assertTrue(any(item["patch_family"] == "axis-slabs-2" for item in proper))
        best = report["best_proper_local_candidate"]
        self.assertIsNotNone(best)
        self.assertLess(max(best["left"], best["right"]), 1.0)

    def test_axis_slabs_expose_background_weighted_norm_obstruction(self) -> None:
        report = run_parametrix_search(
            L=2,
            average_block=2,
            local_sides=[1],
            slab_thicknesses=[2],
            ball_radii=[],
            mus=[0.0],
            radii=[0.0, 0.01],
            seeds=1,
            relaxations=[0.25, 0.5, 0.75, 1.0],
        )
        self.assertTrue(report["has_strict_proper_local_weighted_remainder_bound"])
        self.assertFalse(report["all_sampled_backgrounds_have_strict_proper_local_bound"])
        by_radius = {item["radius"]: item for item in report["background_closure"]}
        self.assertTrue(by_radius[0.0]["strict_proper_local_bound"])
        self.assertFalse(by_radius[0.01]["strict_proper_local_bound"])
        self.assertTrue(report["spectral_without_weighted_norm_obstructions"])

    def test_torus_balls_close_sampled_small_backgrounds(self) -> None:
        report = run_parametrix_search(
            L=2,
            average_block=2,
            local_sides=[],
            slab_thicknesses=[],
            ball_radii=[2, 3],
            mus=[0.0],
            radii=[0.0, 0.01, 0.03],
            seeds=1,
            relaxations=[1.0],
        )
        self.assertEqual(report["claim_scope"], "finite_lattice_only")
        self.assertTrue(report["has_strict_proper_local_weighted_remainder_bound"])
        self.assertTrue(report["all_sampled_backgrounds_have_strict_proper_local_bound"])
        proper = report["proper_local_convergent_candidates"]
        self.assertTrue(any(
            item["radius"] == 0.01 and item["patch_family"] == "torus-ball-2"
            for item in proper
        ))
        self.assertTrue(any(
            item["radius"] == 0.03 and item["patch_family"] == "torus-ball-3"
            for item in proper
        ))
        by_radius = {item["radius"]: item for item in report["background_closure"]}
        self.assertLess(
            max(
                by_radius[0.03]["best_candidate"]["left"],
                by_radius[0.03]["best_candidate"]["right"],
            ),
            1.0,
        )

    def test_su2_ad_cubic_and_closed_dexp_inverse(self) -> None:
        y = np.array([0.07, -0.03, 0.11])
        A = ad_matrix(y)
        self.assertLess(
            np.linalg.norm(A@A@A + 4.0*float(y@y)*A, ord=2),
            1e-12,
        )
        D = dexp_matrix(y)
        Di = inverse_dexp_matrix(y)
        self.assertLess(np.linalg.norm(Di@D-np.eye(3), ord=2), 1e-12)
        self.assertLess(np.linalg.norm(D@Di-np.eye(3), ord=2), 1e-12)
        report = run_ad_calculus(radius=0.2, samples=16, seed=0)
        self.assertLess(report["inverse_left_residual_max"], 1e-12)
        self.assertLess(report["inverse_right_residual_max"], 1e-12)


if __name__ == '__main__':
    unittest.main()
