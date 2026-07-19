"""Constructive finite geometry used by the frontier proof search."""
from __future__ import annotations

import numpy as np

from common import PeriodicLattice


def literal_block_lift_section(
    fine: PeriodicLattice, block: int
) -> tuple[PeriodicLattice, np.ndarray]:
    """Lift a coarse bond field constantly over its fine block.

    At the identity background this is an explicit right inverse for the
    block-average convention in common.block_average_matrix: every coarse value
    is copied to all block**dim parallel fine bonds and the average divides by
    the same cardinality.
    """
    if fine.L % block:
        raise ValueError("block size must divide lattice extent")
    coarse = PeriodicLattice(fine.L // block, fine.dim)
    section = np.zeros((3 * fine.n_bonds, 3 * coarse.n_bonds), dtype=float)
    for x in fine.sites():
        coarse_site = tuple(coordinate // block for coordinate in x)
        for mu in range(fine.dim):
            fine_bond = fine.bond_index(x, mu)
            coarse_bond = coarse.bond_index(coarse_site, mu)
            section[
                3 * fine_bond : 3 * fine_bond + 3,
                3 * coarse_bond : 3 * coarse_bond + 3,
            ] = np.eye(3)
    return coarse, section


def right_inverse_residual(Q: np.ndarray, section: np.ndarray) -> float:
    if Q.shape[1] != section.shape[0]:
        raise ValueError("Q and section dimensions do not compose")
    return float(np.linalg.norm(Q @ section - np.eye(Q.shape[0]), ord=2))
