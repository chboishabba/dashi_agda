#!/usr/bin/env python3
"""Locate the weakest finite gauge-fixed Hodge mode in momentum space."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

from common import PeriodicLattice, block_average_matrix, gauge_fixed_hessian, write_receipt


def weakest_mode_report(L: int, block: int) -> dict:
    lat = PeriodicLattice(L)
    _, Q = block_average_matrix(lat, block)
    H = gauge_fixed_hessian(lat, average=Q)
    H = 0.5 * (H + H.T)
    values, vectors = np.linalg.eigh(H)
    weakest = vectors[:, 0].reshape(lat.shape + (lat.dim, 3))
    transformed = np.fft.fftn(weakest, axes=tuple(range(lat.dim)), norm="ortho")
    power = np.sum(np.abs(transformed) ** 2, axis=(-2, -1))
    momentum = tuple(int(x) for x in np.unravel_index(np.argmax(power), power.shape))
    total_power = float(np.sum(power))
    dominant_power = float(power[momentum])
    return {
        "claim_scope": "finite_lattice_only",
        "lattice_extent": L,
        "block_length": block,
        "smallest_eigenvalue": float(values[0]),
        "next_eigenvalue": float(values[1]) if len(values) > 1 else None,
        "candidate_hodge_constant": float(1.0 / values[0]) if values[0] > 0 else None,
        "dominant_lattice_momentum": list(momentum),
        "dominant_momentum_power_fraction": dominant_power / max(total_power, 1e-30),
        "zero_momentum_power_fraction": float(power[(0,) * lat.dim]) / max(total_power, 1e-30),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--L", type=int, default=2)
    parser.add_argument("--block", type=int, default=2)
    parser.add_argument("--out", default="operator_analysis/hodge-spectrum.json")
    args = parser.parse_args()
    report = weakest_mode_report(args.L, args.block)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    write_receipt(args.out, {"operator": "gauge_fixed_hodge_spectrum", **report})
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
