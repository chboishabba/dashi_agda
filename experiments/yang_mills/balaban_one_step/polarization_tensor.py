#!/usr/bin/env python3
"""Numerically differentiate the finite restricted log determinant at B=0."""
from __future__ import annotations
import argparse
from pathlib import Path
import numpy as np
from common import (PeriodicLattice, block_average_matrix, gauge_fixed_hessian,
                    constrained_hessian, lie_field_to_links, slogdet_positive,
                    write_receipt)


def mode_field(lat: PeriodicLattice, momentum: tuple[int, ...], axis: int, color: int) -> np.ndarray:
    field = np.zeros(lat.shape + (lat.dim, 3), dtype=float)
    for x in lat.sites():
        phase = 2*np.pi*sum(momentum[i]*x[i] for i in range(lat.dim))/lat.L
        field[x + (axis, color)] = np.cos(phase)
    norm = np.linalg.norm(field)
    return field/norm if norm else field


def effective(lat: PeriodicLattice, block: int, field: np.ndarray,
              gauge_weight: float, average_weight: float) -> float:
    links = lie_field_to_links(field)
    _, Q = block_average_matrix(lat, block, links)
    H = gauge_fixed_hessian(lat, background=links, gauge_weight=gauge_weight,
                            average=Q, average_weight=average_weight)
    _, HK = constrained_hessian(H, Q)
    return 0.5*slogdet_positive(HK)[0]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=2)
    ap.add_argument('--block', type=int, default=2)
    ap.add_argument('--momentum', default='1,0,0,0')
    ap.add_argument('--color', type=int, default=0)
    ap.add_argument('--eps', type=float, default=1e-4)
    ap.add_argument('--gauge-weight', type=float, default=1.0)
    ap.add_argument('--average-weight', type=float, default=1.0)
    ap.add_argument('--out', default='operator_analysis/polarization.npy')
    args = ap.parse_args()
    lat = PeriodicLattice(args.L)
    momentum = tuple(map(int, args.momentum.split(',')))
    if len(momentum) != lat.dim:
        raise ValueError('momentum dimension mismatch')
    modes = [mode_field(lat, momentum, mu, args.color) for mu in range(lat.dim)]
    eps = args.eps
    tensor = np.empty((lat.dim, lat.dim))
    for mu, u in enumerate(modes):
        for nu, v in enumerate(modes):
            tensor[mu,nu] = (
                effective(lat,args.block,eps*(u+v),args.gauge_weight,args.average_weight)
                - effective(lat,args.block,eps*(u-v),args.gauge_weight,args.average_weight)
                - effective(lat,args.block,eps*(-u+v),args.gauge_weight,args.average_weight)
                + effective(lat,args.block,-eps*(u+v),args.gauge_weight,args.average_weight)
            )/(4*eps*eps)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    np.save(args.out, tensor)
    write_receipt(Path(args.out).with_suffix('.json'), {
        'operator': 'finite_vacuum_polarization', 'L': args.L,
        'momentum': list(momentum), 'color': args.color, 'eps': eps,
        'symmetry_residual': float(np.linalg.norm(tensor-tensor.T)),
    })

if __name__ == '__main__':
    main()
