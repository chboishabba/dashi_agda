#!/usr/bin/env python3
"""Explore a finite constrained nonlinear Wilson critical-point map.

The map works in coordinates on ker Q.  It uses the restricted quadratic
Hessian as a preconditioner and the literal finite Wilson action as the nonlinear
objective.  Jacobians and contraction factors are numerical diagnostics only.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import numpy as np
from common import (PeriodicLattice, block_average_matrix, constrained_hessian,
                    gauge_fixed_hessian, lie_field_to_links, nullspace,
                    wilson_action, write_receipt)


def finite_gradient(fun, x: np.ndarray, eps: float) -> np.ndarray:
    grad = np.empty_like(x)
    for i in range(len(x)):
        e = np.zeros_like(x); e[i] = eps
        grad[i] = (fun(x+e)-fun(x-e))/(2*eps)
    return grad


def numerical_jacobian(fun, x: np.ndarray, eps: float) -> np.ndarray:
    columns = []
    for i in range(len(x)):
        e = np.zeros_like(x); e[i] = eps
        columns.append((fun(x+e)-fun(x-e))/(2*eps))
    return np.stack(columns, axis=1)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=2)
    ap.add_argument('--block', type=int, default=2)
    ap.add_argument('--step-size', type=float, default=0.5)
    ap.add_argument('--gradient-eps', type=float, default=1e-5)
    ap.add_argument('--jacobian-eps', type=float, default=1e-4)
    ap.add_argument('--iterations', type=int, default=20)
    ap.add_argument('--initial-radius', type=float, default=1e-3)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--out', default='operator_analysis/nonlinear_fixed_point.json')
    args = ap.parse_args()

    lat = PeriodicLattice(args.L)
    _, Q = block_average_matrix(lat, args.block)
    H = gauge_fixed_hessian(lat, average=Q)
    K, HK = constrained_hessian(H, Q)
    HK_inv = np.linalg.inv(HK)

    def action_coordinates(z: np.ndarray) -> float:
        fine = (K@z).reshape(lat.shape+(lat.dim,3))
        return wilson_action(lat, lie_field_to_links(fine)) + 0.5*float(z@HK@z)

    def step(z: np.ndarray) -> np.ndarray:
        grad = finite_gradient(action_coordinates, z, args.gradient_eps)
        return z - args.step_size*(HK_inv@grad)

    zero = np.zeros(K.shape[1])
    J = numerical_jacobian(step, zero, args.jacobian_eps)
    contraction = float(np.linalg.norm(J,2))
    rng = np.random.default_rng(args.seed)
    z = rng.normal(size=K.shape[1])
    z *= args.initial_radius/max(np.linalg.norm(z),1e-30)
    history = [float(np.linalg.norm(z))]
    for _ in range(args.iterations):
        z = step(z); history.append(float(np.linalg.norm(z)))
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    write_receipt(args.out, {
        'operator': 'finite_nonlinear_critical_map', 'L': args.L,
        'coordinate_dimension': int(K.shape[1]),
        'jacobian_operator_norm_at_zero': contraction,
        'locally_contractive_candidate': bool(contraction < 1),
        'initial_norm': history[0], 'final_norm': history[-1],
        'norm_history': history,
    })

if __name__ == '__main__':
    main()
