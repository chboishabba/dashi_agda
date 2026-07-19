#!/usr/bin/env python3
"""Finite Neumann/random-walk expansion for a restricted Green operator.

Given a positive restricted Hessian H, split H=D-E with diagonal D.  If
rho=||D^{-1/2} E D^{-1/2}||_2 < 1, the inverse is a convergent walk sum.  The
script emits the finite truncation, exact residual, and geometric remainder
majorant.  Results are finite computations, not uniform decay theorems.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import numpy as np
from common import constrained_hessian, write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--H', required=True)
    ap.add_argument('--Q', required=True)
    ap.add_argument('--depth', type=int, default=8)
    ap.add_argument('--out-prefix', default='operator_analysis/random_walk')
    args = ap.parse_args()
    _, A = constrained_hessian(np.load(args.H), np.load(args.Q))
    diagonal = np.diag(A)
    if np.any(diagonal <= 0):
        raise np.linalg.LinAlgError('nonpositive diagonal prevents Jacobi walk split')
    root_inv = np.diag(1.0/np.sqrt(diagonal))
    transfer = np.eye(A.shape[0]) - root_inv @ A @ root_inv
    rho = float(np.linalg.norm(transfer, 2))
    term = np.eye(A.shape[0])
    partial = term.copy()
    for _ in range(args.depth):
        term = term @ transfer
        partial += term
    green = root_inv @ partial @ root_inv
    inverse_residual = float(np.linalg.norm(A@green-np.eye(A.shape[0]), 2))
    remainder_bound = float('inf') if rho >= 1 else float(
        np.linalg.norm(root_inv,2)**2 * rho**(args.depth+1)/(1-rho)
    )
    prefix = Path(args.out_prefix)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    np.save(str(prefix)+'_green.npy', green)
    write_receipt(str(prefix)+'_receipt.json', {
        'operator': 'finite_random_walk_green', 'depth': args.depth,
        'transfer_norm': rho, 'convergent_by_norm': bool(rho < 1),
        'inverse_residual': inverse_residual,
        'geometric_remainder_bound': remainder_bound,
    })

if __name__ == '__main__':
    main()
