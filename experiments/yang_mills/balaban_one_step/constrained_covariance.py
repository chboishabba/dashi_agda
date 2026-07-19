#!/usr/bin/env python3
"""Restrict H to ker Q and construct its finite numerical covariance."""
from __future__ import annotations
import argparse
from pathlib import Path
import numpy as np
from common import conditional_covariance, gershgorin_lower_bound, write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--H', required=True)
    ap.add_argument('--Q', required=True)
    ap.add_argument('--out-prefix', default='operator_analysis/constrained')
    ap.add_argument('--rtol', type=float, default=1e-10)
    args = ap.parse_args()
    H, Q = np.load(args.H), np.load(args.Q)
    K, CK, C = conditional_covariance(H, Q, rtol=args.rtol)
    prefix = Path(args.out_prefix)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    np.save(str(prefix)+'_kernel_basis.npy', K)
    np.save(str(prefix)+'_coordinate_covariance.npy', CK)
    np.save(str(prefix)+'_full_covariance.npy', C)
    HK = K.T @ H @ K
    write_receipt(str(prefix)+'_receipt.json', {
        'operator': 'conditional_covariance', 'kernel_dimension': int(K.shape[1]),
        'lambda_min': float(np.linalg.eigvalsh(HK)[0]),
        'gershgorin_lower_bound': gershgorin_lower_bound(HK),
        'left_inverse_residual': float(np.linalg.norm(CK@HK-np.eye(HK.shape[0]), ord=np.inf)),
        'constraint_residual': float(np.linalg.norm(Q@C, ord=np.inf)),
    })

if __name__ == '__main__':
    main()
