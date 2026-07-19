#!/usr/bin/env python3
"""Emit conservative finite-matrix positivity and inverse certificates."""
from __future__ import annotations
import argparse
import numpy as np
from common import gershgorin_lower_bound, write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--matrix', required=True)
    ap.add_argument('--out', default='operator_analysis/certificate.json')
    args = ap.parse_args()
    A = np.load(args.matrix)
    S = 0.5*(A+A.T)
    eig = np.linalg.eigvalsh(S)
    inv = np.linalg.inv(S)
    residual = np.linalg.norm(S@inv-np.eye(S.shape[0]), ord=np.inf)
    eps = np.finfo(float).eps
    norm = np.linalg.norm(S, ord=np.inf)
    conservative = float(eig[0]-64*eps*max(1.0,norm)*S.shape[0])
    write_receipt(args.out, {
        'status_detail': 'floating_with_roundoff_margin',
        'dimension': int(S.shape[0]),
        'lambda_min_numeric': float(eig[0]),
        'lambda_lower_roundoff_margin': conservative,
        'gershgorin_lower_bound': gershgorin_lower_bound(S),
        'inverse_residual': float(residual),
        'certified_positive_by_margin': bool(conservative > 0),
    })

if __name__ == '__main__':
    main()
