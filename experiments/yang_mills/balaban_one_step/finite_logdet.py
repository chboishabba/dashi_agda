#!/usr/bin/env python3
"""Compute the positive finite restricted Gaussian log determinant."""
from __future__ import annotations
import argparse
import numpy as np
from common import constrained_hessian, slogdet_positive, write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--H', required=True)
    ap.add_argument('--Q', required=True)
    ap.add_argument('--out', default='operator_analysis/logdet.json')
    args = ap.parse_args()
    _, HK = constrained_hessian(np.load(args.H), np.load(args.Q))
    logdet, residual = slogdet_positive(HK)
    write_receipt(args.out, {
        'operator': 'restricted_logdet', 'dimension': int(HK.shape[0]),
        'logdet': logdet, 'gaussian_half_logdet': 0.5*logdet,
        'inverse_residual': residual,
    })

if __name__ == '__main__':
    main()
