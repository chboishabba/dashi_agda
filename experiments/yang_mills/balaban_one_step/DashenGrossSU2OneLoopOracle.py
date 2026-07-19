#!/usr/bin/env python3
"""Convention calibration for the Dashen-Gross SU(N) one-loop scale ratio.

This records the published convention formula. It does not substitute that
calibration for Bałaban's finite-history beta theorem.
"""
from __future__ import annotations
import argparse
import math
from common import write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--N', type=int, default=2)
    ap.add_argument('--out', default='operator_analysis/dashen_gross.json')
    args = ap.parse_args()
    ratio_sq = 38.852704*math.exp(-3*math.pi**2/(11*args.N**2))
    write_receipt(args.out, {
        'operator': 'dashen_gross_convention_calibration',
        'N': args.N,
        'lambda_MS_over_lambda_L_squared': ratio_sq,
        'lambda_MS_over_lambda_L': math.sqrt(ratio_sq),
        'promotion': 'calibration_only',
    })

if __name__ == '__main__':
    main()
