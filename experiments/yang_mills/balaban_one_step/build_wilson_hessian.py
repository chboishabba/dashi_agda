#!/usr/bin/env python3
"""Build the finite gauge-fixed Wilson quadratic Hessian."""
from __future__ import annotations
import argparse
from pathlib import Path
import numpy as np
from common import PeriodicLattice, gauge_fixed_hessian, identity_links, lie_field_to_links, write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=2)
    ap.add_argument('--Q', help='optional block-average matrix .npy')
    ap.add_argument('--background', help='optional .npy su(2) field')
    ap.add_argument('--gauge-weight', type=float, default=1.0)
    ap.add_argument('--average-weight', type=float, default=1.0)
    ap.add_argument('--out', default='operator_analysis/H.npy')
    args = ap.parse_args()
    lat = PeriodicLattice(args.L)
    bg = identity_links(lat) if args.background is None else lie_field_to_links(np.load(args.background))
    Q = None if args.Q is None else np.load(args.Q)
    H = gauge_fixed_hessian(lat, background=bg, gauge_weight=args.gauge_weight,
                            average=Q, average_weight=args.average_weight)
    eig = np.linalg.eigvalsh(H)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    np.save(args.out, H)
    write_receipt(Path(args.out).with_suffix('.json'), {
        'operator': 'gauge_fixed_wilson_hessian', 'L': args.L,
        'shape': list(H.shape), 'symmetric_residual': float(np.linalg.norm(H-H.T)),
        'lambda_min': float(eig[0]), 'lambda_max': float(eig[-1]),
    })

if __name__ == '__main__':
    main()
