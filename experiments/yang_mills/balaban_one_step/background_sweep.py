#!/usr/bin/env python3
"""Sweep finite regular SU(2) backgrounds and search for coercivity loss."""
from __future__ import annotations
import argparse
import csv
from pathlib import Path
import numpy as np
from common import (PeriodicLattice, block_average_matrix, constrained_hessian,
                    gauge_fixed_hessian, lie_field_to_links, write_receipt)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=2)
    ap.add_argument('--block', type=int, default=2)
    ap.add_argument('--radii', default='0,0.01,0.02,0.05')
    ap.add_argument('--samples', type=int, default=8)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--out', default='operator_analysis/background_sweep.csv')
    args = ap.parse_args()
    lat = PeriodicLattice(args.L)
    rng = np.random.default_rng(args.seed)
    rows = []
    for radius in map(float, args.radii.split(',')):
        for sample in range(args.samples):
            direction = rng.normal(size=lat.shape+(lat.dim,3))
            direction /= max(np.linalg.norm(direction), 1e-30)
            links = lie_field_to_links(radius*direction)
            _, Q = block_average_matrix(lat, args.block, links)
            H = gauge_fixed_hessian(lat, background=links, average=Q)
            _, HK = constrained_hessian(H, Q)
            ev = np.linalg.eigvalsh(HK)
            rows.append({'radius': radius, 'sample': sample,
                         'lambda_min': ev[0], 'lambda_max': ev[-1],
                         'condition': ev[-1]/ev[0]})
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys())
        writer.writeheader(); writer.writerows(rows)
    write_receipt(out.with_suffix('.json'), {
        'operator': 'background_sweep', 'L': args.L,
        'samples': len(rows),
        'minimum_lambda': float(min(r['lambda_min'] for r in rows)),
    })

if __name__ == '__main__':
    main()
