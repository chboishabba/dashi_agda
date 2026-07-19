#!/usr/bin/env python3
"""Build the finite gauge-covariant block-average matrix Q(B)."""
from __future__ import annotations
import argparse
from pathlib import Path
import numpy as np
from common import PeriodicLattice, block_average_matrix, identity_links, lie_field_to_links, write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=2)
    ap.add_argument('--block', type=int, default=2)
    ap.add_argument('--background', help='optional .npy su(2) field with shape (L,)*4+(4,3)')
    ap.add_argument('--out', default='operator_analysis/Q.npy')
    args = ap.parse_args()
    lat = PeriodicLattice(args.L)
    background = identity_links(lat) if args.background is None else lie_field_to_links(np.load(args.background))
    coarse, Q = block_average_matrix(lat, args.block, background)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    np.save(args.out, Q)
    write_receipt(Path(args.out).with_suffix('.json'), {
        'operator': 'Q(B)', 'L': args.L, 'block': args.block,
        'fine_shape': list(Q.shape), 'coarse_L': coarse.L,
        'rank': int(np.linalg.matrix_rank(Q)),
    })

if __name__ == '__main__':
    main()
