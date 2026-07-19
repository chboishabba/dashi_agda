#!/usr/bin/env python3
"""Fit a finite polarization tensor to the lattice transverse YM tensor."""
from __future__ import annotations
import argparse
import numpy as np
from common import PeriodicLattice, extract_beta_from_tensor, write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--tensor', required=True)
    ap.add_argument('--L', type=int, required=True)
    ap.add_argument('--momentum', default='1,0,0,0')
    ap.add_argument('--out', default='operator_analysis/beta.json')
    args = ap.parse_args()
    lat = PeriodicLattice(args.L)
    momentum = tuple(map(int, args.momentum.split(',')))
    result = extract_beta_from_tensor(np.load(args.tensor), lat, momentum)
    write_receipt(args.out, {'operator': 'beta_extraction', 'L': args.L,
                             'momentum': list(momentum), **result})

if __name__ == '__main__':
    main()
