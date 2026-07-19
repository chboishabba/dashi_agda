#!/usr/bin/env python3
"""Report symmetry and Ward-transversality residuals."""
from __future__ import annotations
import argparse
import numpy as np
from common import write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--tensor', required=True)
    ap.add_argument('--L', type=int, required=True)
    ap.add_argument('--momentum', default='1,0,0,0')
    ap.add_argument('--out', default='operator_analysis/ward.json')
    args = ap.parse_args()
    tensor = np.load(args.tensor)
    p = np.asarray(tuple(map(int, args.momentum.split(','))), dtype=float)
    k = 2*np.sin(np.pi*p/args.L)
    write_receipt(args.out, {
        'operator': 'ward_residuals',
        'symmetry': float(np.linalg.norm(tensor-tensor.T)),
        'left_transversality': float(np.linalg.norm(k@tensor)),
        'right_transversality': float(np.linalg.norm(tensor@k)),
        'tensor_norm': float(np.linalg.norm(tensor)),
    })

if __name__ == '__main__':
    main()
