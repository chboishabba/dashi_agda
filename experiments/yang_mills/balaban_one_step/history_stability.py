#!/usr/bin/env python3
"""Compare beta receipts across finite RG histories without uniform promotion."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np
from common import write_receipt


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('receipts', nargs='+')
    ap.add_argument('--out', default='operator_analysis/history_stability.json')
    args = ap.parse_args()
    data = [json.loads(Path(p).read_text()) for p in args.receipts]
    beta = np.asarray([d['beta'] for d in data], dtype=float)
    write_receipt(args.out, {
        'operator': 'history_stability', 'count': len(data),
        'beta_min': float(beta.min()), 'beta_max': float(beta.max()),
        'beta_range': float(np.ptp(beta)), 'beta_mean': float(beta.mean()),
        'beta_std': float(beta.std()),
    })

if __name__ == '__main__':
    main()
