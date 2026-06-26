#!/usr/bin/env python3
"""Verify L_neg,cross - c0 * L_abs,cross ⪰ 0 on the seam block.

Uses the existing summary.json — no expensive recomputation.
The PSD condition is equivalent to λ_min(K_block) ≥ c0,
which is directly reported by the decomposition script.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

C0 = 0.15
SUMMARY_PATH = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_cross_shell_block_decomposition_20260625/summary.json"
)


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--c0", type=float, default=C0)
    p.add_argument("--Ns", type=int, nargs="+", default=[6, 8, 10, 12])
    args = p.parse_args()

    if not SUMMARY_PATH.exists():
        print(f"❌ {SUMMARY_PATH} not found")
        return 1

    data = json.loads(SUMMARY_PATH.read_text())
    rows_by_N = {int(r["N"]): r for r in data.get("rows", [])}

    print(f"PSD verification: L_neg,cross - {args.c0} * L_abs,cross ⪰ 0\n")
    print(f"  {'N':>3s}  {'λ_min(K_block)':>16s}  {'gap':>10s}  {'PSD':>5s}")
    all_ok = True
    for N in args.Ns:
        r = rows_by_N.get(N)
        if r is None:
            print(f"  {N:3d}  {'—':>16s}  {'—':>10s}  {'N/A':>5s}")
            all_ok = False
            continue
        blk = r.get("block_lambda_min")
        if not (isinstance(blk, (int, float)) and math.isfinite(blk)):
            print(f"  {N:3d}  {'N/A':>16s}  {'N/A':>10s}  {'N/A':>5s}")
            all_ok = False
            continue
        lam = float(blk)
        gap = lam - args.c0
        ok = gap >= -1.0e-10
        all_ok = all_ok and ok
        print(f"  {N:3d}  {lam:16.6f}  {gap:+10.6f}  {'✅' if ok else '❌':>5s}")

    print(f"\nResult: {'ALL PASS' if all_ok else 'FAIL'}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    exit(main())
