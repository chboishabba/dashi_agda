#!/usr/bin/env python3
"""Exact rational non-promotional regression for K04d Nat log gap.

The symbolic all-N identity lives in BishopK04dNatLogFromOriginalGapExact.
This script independently checks the first N actual Nat ratios using Python
Fraction. It does NOT prove exp_B(-L)=1-x, Agda kernel acceptance, or xi.
"""
import argparse
from fractions import Fraction


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--through-index", type=int, default=9999)
    opts = ap.parse_args()
    if not 0 <= opts.through_index <= 100000:
        raise SystemExit("--through-index out of supported range")
    for n in range(opts.through_index + 1):
        q = Fraction(n + 1, n + 2)
        gap = Fraction(1, n + 2)
        assert q + gap == 1, (n, q, gap)
        assert (1 - q) * (n + 2) == 1, n
        assert gap * (n + 2) == 1, n
    print(f"PASS: {opts.through_index+1} exact Nat log-gap rational checks")
    print("NON-PROMOTIONAL: the source Bishop negative-log/exponential identity remains independent.")


if __name__ == "__main__":
    main()
