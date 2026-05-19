#!/usr/bin/env python3
"""HEP-R46 mass-kernel calibration diagnostic.

Computes the Breit-Wigner window factors and the neutral-current hard kernel factor
needed to match observed mean t43/t45 ratio values.
"""

from __future__ import annotations

import argparse
import math
import csv
from pathlib import Path

M_Z = 91.1876
G_Z = 2.4952


def parse_ratio_mean(path: Path) -> float:
    """Read mean value from a t43/t45 CSV Ratio column."""

    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle)
        header = []
        for row in reader:
            if not row or row[0].startswith("#:"):
                continue
            header = row
            break
        if not header:
            raise ValueError(f"{path}: empty file")
        try:
            ratio_idx = header.index("Ratio")
        except ValueError as exc:
            raise ValueError(f"{path}: missing Ratio column") from exc

        total = 0.0
        count = 0
        for row in reader:
            if not row or row[0].startswith("#:"):
                continue
            if len(row) <= ratio_idx:
                continue
            total += float(row[ratio_idx])
            count += 1

    if count == 0:
        raise ValueError(f"{path}: no ratio rows found")
    return total / count


def bw_integral(m_lo: float, m_hi: float, n: int = 10000) -> float:
    if m_lo <= 0.0 or m_hi <= m_lo:
        raise ValueError(f"invalid mass window [{m_lo}, {m_hi}]")
    dm = (m_hi - m_lo) / n
    m_z2 = M_Z * M_Z
    mz_gamma_sq = (M_Z * G_Z) * (M_Z * G_Z)
    total = 0.0
    for i in range(n):
        m = m_lo + (i + 0.5) * dm
        m2 = m * m
        total += dm / (((m2 - m_z2) ** 2 + mz_gamma_sq))
    return total


def main() -> None:
    parser = argparse.ArgumentParser(description="Diagnose HEP-R46 mass-kernel factor K.")
    parser.add_argument("--t43", default="scripts/data/hepdata/ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv")
    parser.add_argument("--t45", default="scripts/data/hepdata/ins2079374_phistar_mass_106-170_over_mass_76-106_t45.csv")
    args = parser.parse_args()

    t43_mean = parse_ratio_mean(Path(args.t43))
    t45_mean = parse_ratio_mean(Path(args.t45))

    bw_50_76 = bw_integral(50.0, 76.0)
    bw_76_106 = bw_integral(76.0, 106.0)
    bw_106_170 = bw_integral(106.0, 170.0)

    ratio_bw_t43 = bw_50_76 / bw_76_106
    ratio_bw_t45 = bw_106_170 / bw_76_106

    k_needed_t43 = t43_mean / ratio_bw_t43
    k_needed_t45 = t45_mean / ratio_bw_t45

    print("HEP-R46 mass-kernel diagnostic")
    print(f"t43 mean R: {t43_mean:.6f}")
    print(f"t45 mean R: {t45_mean:.6f}")
    print(f"BW ratio 50-76 / 76-106: {ratio_bw_t43:.9f}")
    print(f"BW ratio 106-170 / 76-106: {ratio_bw_t45:.9f}")
    print(f"K needed (t43): {k_needed_t43:.6f}")
    print(f"K needed (t45): {k_needed_t45:.6f}")
    print(f"K_t43 / K_t45: {k_needed_t43 / k_needed_t45:.6f}")
    print("Interpretation:")
    print("  If K values are equal within tolerance, one global mass-kernel constant may apply.")
    print("  If they differ materially, the predictor needs mass-window-dependent hard scaling.")


if __name__ == "__main__":
    main()
