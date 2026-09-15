#!/usr/bin/env python3
"""
Diagnostic execution for DASHI's phase-sensitive finite-near RH lane.

This is NOT a same-object instantiation of the repository's final universal
pole-quotient taper. The Agda interface deliberately keeps poleTaperValue
abstract. This script chooses a Gaussian diagnostic taper and uses actual
Riemann-zero ordinates only to generate target-relative phase gaps.

It exercises the literal reflection-pair architecture

    4 * g(u) * cosh(alpha*u) * cos(delta*u)

and compares:
  * a coarse absolute-envelope majorant: env(u);
  * a weaker phase-sensitive one-sided majorant:
        env(u) * max(cos(delta*u), 0).

For positive envelope env, the second majorant is pointwise valid because
env*cos(theta) <= env*max(cos(theta),0). Its purpose is to test whether the
consumer-relative one-sided route can retain meaningful cancellation before
the exact same-object taper/carrier weld is paid.
"""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 50
SIGMA_U = mp.mpf("0.45")
U = mp.mpf("12")
ALPHAS = (mp.mpf("0"), mp.mpf("0.10"), mp.mpf("0.20"))
TARGET_ZERO_INDEX = 9  # 1-based


def taper(u):
    return mp.e ** (-(u / SIGMA_U) ** 2 / 2)


def envelope(u, alpha):
    return 4 * taper(u) * mp.cosh(alpha * u)


def literal_cell(delta, alpha):
    return mp.quad(
        lambda u: envelope(u, alpha) * mp.cos(delta * u),
        [-U, U],
    )


def coarse_absolute_upper(alpha):
    return mp.quad(lambda u: envelope(u, alpha), [-U, U])


def phase_sensitive_upper(delta, alpha):
    return mp.quad(
        lambda u: envelope(u, alpha) * max(mp.cos(delta * u), mp.mpf("0")),
        [-U, U],
    )


def main():
    zeros = [mp.im(mp.zetazero(k)) for k in range(1, 16)]
    target = zeros[TARGET_ZERO_INDEX - 1]

    rows = []
    for zero_index in range(TARGET_ZERO_INDEX - 3, TARGET_ZERO_INDEX + 4):
        if zero_index == TARGET_ZERO_INDEX:
            continue
        ordinate = zeros[zero_index - 1]
        delta = ordinate - target
        for alpha in ALPHAS:
            cell = literal_cell(delta, alpha)
            coarse = coarse_absolute_upper(alpha)
            phase_upper = phase_sensitive_upper(delta, alpha)
            rows.append({
                "zero_index": zero_index,
                "target_zero_index": TARGET_ZERO_INDEX,
                "ordinate": str(ordinate),
                "target_ordinate": str(target),
                "delta": str(delta),
                "alpha": str(alpha),
                "literal_cell": str(cell),
                "coarse_absolute_upper": str(coarse),
                "phase_sensitive_upper": str(phase_upper),
                "phase_over_coarse": str(phase_upper / coarse),
                "cell_le_phase_upper": bool(cell <= phase_upper + mp.mpf("1e-35")),
            })

    ratios = [mp.mpf(row["phase_over_coarse"]) for row in rows]
    ratios_sorted = sorted(ratios)
    median = (ratios_sorted[8] + ratios_sorted[9]) / 2

    report = {
        "diagnostic_only": True,
        "same_object_universal_pole_quotient_taper_used": False,
        "actual_riemann_zero_ordinates_used_for_phase_gaps": True,
        "gaussian_taper_sigma": str(SIGMA_U),
        "integration_cutoff": str(U),
        "target_zero_index": TARGET_ZERO_INDEX,
        "target_ordinate": str(target),
        "tested_cells": len(rows),
        "all_one_sided_bounds_hold": all(r["cell_le_phase_upper"] for r in rows),
        "minimum_phase_over_coarse": str(min(ratios)),
        "median_phase_over_coarse": str(median),
        "maximum_phase_over_coarse": str(max(ratios)),
        "rows": rows,
        "boundary": {
            "numeric_diagnostic_is_rh_proof": False,
            "gaussian_taper_is_final_pole_quotient_taper": False,
            "critical_line_zero_data_proves_off_line_case": False,
            "phase_sensitive_majorant_mechanism_exercised": True,
            "same_object_weld_still_required": True,
        },
    }
    Path("riemann_g2_phase_sensitive_near_diagnostic.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps({
        k: report[k]
        for k in (
            "tested_cells",
            "all_one_sided_bounds_hold",
            "minimum_phase_over_coarse",
            "median_phase_over_coarse",
            "maximum_phase_over_coarse",
        )
    }, indent=2))


if __name__ == "__main__":
    main()
