#!/usr/bin/env python3
"""Non-promoting CT18 DY parton-luminosity diagnostic for W4/W5.

This script computes the corrected full-x Drell-Yan parton luminosity

    dL/dtau = int_tau^1 dx/x sum_q e_q^2
        [f_q(x,M) f_qbar(tau/x,M) + f_qbar(x,M) f_q(tau/x,M)]

using LHAPDF ``xfxQ`` values divided by ``x``.  It is diagnostic only: a local
CT18/LHAPDF run is not an accepted or replacement DY luminosity authority.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
from pathlib import Path
from typing import Any


TARGET_T45 = 0.8804486068
DY_LIGHT_FLAVORS = ((2, 4.0 / 9.0), (1, 1.0 / 9.0), (3, 1.0 / 9.0))


def pdf_f(pdf: Any, pid: int, x: float, q: float) -> float:
    return float(pdf.xfxQ(pid, float(x), float(q))) / x


def dy_dluminosity_dtau(
    pdf: Any,
    mass_gev: float,
    *,
    sqrt_s: float = 13_000.0,
    n_x: int = 400,
    x_max: float = 0.999999,
) -> float:
    """Compute full-x charge-weighted DY dL/dtau at Q=M."""

    if n_x < 2:
        raise ValueError("n_x must be at least 2")
    if not 0.0 < x_max < 1.0:
        raise ValueError("x_max must be between 0 and 1")

    tau = (mass_gev / sqrt_s) ** 2
    if not 0.0 < tau < x_max:
        return 0.0

    log_lo = math.log(tau)
    log_hi = math.log(x_max)
    step = (log_hi - log_lo) / (n_x - 1)
    total = 0.0
    for idx in range(n_x):
        x1 = math.exp(log_lo + step * idx)
        x2 = tau / x1
        if not 0.0 < x2 < 1.0:
            continue

        luminosity = 0.0
        for pid, charge_weight in DY_LIGHT_FLAVORS:
            q1 = pdf_f(pdf, pid, x1, mass_gev)
            qb1 = pdf_f(pdf, -pid, x1, mass_gev)
            q2 = pdf_f(pdf, pid, x2, mass_gev)
            qb2 = pdf_f(pdf, -pid, x2, mass_gev)
            luminosity += charge_weight * (q1 * qb2 + qb1 * q2)

        total += (0.5 if idx in (0, n_x - 1) else 1.0) * luminosity

    return total * step


def integrate_mass_window(
    pdf: Any,
    mass_low: float,
    mass_high: float,
    *,
    sqrt_s: float = 13_000.0,
    n_m: int = 160,
    n_x: int = 400,
    measure: str = "dtau",
) -> float:
    """Integrate dL/dtau over a mass window with either dM or dtau measure."""

    if n_m < 2:
        raise ValueError("n_m must be at least 2")
    if mass_low <= 0.0 or mass_high <= mass_low:
        raise ValueError("mass window must satisfy 0 < low < high")
    if measure not in {"dtau", "dM"}:
        raise ValueError("measure must be dtau or dM")

    step = (mass_high - mass_low) / (n_m - 1)
    total = 0.0
    s_hadron = sqrt_s * sqrt_s
    for idx in range(n_m):
        mass = mass_low + step * idx
        value = dy_dluminosity_dtau(pdf, mass, sqrt_s=sqrt_s, n_x=n_x)
        if measure == "dtau":
            value *= 2.0 * mass / s_hadron
        total += (0.5 if idx in (0, n_m - 1) else 1.0) * value
    return total * step


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    try:
        import lhapdf  # type: ignore[import-not-found]
    except ImportError as exc:
        raise RuntimeError(f"Python LHAPDF binding unavailable: {exc}") from exc

    pdf = lhapdf.mkPDF(args.pdf_set, args.member)
    centers = {
        "t43_center_M61_64": dy_dluminosity_dtau(
            pdf, 61.64, sqrt_s=args.sqrt_s, n_x=args.n_x
        ),
        "z_center_M91_2": dy_dluminosity_dtau(pdf, 91.2, sqrt_s=args.sqrt_s, n_x=args.n_x),
        "t45_center_M134_24": dy_dluminosity_dtau(
            pdf, 134.24, sqrt_s=args.sqrt_s, n_x=args.n_x
        ),
    }

    windows_dtau = {
        "L43_50_76": integrate_mass_window(
            pdf, 50.0, 76.0, sqrt_s=args.sqrt_s, n_m=args.n_m, n_x=args.n_x, measure="dtau"
        ),
        "LZ_76_106": integrate_mass_window(
            pdf, 76.0, 106.0, sqrt_s=args.sqrt_s, n_m=args.n_m, n_x=args.n_x, measure="dtau"
        ),
        "L45_106_170": integrate_mass_window(
            pdf,
            106.0,
            170.0,
            sqrt_s=args.sqrt_s,
            n_m=args.n_m,
            n_x=args.n_x,
            measure="dtau",
        ),
    }
    windows_dM = {
        "L43_50_76": integrate_mass_window(
            pdf, 50.0, 76.0, sqrt_s=args.sqrt_s, n_m=args.n_m, n_x=args.n_x, measure="dM"
        ),
        "LZ_76_106": integrate_mass_window(
            pdf, 76.0, 106.0, sqrt_s=args.sqrt_s, n_m=args.n_m, n_x=args.n_x, measure="dM"
        ),
        "L45_106_170": integrate_mass_window(
            pdf,
            106.0,
            170.0,
            sqrt_s=args.sqrt_s,
            n_m=args.n_m,
            n_x=args.n_x,
            measure="dM",
        ),
    }

    dtau_t45_over_z = windows_dtau["L45_106_170"] / windows_dtau["LZ_76_106"]
    dtau_t45_over_t43 = windows_dtau["L45_106_170"] / windows_dtau["L43_50_76"]
    dM_t45_over_z = windows_dM["L45_106_170"] / windows_dM["LZ_76_106"]
    dM_t45_over_t43 = windows_dM["L45_106_170"] / windows_dM["L43_50_76"]
    center_t45_over_z = centers["t45_center_M134_24"] / centers["z_center_M91_2"]
    center_t45_over_t43 = centers["t45_center_M134_24"] / centers["t43_center_M61_64"]
    compared_abs_gap = abs(dtau_t45_over_z - TARGET_T45)
    target_tolerance = 1.0e-10

    return {
        "artifact_schema": "dashi-w4w5-ct18-corrected-dy-luminosity-diagnostic-v1",
        "status": "candidate_diagnostic_non_promoting",
        "accepted_dy_luminosity_convention_status": "candidate_local_ct18nlo_lhapdf_convention_not_accepted",
        "accepted_dy_luminosity_first_missing": "missingAcceptedDYLuminosityConventionAuthority",
        "promotion": {
            "w4": False,
            "w5": False,
            "accepted_dy_convention": False,
            "pdf_carrier": False,
        },
        "pdf_set": args.pdf_set,
        "member": args.member,
        "lhapdf_version": getattr(lhapdf, "version", lambda: None)(),
        "lhapdf_data_path": os.environ.get("LHAPDF_DATA_PATH"),
        "sqrt_s_gev": args.sqrt_s,
        "n_x": args.n_x,
        "n_m": args.n_m,
        "formula": (
            "dL/dtau = integral_tau^1 dx/x sum_q e_q^2 "
            "[fq(x,M) f_qbar(tau/x,M) + f_qbar(x,M) fq(tau/x,M)]"
        ),
        "scale_choice": "Q = M",
        "flavors": [{"pid": pid, "charge_weight": weight} for pid, weight in DY_LIGHT_FLAVORS],
        "target_correction_factor": TARGET_T45,
        "center_dluminosity_dtau": centers,
        "center_ratios": {
            "t45_over_z": center_t45_over_z,
            "t45_over_z_abs_gap": abs(center_t45_over_z - TARGET_T45),
            "t45_over_t43": center_t45_over_t43,
            "t45_over_t43_abs_gap": abs(center_t45_over_t43 - TARGET_T45),
        },
        "mass_window_integral_dtau": windows_dtau,
        "mass_window_integral_dtau_ratios": {
            "t45_over_z": dtau_t45_over_z,
            "t45_over_z_abs_gap": abs(dtau_t45_over_z - TARGET_T45),
            "t45_over_t43": dtau_t45_over_t43,
            "t45_over_t43_abs_gap": abs(dtau_t45_over_t43 - TARGET_T45),
        },
        "mass_window_integral_dM_diagnostic": windows_dM,
        "mass_window_integral_dM_ratios": {
            "t45_over_z": dM_t45_over_z,
            "t45_over_z_abs_gap": abs(dM_t45_over_z - TARGET_T45),
            "t45_over_t43": dM_t45_over_t43,
            "t45_over_t43_abs_gap": abs(dM_t45_over_t43 - TARGET_T45),
        },
        "decision": {
            "compared_ratio": "mass_window_integral_dtau_ratios.t45_over_z",
            "correction_factor": dtau_t45_over_z,
            "target": TARGET_T45,
            "target_tolerance": target_tolerance,
            "abs_gap": compared_abs_gap,
            "matches_target": compared_abs_gap <= target_tolerance,
            "reason": (
                "corrected local CT18 full-x dL/dtau diagnostic does not match the target "
                "and no accepted/replacement DY luminosity authority packet is present"
            ),
        },
        "governance": {
            "diagnostic_only": True,
            "do_not_promote_w4_w5_without_accepted_or_replacement_authority_packet": True,
            "blocker_remains": "missingAcceptedDYLuminosityConventionAuthority",
        },
    }


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf-set", default="CT18NLO")
    parser.add_argument("--member", type=int, default=0)
    parser.add_argument("--sqrt-s", type=float, default=13_000.0)
    parser.add_argument("--n-x", type=int, default=400)
    parser.add_argument("--n-m", type=int, default=160)
    parser.add_argument("--output", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        payload = build_payload(args)
    except (RuntimeError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        return 2

    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
