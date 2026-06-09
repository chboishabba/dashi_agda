#!/usr/bin/env python3
"""NS A6 triadic compensated leakage diagnostic harness.

This pure-stdlib harness models the A6 route at bookkeeping level:

* a localized enstrophy ODE with linear dissipation and superlinear remainder;
* pointwise-to-Abel bias transfer through a small stationarity defect;
* Bony/paraproduct correction at O(N^-1);
* bias-to-dissipation absorption with an O(N^-1/2) stationarity defect;
* assembly of the modeled inequality

    d_t D_r + (eps0/4) * c_lambda * D_r <= C * D_r^(1+alpha).

It is a finite diagnostic/falsification surface only.  It proves no PDE
statement and keeps all promotion flags false.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


DEFAULT_OUTPUT = Path("outputs/ns_a6_triadic_compensated_leakage_harness.json")
LAMBDA_RMS = math.sqrt(11.0 / 60.0)


@dataclass(frozen=True)
class SweepRow:
    profile: str
    n: int
    d_r: float
    eta: float
    c_lrt: float
    epsilon0: float
    alpha: float
    nonlinear_c: float
    c_lambda: float
    linear_target: float
    raw_bias_density: float
    transferred_bias_density: float
    stationarity_defect: float
    abel_transfer_error: float
    bony_correction: float
    localization_error: float
    total_correction: float
    absorption_margin: float
    nonlinear_rhs: float
    modeled_dt_upper: float
    assembled_lhs_minus_rhs: float
    inequality_holds: bool


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="Use a 15s-safe compact sweep.")
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout.")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--big-c", type=float, default=1.0, help="Global correction constant.")
    parser.add_argument(
        "--profiles",
        nargs="*",
        default=None,
        help="Optional subset of profiles: balanced, favorable, stressed, adverse",
    )
    return parser.parse_args()


def profile_specs() -> dict[str, dict[str, float]]:
    return {
        "balanced": {
            "stationarity_const": 0.28,
            "abel_const": 0.18,
            "bony_const": 0.55,
            "localization_const": 0.14,
            "bias_factor": 0.20,
        },
        "favorable": {
            "stationarity_const": 0.20,
            "abel_const": 0.12,
            "bony_const": 0.40,
            "localization_const": 0.10,
            "bias_factor": 0.16,
        },
        "stressed": {
            "stationarity_const": 0.42,
            "abel_const": 0.26,
            "bony_const": 0.75,
            "localization_const": 0.18,
            "bias_factor": 0.24,
        },
        "adverse": {
            "stationarity_const": 0.60,
            "abel_const": 0.34,
            "bony_const": 1.05,
            "localization_const": 0.22,
            "bias_factor": 0.28,
        },
    }


def choose_profiles(args: argparse.Namespace) -> list[str]:
    names = list(profile_specs().keys())
    if not args.profiles:
        return names if not args.quick else ["balanced", "favorable", "stressed"]
    allowed = set(names)
    chosen = []
    for name in args.profiles:
        if name not in allowed:
            raise SystemExit(f"unknown profile: {name}")
        chosen.append(name)
    return chosen


def sweep_values(args: argparse.Namespace) -> dict[str, list[float] | list[int]]:
    if args.quick:
        return {
            "n": [10_000, 100_000, 1_000_000],
            "d_r": [0.0125, 0.025, 0.05],
            "eta": [0.05, 0.10],
            "c_lrt": [0.35, 0.50],
            "epsilon0": [0.20, 0.35],
            "alpha": [0.125, 0.25],
            "nonlinear_c": [1.0, 1.5],
        }
    return {
        "n": [10_000, 100_000, 1_000_000, 10_000_000],
        "d_r": [0.01, 0.02, 0.04, 0.08],
        "eta": [0.02, 0.05, 0.10],
        "c_lrt": [0.25, 0.35, 0.50],
        "epsilon0": [0.15, 0.20, 0.35],
        "alpha": [0.10, 0.125, 0.25],
        "nonlinear_c": [0.75, 1.0, 1.5],
    }


def build_row(
    profile: str,
    spec: dict[str, float],
    n: int,
    d_r: float,
    eta: float,
    c_lrt: float,
    epsilon0: float,
    alpha: float,
    nonlinear_c: float,
    big_c: float,
) -> SweepRow:
    inv_root_n = n ** -0.5
    inv_n = 1.0 / n
    c_lambda = 0.5 * LAMBDA_RMS * c_lrt * c_lrt
    linear_target = 0.25 * epsilon0 * c_lambda

    raw_bias_density = spec["bias_factor"] * c_lambda * eta
    stationarity_defect = big_c * spec["stationarity_const"] * inv_root_n
    abel_transfer_error = big_c * spec["abel_const"] * inv_root_n
    bony_correction = big_c * spec["bony_const"] * inv_n
    localization_error = big_c * spec["localization_const"] * inv_root_n

    transferred_bias_density = max(
        0.0,
        raw_bias_density - stationarity_defect - abel_transfer_error,
    )
    total_correction = (
        stationarity_defect
        + abel_transfer_error
        + bony_correction
        + localization_error
        + transferred_bias_density
    )
    absorption_margin = linear_target - total_correction

    nonlinear_rhs = nonlinear_c * (d_r ** (1.0 + alpha))
    modeled_dt_upper = nonlinear_rhs - absorption_margin * d_r
    assembled_lhs_minus_rhs = absorption_margin * d_r

    return SweepRow(
        profile=profile,
        n=n,
        d_r=d_r,
        eta=eta,
        c_lrt=c_lrt,
        epsilon0=epsilon0,
        alpha=alpha,
        nonlinear_c=nonlinear_c,
        c_lambda=c_lambda,
        linear_target=linear_target,
        raw_bias_density=raw_bias_density,
        transferred_bias_density=transferred_bias_density,
        stationarity_defect=stationarity_defect,
        abel_transfer_error=abel_transfer_error,
        bony_correction=bony_correction,
        localization_error=localization_error,
        total_correction=total_correction,
        absorption_margin=absorption_margin,
        nonlinear_rhs=nonlinear_rhs,
        modeled_dt_upper=modeled_dt_upper,
        assembled_lhs_minus_rhs=assembled_lhs_minus_rhs,
        inequality_holds=absorption_margin >= 0.0,
    )


def run(args: argparse.Namespace) -> dict[str, Any]:
    values = sweep_values(args)
    specs = profile_specs()
    profiles = choose_profiles(args)
    rows: list[SweepRow] = []

    for profile in profiles:
        spec = specs[profile]
        for n in values["n"]:
            for d_r in values["d_r"]:
                for eta in values["eta"]:
                    for c_lrt in values["c_lrt"]:
                        for epsilon0 in values["epsilon0"]:
                            for alpha in values["alpha"]:
                                for nonlinear_c in values["nonlinear_c"]:
                                    rows.append(
                                        build_row(
                                            profile=profile,
                                            spec=spec,
                                            n=n,
                                            d_r=d_r,
                                            eta=eta,
                                            c_lrt=c_lrt,
                                            epsilon0=epsilon0,
                                            alpha=alpha,
                                            nonlinear_c=nonlinear_c,
                                            big_c=args.big_c,
                                        )
                                    )

    passing = [row for row in rows if row.inequality_holds]
    failing = [row for row in rows if not row.inequality_holds]
    rows_by_profile: dict[str, list[SweepRow]] = {name: [] for name in profiles}
    for row in rows:
        rows_by_profile[row.profile].append(row)

    profile_summary: dict[str, Any] = {}
    for profile, prows in rows_by_profile.items():
        profile_summary[profile] = {
            "row_count": len(prows),
            "pass_count": sum(1 for row in prows if row.inequality_holds),
            "fail_count": sum(1 for row in prows if not row.inequality_holds),
            "best_absorption_margin": max(row.absorption_margin for row in prows),
            "worst_absorption_margin": min(row.absorption_margin for row in prows),
            "mean_absorption_margin": sum(row.absorption_margin for row in prows) / len(prows),
            "mean_modeled_dt_upper": sum(row.modeled_dt_upper for row in prows) / len(prows),
        }

    worst_rows = sorted(rows, key=lambda row: row.absorption_margin)[:10]
    best_rows = sorted(rows, key=lambda row: row.absorption_margin, reverse=True)[:10]

    n_thresholds: dict[str, int | None] = {}
    for profile, prows in rows_by_profile.items():
        success_ns = sorted({row.n for row in prows if row.inequality_holds})
        n_thresholds[profile] = success_ns[0] if success_ns else None

    payload = {
        "harness": "ns_a6_triadic_compensated_leakage_harness",
        "scope": "finite_a6_diagnostic_not_pde_proof",
        "model": {
            "equation": "d_t D_r + (eps0/4)*c_lambda*D_r <= C*D_r^(1+alpha)",
            "c_lambda_formula": "0.5*sqrt(11/60)*c_lrt^2",
            "stationarity_rate": "O(N^-1/2)",
            "abel_transfer_rate": "O(N^-1/2)",
            "bony_rate": "O(N^-1)",
            "localization_rate": "O(N^-1/2)",
            "promotion_false": True,
        },
        "sweep": {
            "quick": bool(args.quick),
            "big_c": args.big_c,
            "profiles": profiles,
            "n_values": values["n"],
            "d_r_values": values["d_r"],
            "eta_values": values["eta"],
            "c_lrt_values": values["c_lrt"],
            "epsilon0_values": values["epsilon0"],
            "alpha_values": values["alpha"],
            "nonlinear_c_values": values["nonlinear_c"],
        },
        "summary": {
            "row_count": len(rows),
            "pass_count": len(passing),
            "fail_count": len(failing),
            "pass_fraction": len(passing) / len(rows) if rows else None,
            "best_absorption_margin": max(row.absorption_margin for row in rows) if rows else None,
            "worst_absorption_margin": min(row.absorption_margin for row in rows) if rows else None,
            "min_success_n_by_profile": n_thresholds,
            "profile_summary": profile_summary,
        },
        "extremes": {
            "worst_rows": [asdict(row) for row in worst_rows],
            "best_rows": [asdict(row) for row in best_rows],
        },
        "rows": [asdict(row) for row in rows],
        "promotion": {
            "a6_proved": False,
            "navier_stokes_clay": False,
            "terminal": False,
        },
    }
    return payload


def main() -> int:
    args = parse_args()
    payload = run(args)
    text = json.dumps(payload, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
