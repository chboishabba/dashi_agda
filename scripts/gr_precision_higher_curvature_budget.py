#!/usr/bin/env python3
"""Diagnostic budget for precision-gravity higher-curvature coefficients.

This script is deliberately not a carrier prediction.  It converts external
benchmark bounds into target coefficient scales for a future carrier-derived
effective action

    S_eff = int sqrt(-g) ((R - 2 Lambda)/(16 pi G)
             + alpha1 R^2 + alpha2 R_munu R^munu + ...).

The simple dimensional proxy used here is

    fractional_correction ~= |alpha| / L^2,

so a benchmark bound b at length scale L gives |alpha| <= b L^2 and
sqrt(|alpha|) <= sqrt(b) L.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT_DIR = REPO_ROOT / "scripts" / "data" / "outputs"


@dataclass(frozen=True)
class Benchmark:
    name: str
    observable: str
    bound: float
    scale_m: float
    scale_name: str
    coefficient: str
    note: str


@dataclass(frozen=True)
class BudgetRow:
    name: str
    observable: str
    coefficient: str
    bound: float
    scale_name: str
    scale_m: float
    alpha_bound_m2: float
    sqrt_alpha_bound_m: float
    alpha_bound_over_scale2: float
    promotion_status: str
    note: str


def default_benchmarks() -> list[Benchmark]:
    # External benchmark defaults.  They are configurable inputs, not claims
    # that DASHI derives or updates these experimental limits.
    solar_radius_m = 6.957e8
    earth_radius_m = 6.371e6
    earth_moon_distance_m = 3.844e8

    return [
        Benchmark(
            name="cassini_ppn_gamma_solar_limb",
            observable="PPN gamma fractional deviation",
            bound=2.3e-5,
            scale_m=solar_radius_m,
            scale_name="solar_radius",
            coefficient="alpha1_R2_or_alpha2_Ricci2_proxy",
            note="Cassini-style solar-system PPN gamma benchmark; proxy bound only.",
        ),
        Benchmark(
            name="earth_surface_gravity_fractional",
            observable="fractional Earth weak-field correction",
            bound=1.0e-9,
            scale_m=earth_radius_m,
            scale_name="earth_radius",
            coefficient="alpha1_R2_or_alpha2_Ricci2_proxy",
            note="Engineering target for better-than-baseline Earth gravity correction budget.",
        ),
        Benchmark(
            name="microscope_wep_eta_proxy",
            observable="weak-equivalence-principle eta proxy",
            bound=1.3e-14,
            scale_m=earth_moon_distance_m,
            scale_name="earth_moon_distance",
            coefficient="nonminimal_matter_curvature_proxy",
            note="MICROSCOPE-style WEP benchmark treated as a separate matter-coupling proxy.",
        ),
    ]


def compute_budget(benchmarks: list[Benchmark]) -> list[BudgetRow]:
    rows: list[BudgetRow] = []
    for item in benchmarks:
        alpha_bound = item.bound * item.scale_m * item.scale_m
        rows.append(
            BudgetRow(
                name=item.name,
                observable=item.observable,
                coefficient=item.coefficient,
                bound=item.bound,
                scale_name=item.scale_name,
                scale_m=item.scale_m,
                alpha_bound_m2=alpha_bound,
                sqrt_alpha_bound_m=math.sqrt(alpha_bound),
                alpha_bound_over_scale2=item.bound,
                promotion_status="NO_PROMOTION",
                note=item.note,
            )
        )
    return rows


def write_outputs(rows: list[BudgetRow], output_dir: Path) -> tuple[Path, Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "gr_precision_higher_curvature_budget.json"
    csv_path = output_dir / "gr_precision_higher_curvature_budget.csv"

    payload = {
        "status": "diagnostic_external_benchmark_budget_no_promotion",
        "model": "fractional_correction ~= |alpha| / L^2",
        "carrier_coefficients_derived": False,
        "gravity_prediction_promoted": False,
        "rows": [asdict(row) for row in rows],
    }
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    fieldnames = list(asdict(rows[0]).keys()) if rows else []
    with csv_path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))

    return json_path, csv_path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compute fail-closed precision-gravity coefficient budgets."
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="Directory for JSON/CSV outputs.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    rows = compute_budget(default_benchmarks())
    json_path, csv_path = write_outputs(rows, args.out_dir)
    print(f"wrote {json_path}")
    print(f"wrote {csv_path}")
    for row in rows:
        print(
            f"{row.name}: sqrt_alpha_bound_m={row.sqrt_alpha_bound_m:.6e}, "
            f"alpha_bound_m2={row.alpha_bound_m2:.6e}, "
            f"promotion_status={row.promotion_status}"
        )


if __name__ == "__main__":
    main()
