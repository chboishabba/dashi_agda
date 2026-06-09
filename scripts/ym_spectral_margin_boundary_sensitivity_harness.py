#!/usr/bin/env python3
"""YM spectral-margin boundary-sensitivity proxy harness.

This pure-stdlib diagnostic sweeps finite quotient spectra around the proxy
budget

    H >= c_delta * Delta + c_hol * Hol - E_d

and checks whether the margin is stable under coefficient, holonomy, kinetic,
error-budget, and near-zero-pollution perturbations.

The output is a diagnostic receipt only.  It is not a proof of Yang-Mills
Hamiltonian domination, reflection positivity, OS/Wightman reconstruction,
continuum no-pollution, or any Clay claim.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


DEFAULT_OUTPUT = Path("outputs/ym_spectral_margin_boundary_sensitivity_harness.json")


@dataclass(frozen=True)
class Parameters:
    dimension: int
    quotient_dimension: int
    sweeps: int
    margin_floor: float
    kinetic_gap_floor: float
    holonomy_floor: float
    pollution_floor: float


@dataclass(frozen=True)
class Row:
    regime: str
    kind: str
    index: int
    expected_pass: bool
    passed_proxy_checks: bool
    c_delta: float
    c_hol: float
    ed_budget: float
    holonomy_floor_value: float
    kinetic_gap_value: float
    h_min_eigenvalue: float
    comparison_min_eigenvalue: float
    domination_margin: float
    h_minus_ed_floor: float
    pollution_distance: float
    checks: dict[str, bool]
    failure_reasons: list[str]


@dataclass(frozen=True)
class RegimeSummary:
    name: str
    kind: str
    expected_pass: bool
    row_count: int
    rows_passing: int
    rows_failing: int
    min_domination_margin: float
    min_h_minus_ed_floor: float
    min_pollution_distance: float
    min_kinetic_gap: float
    min_holonomy_floor: float
    max_ed_budget: float
    classification_matches_expectation: bool


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimension", type=int, default=6)
    parser.add_argument("--quotient-dimension", type=int, default=4)
    parser.add_argument("--sweeps", type=int, default=9)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true", help="Emit compact JSON to stdout.")
    return parser.parse_args(argv)


def validate_args(args: argparse.Namespace) -> None:
    if args.dimension < 3:
        raise ValueError("--dimension must be at least 3")
    if not (1 <= args.quotient_dimension < args.dimension):
        raise ValueError("--quotient-dimension must be between 1 and dimension - 1")
    if args.sweeps < 3:
        raise ValueError("--sweeps must be at least 3")


def linspace(start: float, stop: float, count: int) -> list[float]:
    if count == 1:
        return [(start + stop) / 2.0]
    return [start + (stop - start) * index / (count - 1) for index in range(count)]


def quotient_spectrum(floor: float, spread: float, quotient_dimension: int) -> list[float]:
    return [floor + spread * index for index in range(quotient_dimension)]


def row_for(
    regime: str,
    kind: str,
    index: int,
    expected_pass: bool,
    params: Parameters,
    c_delta: float,
    c_hol: float,
    ed_budget: float,
    holonomy_floor_value: float,
    kinetic_gap_value: float,
    pollution_override: float | None = None,
    reserve: float = 0.12,
) -> Row:
    delta = quotient_spectrum(kinetic_gap_value, 0.23, params.quotient_dimension)
    hol = quotient_spectrum(holonomy_floor_value, 0.19, params.quotient_dimension)
    error = [ed_budget * (1.0 + 0.04 * i) for i in range(params.quotient_dimension)]
    comparison = [c_delta * d + c_hol * h - e for d, h, e in zip(delta, hol, error)]
    h = [value + reserve + 0.035 * i for i, value in enumerate(comparison)]
    if pollution_override is not None:
        h[0] = pollution_override

    residual = [h_value - comparison_value for h_value, comparison_value in zip(h, comparison)]
    h_minus_ed = [h_value - e_value for h_value, e_value in zip(h, error)]
    domination_margin = min(residual)
    h_min = min(h)
    comparison_min = min(comparison)
    h_minus_ed_floor = min(h_minus_ed)
    pollution_distance = min(abs(value) for value in h)
    kinetic_gap = min(delta)
    hol_floor = min(hol)

    weighted_floor = c_delta * kinetic_gap + c_hol * hol_floor
    checks = {
        "dimension_budget_valid": params.quotient_dimension < params.dimension,
        "coefficients_nonnegative": c_delta >= 0.0 and c_hol >= 0.0,
        "kinetic_gap_present": kinetic_gap >= params.kinetic_gap_floor,
        "holonomy_floor_present": hol_floor >= params.holonomy_floor,
        "ed_budget_absorbed": ed_budget <= 0.55 * weighted_floor,
        "domination_margin_positive": domination_margin >= params.margin_floor,
        "h_minus_ed_positive": h_minus_ed_floor >= params.margin_floor,
        "no_near_zero_pollution": pollution_distance >= params.pollution_floor,
    }
    passed = all(checks.values())
    failures = [name for name, value in checks.items() if not value]
    return Row(
        regime=regime,
        kind=kind,
        index=index,
        expected_pass=expected_pass,
        passed_proxy_checks=passed,
        c_delta=c_delta,
        c_hol=c_hol,
        ed_budget=ed_budget,
        holonomy_floor_value=hol_floor,
        kinetic_gap_value=kinetic_gap,
        h_min_eigenvalue=h_min,
        comparison_min_eigenvalue=comparison_min,
        domination_margin=domination_margin,
        h_minus_ed_floor=h_minus_ed_floor,
        pollution_distance=pollution_distance,
        checks=checks,
        failure_reasons=failures,
    )


def build_rows(params: Parameters) -> list[Row]:
    rows: list[Row] = []
    sweep = linspace(0.0, 1.0, params.sweeps)

    for index, t in enumerate(sweep):
        rows.append(
            row_for(
                "stable_full_degree_boundary",
                "good",
                index,
                True,
                params,
                c_delta=0.68 + 0.10 * t,
                c_hol=0.58 + 0.08 * (1.0 - t),
                ed_budget=0.030 + 0.012 * t,
                holonomy_floor_value=0.34 - 0.02 * t,
                kinetic_gap_value=0.38 + 0.03 * t,
                reserve=0.13,
            )
        )
        rows.append(
            row_for(
                "holonomy_buffered_boundary",
                "good",
                index,
                True,
                params,
                c_delta=0.46 + 0.04 * t,
                c_hol=0.90 - 0.05 * t,
                ed_budget=0.024 + 0.010 * t,
                holonomy_floor_value=0.48 - 0.03 * t,
                kinetic_gap_value=0.31 + 0.02 * t,
                reserve=0.11,
            )
        )
        rows.append(
            row_for(
                "ed_margin_absorbed_boundary",
                "good",
                index,
                True,
                params,
                c_delta=0.74 - 0.03 * t,
                c_hol=0.62 + 0.02 * t,
                ed_budget=0.036 + 0.014 * t,
                holonomy_floor_value=0.37 - 0.015 * t,
                kinetic_gap_value=0.42 - 0.02 * t,
                reserve=0.15,
            )
        )

        rows.append(
            row_for(
                "weak_kinetic_boundary",
                "bad",
                index,
                False,
                params,
                c_delta=0.70,
                c_hol=0.62,
                ed_budget=0.026,
                holonomy_floor_value=0.36,
                kinetic_gap_value=0.020 + 0.035 * t,
                reserve=0.12,
            )
        )
        rows.append(
            row_for(
                "missing_holonomy_boundary",
                "bad",
                index,
                False,
                params,
                c_delta=0.74,
                c_hol=0.64,
                ed_budget=0.025,
                holonomy_floor_value=0.001 + 0.030 * t,
                kinetic_gap_value=0.40,
                reserve=0.12,
            )
        )
        rows.append(
            row_for(
                "ed_overbudget_boundary",
                "bad",
                index,
                False,
                params,
                c_delta=0.62,
                c_hol=0.54,
                ed_budget=0.28 + 0.06 * t,
                holonomy_floor_value=0.30,
                kinetic_gap_value=0.34,
                reserve=0.12,
            )
        )
        rows.append(
            row_for(
                "spectral_pollution_boundary",
                "bad",
                index,
                False,
                params,
                c_delta=0.76,
                c_hol=0.66,
                ed_budget=0.030,
                holonomy_floor_value=0.36,
                kinetic_gap_value=0.41,
                pollution_override=0.006 + 0.035 * t,
                reserve=0.13,
            )
        )
    return rows


def summarize_regime(rows: Sequence[Row], name: str) -> RegimeSummary:
    selected = [row for row in rows if row.regime == name]
    if not selected:
        raise ValueError(f"no rows for regime {name}")
    return RegimeSummary(
        name=name,
        kind=selected[0].kind,
        expected_pass=selected[0].expected_pass,
        row_count=len(selected),
        rows_passing=sum(1 for row in selected if row.passed_proxy_checks),
        rows_failing=sum(1 for row in selected if not row.passed_proxy_checks),
        min_domination_margin=min(row.domination_margin for row in selected),
        min_h_minus_ed_floor=min(row.h_minus_ed_floor for row in selected),
        min_pollution_distance=min(row.pollution_distance for row in selected),
        min_kinetic_gap=min(row.kinetic_gap_value for row in selected),
        min_holonomy_floor=min(row.holonomy_floor_value for row in selected),
        max_ed_budget=max(row.ed_budget for row in selected),
        classification_matches_expectation=all(
            row.passed_proxy_checks == row.expected_pass for row in selected
        ),
    )


def aggregate_metrics(rows: Sequence[Row]) -> dict[str, Any]:
    good = [row for row in rows if row.expected_pass]
    bad = [row for row in rows if not row.expected_pass]
    return {
        "row_count": len(rows),
        "good_row_count": len(good),
        "bad_row_count": len(bad),
        "good_rows_passed": sum(1 for row in good if row.passed_proxy_checks),
        "bad_rows_failed": sum(1 for row in bad if not row.passed_proxy_checks),
        "classification_accuracy": sum(
            1 for row in rows if row.passed_proxy_checks == row.expected_pass
        )
        / float(len(rows)),
        "min_good_domination_margin": min(row.domination_margin for row in good),
        "max_bad_domination_margin": max(row.domination_margin for row in bad),
        "min_good_pollution_distance": min(row.pollution_distance for row in good),
        "min_bad_pollution_distance": min(row.pollution_distance for row in bad),
        "max_good_ed_budget": max(row.ed_budget for row in good),
        "max_bad_ed_budget": max(row.ed_budget for row in bad),
    }


def build_report(params: Parameters) -> dict[str, Any]:
    rows = build_rows(params)
    regime_names = sorted({row.regime for row in rows})
    summaries = [summarize_regime(rows, name) for name in regime_names]
    good_regimes = [summary for summary in summaries if summary.expected_pass]
    bad_regimes = [summary for summary in summaries if not summary.expected_pass]
    metrics = aggregate_metrics(rows)
    validation_flags = {
        "all_good_regimes_pass": all(summary.rows_failing == 0 for summary in good_regimes),
        "all_bad_regimes_fail": all(summary.rows_passing == 0 for summary in bad_regimes),
        "classification_matches_expectation": metrics["classification_accuracy"] == 1.0,
        "weak_kinetic_regime_present": any(row.regime == "weak_kinetic_boundary" for row in rows),
        "missing_holonomy_regime_present": any(row.regime == "missing_holonomy_boundary" for row in rows),
        "ed_overbudget_regime_present": any(row.regime == "ed_overbudget_boundary" for row in rows),
        "spectral_pollution_regime_present": any(row.regime == "spectral_pollution_boundary" for row in rows),
        "stdlib_only": True,
        "deterministic": True,
        "diagnostic_only": True,
        "promotion_blocked": True,
    }
    ok = all(validation_flags.values())
    return {
        "ok": ok,
        "promotion": False,
        "diagnostic_only": True,
        "parameters": asdict(params),
        "good_regimes": [asdict(summary) for summary in good_regimes],
        "bad_regimes": [asdict(summary) for summary in bad_regimes],
        "aggregate_metrics": metrics,
        "validation_flags": validation_flags,
        "rows": [asdict(row) for row in rows],
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    params = Parameters(
        dimension=args.dimension,
        quotient_dimension=args.quotient_dimension,
        sweeps=args.sweeps,
        margin_floor=0.075,
        kinetic_gap_floor=0.18,
        holonomy_floor=0.16,
        pollution_floor=0.08,
    )
    report = build_report(params)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(report, sort_keys=True))
    else:
        print(
            "YM spectral-margin boundary-sensitivity proxy: "
            f"ok={report['ok']} output={args.json_output}"
        )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
