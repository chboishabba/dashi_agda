#!/usr/bin/env python3
"""Finite-mode physical-real diagnostic for the R650 C1 signed spacetime leaf.

C1 asks for a cutoff-independent bound

    4 * integral_0^T GlobalForcingFull_N(t) dt <= B(T).

The shared R406 evaluator now mirrors the exact R566/R568 instantaneous scalar

    GlobalForcingFull_N
      = sum_k sum_{alpha,beta in fibre(k)}
          K(alpha,beta) Re <G_alpha, D_beta>,

including the diagonal and complete ordered square.

This script evaluates that scalar on saved finite Galerkin states and uses
trapezoidal quadrature along each matched trajectory.  Across a matched-cutoff
manifest it reports the signed integral sequence and basic growth diagnostics.

It does NOT infer a cutoff-uniform theorem from finitely many cutoffs, does NOT
fit/extrapolate a Clay bound, and carries no Agda-kernel/continuum/Clay authority.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import tempfile
from pathlib import Path
from typing import Any

import numpy as np

from ns_r406_physical_real_eval import evaluate_r406

SCRIPT_NAME = "scripts/ns_r650_c1_physical_real_scan.py"
CONTRACT = "ns_r650_c1_physical_real_scan"
ROUTE_DECISION = "FAIL_CLOSED_R650_C1_PHYSICAL_REAL_SCAN"
SCHEMA_VERSION = "1.0.0"

AUTHORITY = {
    "finite_galerkin_diagnostic": True,
    "r568_forcing_full_physical_real_specialization": True,
    "sampled_trapezoid_time_integration": True,
    "finite_cutoff_comparison_only": True,
    "cutoff_uniform_bound_proved": False,
    "formal_rational_helical_same_object": False,
    "exact_time_integral_authority": False,
    "agda_kernel_authority": False,
    "continuum_authority": False,
    "clay_authority": False,
    "promoted": False,
}


def _atomic_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, delete=False
    ) as handle:
        tmp = Path(handle.name)
        json.dump(
            payload,
            handle,
            indent=2 if pretty else None,
            sort_keys=True,
            ensure_ascii=False,
            allow_nan=False,
        )
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(tmp, path)
    finally:
        if tmp.exists():
            tmp.unlink()


def _load_state(path: Path) -> tuple[np.ndarray, float, float | None]:
    with np.load(path, allow_pickle=False) as data:
        raw = np.asarray(data["raw_hat"], dtype=np.complex128)
        nu = float(data["nu"]) if "nu" in data else 1.0e-3
        time = float(data["time"]) if "time" in data else None
    return raw, nu, time


def _trapz(times: list[float], values: list[float]) -> float:
    if len(times) != len(values):
        raise ValueError("times/values length mismatch")
    if len(times) < 2:
        return 0.0
    total = 0.0
    for index in range(len(times) - 1):
        dt = times[index + 1] - times[index]
        if dt < 0.0:
            raise ValueError("trajectory times must be nondecreasing")
        total += 0.5 * dt * (values[index] + values[index + 1])
    return float(total)


def evaluate_state(
    path: Path,
    *,
    formal_cutoff: int | None,
    max_pairs: int,
) -> dict[str, Any]:
    raw, nu, time = _load_state(path)
    grid_n = int(raw.shape[0])
    selected_cutoff = grid_n // 3 if formal_cutoff is None else int(formal_cutoff)

    evaluated = evaluate_r406(
        raw,
        nu=nu,
        formal_cutoff=selected_cutoff,
        max_pairs=max_pairs,
        include_output_rows=False,
    )

    forcing_full = float(evaluated["global_forcing_full"])
    c1_integrand = float(evaluated["c1_instantaneous_four_forcing_full"])
    return {
        "source_state": str(path),
        "time": time,
        "fft_grid": grid_n,
        "formal_cutoff": selected_cutoff,
        "uses_full_alias_safe_cutoff": selected_cutoff == grid_n // 3,
        "viscosity": float(nu),
        "global_forcing_full": forcing_full,
        "c1_integrand_four_forcing_full": c1_integrand,
        "forcing_full_diagonal": float(
            evaluated["global_forcing_full_diagonal"]
        ),
        "forcing_full_offdiagonal": float(
            evaluated["global_forcing_full_offdiagonal"]
        ),
        "offdiagonal_minus_twice_direct_companion": float(
            evaluated["offdiagonal_minus_twice_direct_companion"]
        ),
        "c1_r406_diagonal_coupling_residual": float(
            evaluated["c1_r406_diagonal_coupling_residual"]
        ),
        "r406_weighted_remainder": float(
            evaluated["r406_weighted_remainder"]
        ),
        "evaluated_unordered_pair_count": int(
            evaluated["evaluated_pair_count"]
        ),
        "minimum_pair_rate": evaluated["minimum_pair_rate"],
    }


def _trajectory_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    if not rows:
        raise ValueError("empty trajectory")
    if any(row["time"] is None for row in rows):
        return {
            "integrated": False,
            "reason": "one or more states have no saved time",
        }

    ordered = sorted(rows, key=lambda row: float(row["time"]))
    times = [float(row["time"]) for row in ordered]
    cutoffs = {int(row["formal_cutoff"]) for row in ordered}
    viscosities = {float(row["viscosity"]) for row in ordered}
    if len(cutoffs) != 1:
        raise ValueError("trajectory changes formal cutoff")
    if len(viscosities) != 1:
        raise ValueError("trajectory changes viscosity")

    values = [float(row["c1_integrand_four_forcing_full"]) for row in ordered]
    forcing_values = [float(row["global_forcing_full"]) for row in ordered]
    integral = _trapz(times, values)
    forcing_integral = _trapz(times, forcing_values)

    return {
        "integrated": True,
        "sample_count": len(ordered),
        "initial_time": times[0],
        "terminal_time": times[-1],
        "formal_cutoff": next(iter(cutoffs)),
        "viscosity": next(iter(viscosities)),
        "integrated_four_global_forcing_full_trapezoid": integral,
        "integrated_global_forcing_full_trapezoid": forcing_integral,
        "factor_four_quadrature_residual": float(
            integral - 4.0 * forcing_integral
        ),
        "minimum_instantaneous_c1_integrand": min(values),
        "maximum_instantaneous_c1_integrand": max(values),
        "maximum_absolute_instantaneous_c1_integrand": max(
            abs(value) for value in values
        ),
    }


def _finite_cutoff_summary(runs: list[dict[str, Any]]) -> dict[str, Any]:
    integrated = [
        run
        for run in runs
        if isinstance(run.get("trajectory"), dict)
        and run["trajectory"].get("integrated") is True
    ]
    points = sorted(
        (
            int(run["trajectory"]["formal_cutoff"]),
            float(
                run["trajectory"][
                    "integrated_four_global_forcing_full_trapezoid"
                ]
            ),
        )
        for run in integrated
    )

    successive: list[dict[str, Any]] = []
    for (n0, value0), (n1, value1) in zip(points, points[1:]):
        successive.append(
            {
                "lower_cutoff": n0,
                "upper_cutoff": n1,
                "lower_value": value0,
                "upper_value": value1,
                "signed_difference": value1 - value0,
                "absolute_difference": abs(value1 - value0),
                "absolute_value_ratio": (
                    abs(value1) / abs(value0)
                    if abs(value0) > 1.0e-30
                    else None
                ),
            }
        )

    return {
        "points": [
            {"formal_cutoff": cutoff, "signed_integral": value}
            for cutoff, value in points
        ],
        "successive_cutoff_differences": successive,
        "maximum_observed_signed_integral": (
            max((value for _, value in points), default=None)
        ),
        "maximum_observed_absolute_integral": (
            max((abs(value) for _, value in points), default=None)
        ),
        "finite_sample_supports_uniform_bound_theorem": False,
        "interpretation": (
            "Finite-cutoff telemetry only. Bounded observed values do not "
            "constitute a cutoff-uniform theorem."
        ),
    }


def scan_manifest(
    manifest: Path,
    *,
    formal_cutoff: int | None,
    max_pairs: int,
) -> dict[str, Any]:
    source = json.loads(manifest.read_text(encoding="utf-8"))
    if not isinstance(source, dict) or not isinstance(source.get("runs"), list):
        raise ValueError("manifest must contain a runs list")

    runs_out: list[dict[str, Any]] = []
    for run in source["runs"]:
        if not isinstance(run, dict) or not isinstance(run.get("states"), list):
            continue
        rows = [
            evaluate_state(
                Path(state["source_state"]),
                formal_cutoff=formal_cutoff,
                max_pairs=max_pairs,
            )
            for state in run["states"]
            if isinstance(state, dict)
            and isinstance(state.get("source_state"), str)
        ]
        runs_out.append(
            {
                "trajectory_id": run.get("trajectory_id"),
                "source_grid_cutoff": run.get("cutoff"),
                "rows": rows,
                "trajectory": _trajectory_summary(rows),
            }
        )

    return {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "source_manifest": str(manifest),
        "formal_cutoff_override": formal_cutoff,
        "runs": runs_out,
        "cutoff_comparison": _finite_cutoff_summary(runs_out),
        "formal_theorem_status": (
            "not-proved-finite-cutoff-physical-real-diagnostic-only"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--state", type=Path)
    source.add_argument("--manifest", type=Path)
    parser.add_argument(
        "--formal-cutoff",
        type=int,
        help="default: floor(FFT grid / 3) for each state",
    )
    parser.add_argument("--max-pairs", type=int, default=5_000_000)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    if args.state is not None:
        row = evaluate_state(
            args.state,
            formal_cutoff=args.formal_cutoff,
            max_pairs=int(args.max_pairs),
        )
        payload: dict[str, Any] = {
            "script_name": SCRIPT_NAME,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "authority": AUTHORITY,
            "row": row,
            "formal_theorem_status": (
                "not-proved-finite-cutoff-physical-real-diagnostic-only"
            ),
        }
    else:
        payload = scan_manifest(
            args.manifest,
            formal_cutoff=args.formal_cutoff,
            max_pairs=int(args.max_pairs),
        )

    _atomic_json(args.output_json, payload, bool(args.pretty))
    print(
        json.dumps(
            {
                "output_json": str(args.output_json),
                "contract": CONTRACT,
                "formal_theorem_status": payload["formal_theorem_status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
