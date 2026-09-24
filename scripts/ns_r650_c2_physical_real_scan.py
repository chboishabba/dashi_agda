#!/usr/bin/env python3
"""Direct finite-mode diagnostic for the R650 C2 strict-margin inequality.

This combines the literal max-norm dyadic critical production/dissipation
currency with the physical-real R496/R499 R406 direct-companion evaluator.

At one state:

    P'(t) = 2 W(t)
    D'(t) = critical dissipation rate
    R(t)  = physical-real R406 weighted remainder

and the R650 pointwise strengthening is

    P'(t) - (2 nu - delta) D'(t) <= R(t).

When D'(t)>0, the largest delta allowed pointwise is

    delta_max(t) = 2 nu + (R(t)-P'(t))/D'(t).

For a saved trajectory, trapezoidal quadrature gives the analogous diagnostic

    delta_max[0,T]
      = 2 nu + (int R - int P') / int D'.

The actual formal C2 theorem is an exact time-integrated statement on the
literal R408/R406 trajectory.  This script is finite floating telemetry:
- the helical scalar is the intended Euclidean real specialization;
- saved-state integration is trapezoidal;
- no theorem, continuum, or Clay authority is emitted.
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

from ns_r406_physical_real_eval import (
    AUTHORITY as R406_AUTHORITY,
    evaluate_r406,
    nonzero_cutoff_modes,
    projected_state,
    _mode_value,
)
from ns_r650_quantitative_stress_scan import literal_shell_index
from ns_galerkin_coherence_core import frequency_grid

SCRIPT_NAME = "scripts/ns_r650_c2_physical_real_scan.py"
CONTRACT = "ns_r650_c2_physical_real_scan"
ROUTE_DECISION = "FAIL_CLOSED_R650_C2_PHYSICAL_REAL_SCAN"
SCHEMA_VERSION = "1.0.0"

AUTHORITY = {
    "finite_galerkin_diagnostic": True,
    "literal_r650_currency": True,
    "r406_physical_real_specialization": True,
    "sampled_trapezoid_time_integration": True,
    "formal_rational_helical_same_object": False,
    "exact_time_integral_authority": False,
    "agda_kernel_authority": False,
    "continuum_authority": False,
    "clay_authority": False,
    "promoted": False,
}


def _atomic_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=path.parent, delete=False) as handle:
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


def _shell_index_mode(mode: tuple[int, int, int]) -> int:
    m = max(abs(mode[0]), abs(mode[1]), abs(mode[2]))
    if m <= 1:
        return 0
    return int(math.ceil(math.log2(float(m))))


def _critical_currency(
    raw_hat: np.ndarray,
    *,
    nu: float,
    formal_cutoff: int,
) -> dict[str, float]:
    retained_raw, forcing_raw, _meta = projected_state(raw_hat, formal_cutoff)
    n = int(raw_hat.shape[0])
    scale = float(n ** 3)
    velocity = retained_raw / scale
    forcing = forcing_raw / scale

    weighted_transfer = 0.0
    dissipation = 0.0
    unweighted_transfer = 0.0
    for mode in nonzero_cutoff_modes(formal_cutoff):
        u = _mode_value(velocity, mode)
        f = _mode_value(forcing, mode)
        pairing = float(np.real(np.vdot(u, f)))
        weight = float(2 ** _shell_index_mode(mode))
        k2 = float(mode[0] * mode[0] + mode[1] * mode[1] + mode[2] * mode[2])
        unweighted_transfer += pairing
        weighted_transfer += weight * pairing
        dissipation += weight * k2 * float(np.real(np.vdot(u, u)))

    return {
        "unweighted_transfer": float(unweighted_transfer),
        "weighted_transfer_W": float(weighted_transfer),
        "production_rate_2W": float(2.0 * weighted_transfer),
        "critical_dissipation_rate": float(dissipation),
        "viscosity": float(nu),
    }


def evaluate_state(
    path: Path,
    *,
    formal_cutoff: int | None,
    delta: float,
    max_pairs: int,
) -> dict[str, Any]:
    raw, nu, time = _load_state(path)
    grid_n = int(raw.shape[0])
    selected_cutoff = grid_n // 3 if formal_cutoff is None else int(formal_cutoff)

    currency = _critical_currency(raw, nu=nu, formal_cutoff=selected_cutoff)
    r406 = evaluate_r406(
        raw,
        nu=nu,
        formal_cutoff=selected_cutoff,
        max_pairs=max_pairs,
        include_output_rows=False,
    )

    production = float(currency["production_rate_2W"])
    dissipation = float(currency["critical_dissipation_rate"])
    remainder = float(r406["r406_weighted_remainder"])
    strict_surplus = production - (2.0 * nu - delta) * dissipation
    gap = remainder - strict_surplus

    if dissipation > 1.0e-30:
        margin_capacity = 2.0 * nu + (remainder - production) / dissipation
    else:
        margin_capacity = None

    return {
        "source_state": str(path),
        "time": time,
        "fft_grid": grid_n,
        "formal_cutoff": selected_cutoff,
        "uses_full_alias_safe_cutoff": selected_cutoff == grid_n // 3,
        "viscosity": float(nu),
        "tested_delta": float(delta),
        **currency,
        "r406_weighted_remainder": remainder,
        "strict_surplus_rate": float(strict_surplus),
        "r406_minus_strict_surplus": float(gap),
        "tested_delta_pointwise_c2_strengthening_holds": gap >= 0.0,
        "pointwise_margin_capacity": (
            float(margin_capacity) if margin_capacity is not None else None
        ),
        "positive_pointwise_margin_available": (
            margin_capacity is not None and margin_capacity > 0.0
        ),
        "unweighted_conservation_residual": abs(float(currency["unweighted_transfer"])),
        "r406_evaluated_pair_count": int(r406["evaluated_pair_count"]),
        "r406_minimum_pair_rate": r406["minimum_pair_rate"],
        "r406_authority": R406_AUTHORITY,
    }


def _trapz(times: list[float], values: list[float]) -> float:
    if len(times) != len(values):
        raise ValueError("times/values length mismatch")
    if len(times) < 2:
        return 0.0
    total = 0.0
    for i in range(len(times) - 1):
        dt = times[i + 1] - times[i]
        if dt < 0.0:
            raise ValueError("trajectory times must be nondecreasing")
        total += 0.5 * dt * (values[i] + values[i + 1])
    return float(total)


def _trajectory_summary(rows: list[dict[str, Any]], delta: float) -> dict[str, Any]:
    if not rows:
        raise ValueError("empty trajectory")
    if any(row["time"] is None for row in rows):
        return {
            "integrated": False,
            "reason": "one or more states have no saved time",
        }

    ordered = sorted(rows, key=lambda row: float(row["time"]))
    times = [float(row["time"]) for row in ordered]
    viscosities = {float(row["viscosity"]) for row in ordered}
    cutoffs = {int(row["formal_cutoff"]) for row in ordered}
    if len(viscosities) != 1:
        raise ValueError("trajectory changes viscosity")
    if len(cutoffs) != 1:
        raise ValueError("trajectory changes formal cutoff")

    nu = next(iter(viscosities))
    p_int = _trapz(times, [float(row["production_rate_2W"]) for row in ordered])
    d_int = _trapz(times, [float(row["critical_dissipation_rate"]) for row in ordered])
    r_int = _trapz(times, [float(row["r406_weighted_remainder"]) for row in ordered])
    surplus_int = p_int - (2.0 * nu - delta) * d_int
    gap_int = r_int - surplus_int

    if d_int > 1.0e-30:
        margin_capacity = 2.0 * nu + (r_int - p_int) / d_int
    else:
        margin_capacity = None

    return {
        "integrated": True,
        "sample_count": len(ordered),
        "initial_time": times[0],
        "terminal_time": times[-1],
        "viscosity": nu,
        "formal_cutoff": next(iter(cutoffs)),
        "tested_delta": float(delta),
        "integrated_production_trapezoid": p_int,
        "integrated_dissipation_trapezoid": d_int,
        "integrated_r406_trapezoid": r_int,
        "integrated_strict_surplus_trapezoid": float(surplus_int),
        "integrated_r406_minus_surplus_trapezoid": float(gap_int),
        "tested_delta_integrated_c2_diagnostic_holds": gap_int >= 0.0,
        "integrated_margin_capacity": (
            float(margin_capacity) if margin_capacity is not None else None
        ),
        "positive_integrated_margin_available": (
            margin_capacity is not None and margin_capacity > 0.0
        ),
        "pointwise_failure_count": sum(
            1
            for row in ordered
            if not bool(row["tested_delta_pointwise_c2_strengthening_holds"])
        ),
        "minimum_pointwise_margin_capacity": min(
            (
                float(row["pointwise_margin_capacity"])
                for row in ordered
                if row["pointwise_margin_capacity"] is not None
            ),
            default=None,
        ),
    }


def scan_manifest(
    manifest: Path,
    *,
    formal_cutoff: int | None,
    delta: float,
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
                delta=delta,
                max_pairs=max_pairs,
            )
            for state in run["states"]
            if isinstance(state, dict) and isinstance(state.get("source_state"), str)
        ]
        runs_out.append(
            {
                "trajectory_id": run.get("trajectory_id"),
                "source_grid_cutoff": run.get("cutoff"),
                "rows": rows,
                "trajectory": _trajectory_summary(rows, delta),
            }
        )

    return {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "source_manifest": str(manifest),
        "tested_delta": float(delta),
        "formal_cutoff_override": formal_cutoff,
        "runs": runs_out,
        "aggregate": {
            "run_count": len(runs_out),
            "state_count": sum(len(run["rows"]) for run in runs_out),
            "positive_integrated_margin_run_count": sum(
                1
                for run in runs_out
                if run["trajectory"].get("positive_integrated_margin_available") is True
            ),
            "integrated_diagnostic_failure_count": sum(
                1
                for run in runs_out
                if run["trajectory"].get("integrated") is True
                and run["trajectory"].get("tested_delta_integrated_c2_diagnostic_holds")
                is False
            ),
            "formal_theorem_status": "not-proved-numerical-physical-real-diagnostic-only",
        },
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
    parser.add_argument("--delta", type=float, default=0.0)
    parser.add_argument("--max-pairs", type=int, default=5_000_000)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    if args.state is not None:
        row = evaluate_state(
            args.state,
            formal_cutoff=args.formal_cutoff,
            delta=float(args.delta),
            max_pairs=int(args.max_pairs),
        )
        payload: dict[str, Any] = {
            "script_name": SCRIPT_NAME,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "authority": AUTHORITY,
            "row": row,
            "formal_theorem_status": "not-proved-numerical-physical-real-diagnostic-only",
        }
    else:
        payload = scan_manifest(
            args.manifest,
            formal_cutoff=args.formal_cutoff,
            delta=float(args.delta),
            max_pairs=int(args.max_pairs),
        )

    _atomic_json(args.output_json, payload, bool(args.pretty))
    print(
        json.dumps(
            {
                "output_json": str(args.output_json),
                "contract": CONTRACT,
                "formal_theorem_status": payload.get(
                    "formal_theorem_status",
                    payload.get("aggregate", {}).get("formal_theorem_status"),
                ),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
