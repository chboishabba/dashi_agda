#!/usr/bin/env python3
"""Stress-test the exact R650 C2 production/dissipation currency on finite Galerkin states.

This is a candidate-only, fail-closed numerical research harness.  It uses the
same dealiased Leray-projected Fourier state machinery as the matched Galerkin
trajectory generator, but it adopts the literal Agda dyadic convention

    j(k) = ceil(log2 ||k||_infinity),    w(k) = 2^j(k).

For each state it computes

    W_N       = sum_k w(k) Re <u_k, N_k(u)>,
    P_N'      = 2 W_N,
    D_N'      = sum_k w(k) |k|^2 |u_k|^2,
    S_delta   = P_N' - (2 nu - delta) D_N'.

It also reconstructs the finite Abel layer-cake from shell-total transfers and
checks

    W_N = w_min * totalTransfer + layerCake.

The scan deliberately does NOT evaluate the full R406 Gram/resolvent remainder.
Consequently it cannot prove or disprove R650 C2.  Instead it stress-tests the
strictly stronger "viscosity alone pays the surplus" route and reports the
largest positive margin delta allowed by that strengthening.  A negative margin
capacity is a finite-state counterexample to that strengthening, not to C2.

No theorem, continuum, Clay, or promotion authority is emitted.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import tempfile
from pathlib import Path
from typing import Any, Iterable

import numpy as np

from ns_galerkin_coherence_core import (
    frequency_grid,
    leray_project_hat,
    nonlinear_momentum_components,
)

SCRIPT_NAME = "scripts/ns_r650_quantitative_stress_scan.py"
CONTRACT = "ns_r650_quantitative_stress_scan"
ROUTE_DECISION = "FAIL_CLOSED_R650_QUANTITATIVE_STRESS_SCAN"
SCHEMA_VERSION = "1.0.0"

AUTHORITY = {
    "finite_galerkin_diagnostic": True,
    "literal_max_norm_dyadic_weights": True,
    "r647_abel_identity_numeric_check": True,
    "r406_evaluated": False,
    "c1_evaluated": False,
    "c2_theorem_authority": False,
    "continuum_authority": False,
    "clay_authority": False,
    "promoted": False,
}


def _atomic(path: Path, payload: dict[str, Any], pretty: bool) -> None:
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


def _parse_scales(raw: str) -> tuple[float, ...]:
    scales = tuple(float(item.strip()) for item in raw.split(",") if item.strip())
    if not scales:
        raise ValueError("at least one amplitude scale is required")
    if any((not math.isfinite(value)) or value <= 0.0 for value in scales):
        raise ValueError("amplitude scales must be finite and positive")
    return scales


def _ceil_log2_nonnegative(values: np.ndarray) -> np.ndarray:
    values = np.asarray(values, dtype=np.int64)
    out = np.zeros(values.shape, dtype=np.int64)
    positive = values > 0
    if np.any(positive):
        out[positive] = np.ceil(np.log2(values[positive].astype(np.float64))).astype(np.int64)
    return out


def literal_shell_index(wave: np.ndarray) -> np.ndarray:
    """Agda R647/R646 shell: ceil(log2(max(|kx|,|ky|,|kz|)))."""
    max_norm = np.max(np.abs(wave), axis=-1).astype(np.int64)
    return _ceil_log2_nonnegative(max_norm)


def _nonlinear_hat(
    retained_hat: np.ndarray,
    wave: np.ndarray,
    norm_sq: np.ndarray,
    dealias: np.ndarray,
) -> np.ndarray:
    advective_hat, pressure_hat = nonlinear_momentum_components(
        retained_hat, wave, norm_sq, dealias
    )
    return advective_hat + pressure_hat


def _abel_layer_cake(
    shell_index: np.ndarray,
    transfer_density: np.ndarray,
    active: np.ndarray,
) -> dict[str, Any]:
    shell_values = sorted(int(value) for value in np.unique(shell_index[active]))
    if not shell_values:
        return {
            "shells": [],
            "shell_transfers": [],
            "base_weight": 0.0,
            "total_transfer": 0.0,
            "layer_cake": 0.0,
            "abel_reconstruction": 0.0,
        }

    shell_transfer: dict[int, float] = {}
    for shell in shell_values:
        mask = active & (shell_index == shell)
        shell_transfer[shell] = float(np.sum(transfer_density[mask]))

    total = float(sum(shell_transfer.values()))
    base_weight = float(2 ** shell_values[0])
    layer_cake = 0.0
    for index in range(len(shell_values) - 1):
        left = shell_values[index]
        right = shell_values[index + 1]
        increment = float((2 ** right) - (2 ** left))
        suffix = float(sum(shell_transfer[shell] for shell in shell_values[index + 1 :]))
        layer_cake += increment * suffix

    return {
        "shells": shell_values,
        "shell_transfers": [
            {"shell": shell, "weight": float(2 ** shell), "transfer": shell_transfer[shell]}
            for shell in shell_values
        ],
        "base_weight": base_weight,
        "total_transfer": total,
        "layer_cake": float(layer_cake),
        "abel_reconstruction": float(base_weight * total + layer_cake),
    }


def state_metrics(raw_hat: np.ndarray, nu: float, delta: float) -> dict[str, Any]:
    if raw_hat.ndim != 4 or raw_hat.shape[-1] != 3 or len(set(raw_hat.shape[:3])) != 1:
        raise ValueError(f"expected raw_hat shape (N,N,N,3), got {raw_hat.shape!r}")
    if not math.isfinite(nu) or nu <= 0.0:
        raise ValueError("viscosity must be finite and positive")
    if not math.isfinite(delta):
        raise ValueError("delta must be finite")

    n = int(raw_hat.shape[0])
    wave, norm_sq, _norm, dealias = frequency_grid(n)
    retained_hat = leray_project_hat(
        np.asarray(raw_hat, dtype=np.complex128) * dealias[..., None],
        wave,
        norm_sq,
    )
    nonlinear_hat = _nonlinear_hat(retained_hat, wave, norm_sq, dealias)

    scale = float(n ** 3)
    velocity = retained_hat / scale
    nonlinear = nonlinear_hat / scale
    active = dealias & (norm_sq > 0.0)

    shell = literal_shell_index(wave)
    weight = np.power(2.0, shell, dtype=np.float64)
    transfer_density = np.real(np.sum(np.conjugate(velocity) * nonlinear, axis=-1))
    mode_energy = np.sum(np.abs(velocity) ** 2, axis=-1)

    total_transfer = float(np.sum(transfer_density[active]))
    weighted_transfer = float(np.sum(weight[active] * transfer_density[active]))
    production_rate = float(2.0 * weighted_transfer)
    critical_dissipation_rate = float(
        np.sum(weight[active] * norm_sq[active] * mode_energy[active])
    )
    retained_coefficient = float(2.0 * nu - delta)
    strict_surplus_rate = float(
        production_rate - retained_coefficient * critical_dissipation_rate
    )

    if critical_dissipation_rate > 1.0e-30:
        viscosity_only_margin_capacity = float(
            2.0 * nu - production_rate / critical_dissipation_rate
        )
    else:
        viscosity_only_margin_capacity = None

    abel = _abel_layer_cake(shell, transfer_density, active)
    direct_weighted = weighted_transfer
    abel_residual = abs(direct_weighted - float(abel["abel_reconstruction"]))
    layer_cake_conservative_residual = abs(
        direct_weighted - float(abel["layer_cake"])
    )

    divergence = np.einsum("...i,...i->...", wave, retained_hat)
    reality_residual = float(
        np.max(
            np.abs(
                retained_hat
                - np.conjugate(
                    np.roll(
                        np.roll(
                            np.roll(retained_hat[::-1, ::-1, ::-1], 1, axis=0),
                            1,
                            axis=1,
                        ),
                        1,
                        axis=2,
                    )
                )
            )
        )
    )

    return {
        "cutoff": n,
        "physical_viscosity": float(nu),
        "tested_margin_delta": float(delta),
        "retained_coefficient_2nu_minus_delta": retained_coefficient,
        "literal_unweighted_nonlinear_transfer": total_transfer,
        "literal_weighted_transfer_W": weighted_transfer,
        "literal_critical_production_rate_2W": production_rate,
        "literal_critical_dissipation_rate": critical_dissipation_rate,
        "literal_strict_surplus_rate": strict_surplus_rate,
        "viscosity_only_margin_capacity": viscosity_only_margin_capacity,
        "viscosity_only_positive_margin_exists": (
            viscosity_only_margin_capacity is not None
            and viscosity_only_margin_capacity > 0.0
        ),
        "tested_delta_viscosity_only_absorbs": strict_surplus_rate <= 0.0,
        "abel": abel,
        "abel_identity_absolute_residual": float(abel_residual),
        "conservative_layer_cake_absolute_residual": float(layer_cake_conservative_residual),
        "retained_divergence_max_residual": float(np.max(np.abs(divergence))),
        "reality_max_residual": reality_residual,
        "r406_required_for_actual_c2": True,
        "actual_c2_tested": False,
    }


def _manifest_states(path: Path) -> list[Path]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    states: list[Path] = []
    for run in payload.get("runs", []):
        if not isinstance(run, dict):
            continue
        for row in run.get("states", []):
            if isinstance(row, dict) and isinstance(row.get("source_state"), str):
                states.append(Path(row["source_state"]))
    return states


def _load_state(path: Path) -> tuple[np.ndarray, float, float | None]:
    with np.load(path, allow_pickle=False) as data:
        raw = np.asarray(data["raw_hat"], dtype=np.complex128)
        nu = float(data["nu"]) if "nu" in data else 1.0e-3
        time = float(data["time"]) if "time" in data else None
    return raw, nu, time


def _state_paths(explicit: Iterable[Path], manifest: Path | None) -> list[Path]:
    paths = list(explicit)
    if manifest is not None:
        paths.extend(_manifest_states(manifest))
    seen: set[str] = set()
    unique: list[Path] = []
    for path in paths:
        key = str(path)
        if key not in seen:
            seen.add(key)
            unique.append(path)
    if not unique:
        raise ValueError("provide at least one --state or --manifest")
    return unique


def scan(
    paths: list[Path],
    *,
    delta: float,
    amplitude_scales: tuple[float, ...],
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for path in paths:
        raw, nu, time = _load_state(path)
        for amplitude_scale in amplitude_scales:
            metrics = state_metrics(raw * amplitude_scale, nu, delta)
            metrics.update(
                {
                    "source_state": str(path),
                    "time": time,
                    "amplitude_scale": float(amplitude_scale),
                }
            )
            rows.append(metrics)

    capacities = [
        float(row["viscosity_only_margin_capacity"])
        for row in rows
        if row["viscosity_only_margin_capacity"] is not None
    ]
    failures = [
        row
        for row in rows
        if not bool(row["tested_delta_viscosity_only_absorbs"])
    ]
    negative_capacity = [
        row
        for row in rows
        if row["viscosity_only_margin_capacity"] is not None
        and float(row["viscosity_only_margin_capacity"]) <= 0.0
    ]

    return {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "tested_statement": {
            "diagnostic_strengthening": (
                "2*W_N <= (2*nu-delta)*D'_N, i.e. strict surplus <= 0 without R406"
            ),
            "actual_r650_c2": (
                "integral strict surplus <= integral R406 with delta>0"
            ),
            "actual_r650_c2_evaluated": False,
            "interpretation": (
                "failure rejects only the stronger viscosity-only route; "
                "it does not reject R650 C2"
            ),
        },
        "parameters": {
            "delta": float(delta),
            "amplitude_scales": list(amplitude_scales),
            "state_count": len(paths),
        },
        "rows": rows,
        "aggregate": {
            "row_count": len(rows),
            "viscosity_only_tested_delta_failure_count": len(failures),
            "viscosity_only_nonpositive_margin_capacity_count": len(negative_capacity),
            "minimum_viscosity_only_margin_capacity": min(capacities) if capacities else None,
            "maximum_viscosity_only_margin_capacity": max(capacities) if capacities else None,
            "maximum_abel_identity_absolute_residual": max(
                (float(row["abel_identity_absolute_residual"]) for row in rows),
                default=0.0,
            ),
            "maximum_unweighted_conservation_residual": max(
                (abs(float(row["literal_unweighted_nonlinear_transfer"])) for row in rows),
                default=0.0,
            ),
            "stronger_viscosity_only_route_survived_scan": len(failures) == 0,
            "actual_c2_status": "not-tested-r406-evaluator-required",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, action="append", default=[])
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--delta", type=float, default=0.0)
    parser.add_argument(
        "--amplitude-scales",
        default="1",
        help="comma-separated positive multipliers applied to each Fourier state",
    )
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    paths = _state_paths(args.state, args.manifest)
    scales = _parse_scales(args.amplitude_scales)
    payload = scan(paths, delta=args.delta, amplitude_scales=scales)
    _atomic(args.output_json, payload, args.pretty)
    print(
        json.dumps(
            {
                "output_json": str(args.output_json),
                "row_count": payload["aggregate"]["row_count"],
                "viscosity_only_tested_delta_failure_count": payload["aggregate"][
                    "viscosity_only_tested_delta_failure_count"
                ],
                "minimum_viscosity_only_margin_capacity": payload["aggregate"][
                    "minimum_viscosity_only_margin_capacity"
                ],
                "actual_c2_status": payload["aggregate"]["actual_c2_status"],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
