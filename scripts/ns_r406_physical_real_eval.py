#!/usr/bin/env python3
"""Evaluate the R496/R499 direct-companion formula on a finite Fourier state.

This is a numerical physical-real specialization of the literal R406 direct
companion, intended for theorem-search telemetry.

Formal correspondence
---------------------
For each nonzero output k in the literal cutoff cube, enumerate ordered
incidences tau=(p,q,k) with p+q=k and p,q in the same cube. With the intended
Euclidean helical realization

    P_±(k)v = 1/2 [ P_k v ± |k|^{-1} i k×v ],

define the R225/R387 double-mixed cell

    D_tau = 2 A_tau + 2 A_swap(tau),
    A_tau = P_+(p)u_p × P_-(q)u_q,

and the R388 double forcing

    G_tau = 2 F_tau + 2 F_swap(tau),

where

    F_tau = P_+(p)N_p × P_-(q)u_q
          + P_+(p)u_p × P_-(q)N_q.

The cell rate is

    lambda_tau = nu (|p|^2 + |q|^2).

For unordered list-position pairs alpha<beta in one output fibre, R496's direct
companion contribution is

    C_ab = 1/2 * 1/(lambda_a+lambda_b)
           * [ Re<G_a,D_b> + Re<D_a,G_b> ].

R499 identifies the instantaneous literal R406 weighted remainder with

    R406 = 4 * sum_k sum_{a<b in fibre(k)} C_ab.

Trust boundary
--------------
The Agda chain parameterizes HelicalModeScalars over an exact rational field.
Generic Euclidean |k| is not rational. This script instantiates the physically
intended real values |k|, 1/|k|, 1/2 in floating arithmetic. Therefore it is
NOT an exact inhabitant of the rational Agda parameter, NOT theorem authority,
and NOT Clay authority. It is a semantics-faithful physical-real diagnostic.

The evaluator is combinatorial (unordered pairs inside every output fibre).
Use a small --formal-cutoff; an explicit --max-pairs guard refuses large jobs
rather than silently changing the carrier.
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

from ns_galerkin_coherence_core import (
    frequency_grid,
    leray_project_hat,
    nonlinear_momentum_components,
)

SCRIPT_NAME = "scripts/ns_r406_physical_real_eval.py"
CONTRACT = "ns_r406_physical_real_eval"
ROUTE_DECISION = "FAIL_CLOSED_R406_PHYSICAL_REAL_DIAGNOSTIC"
SCHEMA_VERSION = "1.0.0"

AUTHORITY = {
    "finite_galerkin_diagnostic": True,
    "r496_direct_companion_formula_mirrored": True,
    "r499_factor_four_formula_mirrored": True,
    "physical_euclidean_helical_specialization": True,
    "formal_rational_helical_same_object": False,
    "agda_kernel_authority": False,
    "continuum_authority": False,
    "clay_authority": False,
    "promoted": False,
}

Mode = tuple[int, int, int]


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


def _mode_norm_sq(mode: Mode) -> float:
    x, y, z = mode
    return float(x * x + y * y + z * z)


def _in_cube(mode: Mode, cutoff: int) -> bool:
    return max(abs(mode[0]), abs(mode[1]), abs(mode[2])) <= cutoff


def _sub_mode(left: Mode, right: Mode) -> Mode:
    return (
        left[0] - right[0],
        left[1] - right[1],
        left[2] - right[2],
    )


def cutoff_modes(cutoff: int) -> list[Mode]:
    if cutoff < 0:
        raise ValueError("cutoff must be nonnegative")
    return [
        (x, y, z)
        for x in range(-cutoff, cutoff + 1)
        for y in range(-cutoff, cutoff + 1)
        for z in range(-cutoff, cutoff + 1)
    ]


def nonzero_cutoff_modes(cutoff: int) -> list[Mode]:
    return [mode for mode in cutoff_modes(cutoff) if mode != (0, 0, 0)]


def output_fibre(cutoff: int, output: Mode) -> list[tuple[Mode, Mode]]:
    result: list[tuple[Mode, Mode]] = []
    for p in cutoff_modes(cutoff):
        q = _sub_mode(output, p)
        if _in_cube(q, cutoff):
            result.append((p, q))
    return result


def global_pair_count(cutoff: int) -> tuple[int, list[dict[str, Any]]]:
    rows: list[dict[str, Any]] = []
    total = 0
    for output in nonzero_cutoff_modes(cutoff):
        m = len(output_fibre(cutoff, output))
        pairs = m * (m - 1) // 2
        total += pairs
        rows.append(
            {
                "output": list(output),
                "incidence_count": m,
                "unordered_pair_count": pairs,
            }
        )
    return total, rows


def _mode_value(array: np.ndarray, mode: Mode) -> np.ndarray:
    n = int(array.shape[0])
    x, y, z = mode
    return np.asarray(array[z % n, y % n, x % n], dtype=np.complex128)


def _leray_vector(mode: Mode, value: np.ndarray) -> np.ndarray:
    k = np.asarray(mode, dtype=np.float64)
    k2 = float(np.dot(k, k))
    if k2 == 0.0:
        return np.zeros(3, dtype=np.complex128)
    return value - k * (np.dot(k, value) / k2)


def _curl_symbol(mode: Mode, value: np.ndarray) -> np.ndarray:
    k = np.asarray(mode, dtype=np.float64)
    return 1j * np.cross(k, value)


def helical_project(mode: Mode, value: np.ndarray, sign: int) -> np.ndarray:
    if sign not in (-1, 1):
        raise ValueError("helical sign must be +1 or -1")
    k2 = _mode_norm_sq(mode)
    projected = _leray_vector(mode, value)
    if k2 == 0.0:
        return 0.5 * projected
    normalized_curl = _curl_symbol(mode, value) / math.sqrt(k2)
    return 0.5 * (projected + float(sign) * normalized_curl)


def _real_hermitian_cross(left: np.ndarray, right: np.ndarray) -> float:
    return float(np.real(np.vdot(left, right)))


def _mixed_plus_minus(
    p: Mode,
    q: Mode,
    velocity_hat: np.ndarray,
) -> np.ndarray:
    return np.cross(
        helical_project(p, _mode_value(velocity_hat, p), +1),
        helical_project(q, _mode_value(velocity_hat, q), -1),
    )


def _product_rule_forcing(
    p: Mode,
    q: Mode,
    velocity_hat: np.ndarray,
    forcing_hat: np.ndarray,
) -> np.ndarray:
    up = helical_project(p, _mode_value(velocity_hat, p), +1)
    uq = helical_project(q, _mode_value(velocity_hat, q), -1)
    fp = helical_project(p, _mode_value(forcing_hat, p), +1)
    fq = helical_project(q, _mode_value(forcing_hat, q), -1)
    return np.cross(fp, uq) + np.cross(up, fq)


def _double_cell(
    p: Mode,
    q: Mode,
    velocity_hat: np.ndarray,
) -> np.ndarray:
    return (
        2.0 * _mixed_plus_minus(p, q, velocity_hat)
        + 2.0 * _mixed_plus_minus(q, p, velocity_hat)
    )


def _double_forcing(
    p: Mode,
    q: Mode,
    velocity_hat: np.ndarray,
    forcing_hat: np.ndarray,
) -> np.ndarray:
    return (
        2.0 * _product_rule_forcing(p, q, velocity_hat, forcing_hat)
        + 2.0 * _product_rule_forcing(q, p, velocity_hat, forcing_hat)
    )


def _cell_rate(p: Mode, q: Mode, nu: float) -> float:
    return nu * (_mode_norm_sq(p) + _mode_norm_sq(q))


def projected_state(
    raw_hat: np.ndarray,
    formal_cutoff: int,
) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    if raw_hat.ndim != 4 or raw_hat.shape[-1] != 3 or len(set(raw_hat.shape[:3])) != 1:
        raise ValueError(f"expected raw_hat shape (N,N,N,3), got {raw_hat.shape!r}")
    n = int(raw_hat.shape[0])
    max_alias_free = n // 3
    if formal_cutoff < 1:
        raise ValueError("formal cutoff must be at least 1")
    if formal_cutoff > max_alias_free:
        raise ValueError(
            f"formal cutoff {formal_cutoff} exceeds alias-safe floor(N/3)={max_alias_free}"
        )

    wave, norm_sq, _norm, _dealias = frequency_grid(n)
    cube = np.max(np.abs(wave), axis=-1) <= float(formal_cutoff)
    retained = leray_project_hat(
        np.asarray(raw_hat, dtype=np.complex128) * cube[..., None],
        wave,
        norm_sq,
    )
    advective, pressure = nonlinear_momentum_components(retained, wave, norm_sq, cube)
    forcing = advective + pressure
    zero_mode_forcing_residual = float(np.max(np.abs(forcing[0, 0, 0])))
    # The canonical periodic physical carrier is zero-mean and retains only
    # nonzero modes.  The continuum identity gives N_0=0; enforce that exact
    # carrier convention after recording the floating residual.
    forcing[0, 0, 0] = 0.0

    divergence = np.einsum("...i,...i->...", wave, retained)
    return retained, forcing, {
        "fft_grid": n,
        "formal_cutoff": formal_cutoff,
        "alias_safe_cutoff_max": max_alias_free,
        "retained_divergence_max_residual": float(np.max(np.abs(divergence))),
        "pre_enforcement_zero_mode_forcing_residual": zero_mode_forcing_residual,
        "zero_mode_forcing_enforced": True,
    }


def evaluate_r406(
    raw_hat: np.ndarray,
    *,
    nu: float,
    formal_cutoff: int,
    max_pairs: int,
    include_output_rows: bool = False,
) -> dict[str, Any]:
    if not math.isfinite(nu) or nu <= 0.0:
        raise ValueError("viscosity must be finite and positive")
    if max_pairs < 1:
        raise ValueError("max_pairs must be positive")

    predicted_pairs, complexity_rows = global_pair_count(formal_cutoff)
    if predicted_pairs > max_pairs:
        raise RuntimeError(
            "R406 pair guard refused evaluation: "
            f"formal_cutoff={formal_cutoff} requires {predicted_pairs} unordered "
            f"same-output pairs, exceeding max_pairs={max_pairs}"
        )

    retained_hat_raw, forcing_hat_raw, state_meta = projected_state(
        raw_hat, formal_cutoff
    )
    n = int(raw_hat.shape[0])
    fourier_scale = float(n ** 3)
    velocity_hat = retained_hat_raw / fourier_scale
    forcing_hat = forcing_hat_raw / fourier_scale

    global_companion = 0.0
    global_forcing_full = 0.0
    global_forcing_diagonal = 0.0
    global_forcing_offdiagonal = 0.0
    global_rate_lifted_forcing_full = 0.0
    global_coherent_commutator_work = 0.0
    global_weighted_rate_work = 0.0
    output_rows: list[dict[str, Any]] = []
    minimum_pair_rate: float | None = None
    evaluated_pairs = 0

    for output in nonzero_cutoff_modes(formal_cutoff):
        incidences = output_fibre(formal_cutoff, output)
        mixed_cells: list[np.ndarray] = []
        cells: list[np.ndarray] = []
        forces: list[np.ndarray] = []
        rates: list[float] = []

        for p, q in incidences:
            mixed_cells.append(_mixed_plus_minus(p, q, velocity_hat))
            cells.append(_double_cell(p, q, velocity_hat))
            forces.append(_double_forcing(p, q, velocity_hat, forcing_hat))
            rate = _cell_rate(p, q, nu)
            if not (rate > 0.0):
                raise RuntimeError(
                    f"nonpositive cell rate on nonzero output {output}: p={p}, q={q}, rate={rate}"
                )
            rates.append(rate)

        fibre_companion = 0.0
        fibre_forcing_diagonal = 0.0
        fibre_forcing_offdiagonal = 0.0
        fibre_rate_lifted_forcing_full = 0.0
        fibre_pairs = 0
        for i in range(len(incidences)):
            d_i = cells[i]
            g_i = forces[i]
            lambda_i = rates[i]

            diagonal_pair_rate = 2.0 * lambda_i
            if not (diagonal_pair_rate > 0.0):
                raise RuntimeError("nonpositive diagonal R290 pair rate")
            if minimum_pair_rate is None or diagonal_pair_rate < minimum_pair_rate:
                minimum_pair_rate = diagonal_pair_rate
            diagonal_cross = _real_hermitian_cross(g_i, d_i)
            fibre_forcing_diagonal += diagonal_cross / diagonal_pair_rate
            fibre_rate_lifted_forcing_full += diagonal_cross

            for j in range(i + 1, len(incidences)):
                pair_rate = lambda_i + rates[j]
                if not (pair_rate > 0.0):
                    raise RuntimeError("nonpositive R290 pair rate")
                if minimum_pair_rate is None or pair_rate < minimum_pair_rate:
                    minimum_pair_rate = pair_rate

                forcing_ij = _real_hermitian_cross(g_i, cells[j]) / pair_rate
                forcing_ji = _real_hermitian_cross(forces[j], d_i) / pair_rate
                ordered_offdiagonal = forcing_ij + forcing_ji
                fibre_forcing_offdiagonal += ordered_offdiagonal
                fibre_rate_lifted_forcing_full += (
                    _real_hermitian_cross(g_i, cells[j])
                    + _real_hermitian_cross(forces[j], d_i)
                )

                # R496 direct companion is exactly one half of the ordered
                # oriented off-diagonal transpose completion.
                companion = 0.5 * ordered_offdiagonal
                fibre_companion += companion
                fibre_pairs += 1

        fibre_forcing_full = fibre_forcing_diagonal + fibre_forcing_offdiagonal

        mixed = (
            np.sum(np.asarray(mixed_cells), axis=0)
            if mixed_cells
            else np.zeros(3, dtype=np.complex128)
        )
        commutator = (
            0.25 * np.sum(np.asarray(forces), axis=0)
            if forces
            else np.zeros(3, dtype=np.complex128)
        )
        coherent_commutator_work = 2.0 * _real_hermitian_cross(mixed, commutator)
        weighted_decay_vector = (
            -np.sum(
                np.asarray([
                    rates[i] * mixed_cells[i]
                    for i in range(len(mixed_cells))
                ]),
                axis=0,
            )
            if mixed_cells
            else np.zeros(3, dtype=np.complex128)
        )
        tangent = weighted_decay_vector + commutator
        coherent_tangent_work = 2.0 * _real_hermitian_cross(mixed, tangent)
        weighted_rate_work = sum(
            rates[i] * 2.0 * _real_hermitian_cross(mixed, mixed_cells[i])
            for i in range(len(mixed_cells))
        )
        r685_residual = (
            weighted_rate_work
            - (coherent_commutator_work - coherent_tangent_work)
        )
        r687_residual = (
            fibre_rate_lifted_forcing_full
            - 8.0 * coherent_commutator_work
        )

        evaluated_pairs += fibre_pairs
        global_companion += fibre_companion
        global_forcing_diagonal += fibre_forcing_diagonal
        global_forcing_offdiagonal += fibre_forcing_offdiagonal
        global_forcing_full += fibre_forcing_full
        global_rate_lifted_forcing_full += fibre_rate_lifted_forcing_full
        global_coherent_commutator_work += coherent_commutator_work
        global_weighted_rate_work += weighted_rate_work
        if include_output_rows:
            output_rows.append(
                {
                    "output": list(output),
                    "incidence_count": len(incidences),
                    "unordered_pair_count": fibre_pairs,
                    "direct_companion": float(fibre_companion),
                    "r406_weighted_remainder": float(4.0 * fibre_companion),
                    "forcing_full_diagonal": float(fibre_forcing_diagonal),
                    "forcing_full_offdiagonal": float(fibre_forcing_offdiagonal),
                    "forcing_full": float(fibre_forcing_full),
                    "four_times_forcing_full": float(4.0 * fibre_forcing_full),
                    "rate_lifted_forcing_full": float(fibre_rate_lifted_forcing_full),
                    "coherent_commutator_work": float(coherent_commutator_work),
                    "coherent_tangent_work": float(coherent_tangent_work),
                    "weighted_rate_work": float(weighted_rate_work),
                    "weighted_rate_work_nonnegative": weighted_rate_work >= -1.0e-12,
                    "r685_rate_kernel_residual": float(r685_residual),
                    "r687_rate_lift_residual": float(r687_residual),
                    "offdiagonal_minus_twice_direct_companion": float(
                        fibre_forcing_offdiagonal - 2.0 * fibre_companion
                    ),
                }
            )

    if evaluated_pairs != predicted_pairs:
        raise RuntimeError(
            f"pair count mismatch: predicted={predicted_pairs}, evaluated={evaluated_pairs}"
        )

    return {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "state": state_meta,
        "viscosity": float(nu),
        "predicted_pair_count": predicted_pairs,
        "evaluated_pair_count": evaluated_pairs,
        "minimum_pair_rate": minimum_pair_rate,
        "global_direct_companion": float(global_companion),
        "r406_weighted_remainder": float(4.0 * global_companion),
        "global_forcing_full_diagonal": float(global_forcing_diagonal),
        "global_forcing_full_offdiagonal": float(global_forcing_offdiagonal),
        "global_forcing_full": float(global_forcing_full),
        "c1_instantaneous_four_forcing_full": float(4.0 * global_forcing_full),
        "global_rate_lifted_forcing_full": float(global_rate_lifted_forcing_full),
        "global_coherent_commutator_work": float(global_coherent_commutator_work),
        "global_weighted_rate_work": float(global_weighted_rate_work),
        "r687_global_rate_lift_residual": float(
            global_rate_lifted_forcing_full
            - 8.0 * global_coherent_commutator_work
        ),
        "offdiagonal_minus_twice_direct_companion": float(
            global_forcing_offdiagonal - 2.0 * global_companion
        ),
        "c1_r406_diagonal_coupling_residual": float(
            4.0 * global_forcing_full
            - (
                2.0 * (4.0 * global_companion)
                + 4.0 * global_forcing_diagonal
            )
        ),
        "output_rows": output_rows if include_output_rows else None,
        "complexity_rows": complexity_rows if include_output_rows else None,
        "interpretation": (
            "Physical-real floating specialization of the R496/R499 direct companion. "
            "Not an exact rational HelicalModeScalars inhabitant and not theorem authority."
        ),
    }


def _load_state(path: Path) -> tuple[np.ndarray, float, float | None]:
    with np.load(path, allow_pickle=False) as data:
        raw = np.asarray(data["raw_hat"], dtype=np.complex128)
        nu = float(data["nu"]) if "nu" in data else 1.0e-3
        time = float(data["time"]) if "time" in data else None
    return raw, nu, time


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--formal-cutoff", type=int, required=True)
    parser.add_argument("--max-pairs", type=int, default=5_000_000)
    parser.add_argument("--include-output-rows", action="store_true")
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    raw, nu, time = _load_state(args.state)
    payload = evaluate_r406(
        raw,
        nu=nu,
        formal_cutoff=int(args.formal_cutoff),
        max_pairs=int(args.max_pairs),
        include_output_rows=bool(args.include_output_rows),
    )
    payload["source_state"] = str(args.state)
    payload["time"] = time
    _atomic_json(args.output_json, payload, bool(args.pretty))
    print(
        json.dumps(
            {
                "output_json": str(args.output_json),
                "formal_cutoff": payload["state"]["formal_cutoff"],
                "evaluated_pair_count": payload["evaluated_pair_count"],
                "r406_weighted_remainder": payload["r406_weighted_remainder"],
                "global_forcing_full": payload["global_forcing_full"],
                "c1_instantaneous_four_forcing_full": payload[
                    "c1_instantaneous_four_forcing_full"
                ],
                "formal_rational_helical_same_object": False,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
