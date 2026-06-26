#!/usr/bin/env python3
"""Prove the sampled mixed-tail Schur-test bound for the ACL cross block.

This is a candidate-only finite-shell proof artifact.  It reconstructs the
exact positive-sector finite-to-tail block ``L_FT^+`` for the mixed-tail
forced-tail profiles at ``N=6,8,10,12`` with ``K=N-1`` and ``eta=0.25``.

For each sampled shell it proves the matrix inequality

    ||L_FT^+||_2^2 <= (sup_k sum_p |L_FT^+(k,p)|) (sup_p sum_k |L_FT^+(k,p)|)

by computing the exact row/column absolute sums of the explicit finite matrix.
The artifact remains fail-closed: it does not promote theorem authority, full
Navier-Stokes closure, BKM exclusion, or a Clay claim.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import numpy as np

from ns_triad_constrained_adversarial_fork_optimizer import _cube_modes, _shell_levels  # type: ignore
from ns_triad_frame_stability_scan import (  # type: ignore
    AUTHORITY,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_ZERO_EPS,
    OK_STATUS,
    _frame_velocity,
    _json_text,
    _load_raw_bundle,
    _scalar_vorticity_spectrum,
)
from ns_triad_kn_shell6_mixed_tail_decomposition import (  # type: ignore
    _forced_tail_profile,
    _streaming_profile,
)


SCRIPT_NAME = "scripts/ns_triad_kn_acl_schur_test_proof.py"
CONTRACT = "ns_triad_kn_acl_schur_test_proof"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_ACL_SCHUR_TEST_PROOF"
SCHEMA_VERSION = "1.0.0"
DEFAULT_SCALING_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_sparse_schur_scaling_fit_20260624/summary.json"
)
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_acl_schur_test_proof_20260624"
)
CANONICAL_SCHUR_TEST_STATEMENT = (
    "||L_FT^+||_op^2 <= (sup_k sum_p |L_FT^+(k,p)|) * (sup_p sum_k |L_FT^+(k,p)|)"
)
CONTROL_CARD = {
    "O": "Prove the sampled mixed-tail Schur-test inequality for the exact finite-shell L_FT^+ cross block.",
    "R": (
        "Rebuild the forced-tail profiles at N=6,8,10,12, compute the exact "
        "positive-sector finite-to-tail block, and certify the row/column "
        "kernel-sum bound without theorem promotion."
    ),
    "C": SCRIPT_NAME,
    "S": "Finite-shell candidate-only proof artifact; no theorem, full-NS, BKM, or Clay promotion.",
    "L": (
        "Explicit positive-sector cross block -> exact row/column absolute sums "
        "-> Schur-test inequality -> sampled N^-1 operator-norm scale."
    ),
    "P": ROUTE_DECISION,
    "G": "Keep the result fail-closed: the finite-shell proof does not imply a uniform asymptotic theorem.",
    "F": "The remaining gap is uniform/profile-independent promotion of the sampled N^-1 block scale.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--scaling-summary", type=Path, default=DEFAULT_SCALING_SUMMARY)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--shells", type=int, nargs="+", default=[6, 8, 10, 12])
    parser.add_argument("--tail-eta", type=float, default=0.25)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _ratio_stats(values: list[float]) -> dict[str, Any]:
    if not values:
        return {"count": 0}
    mean = sum(values) / len(values)
    stdev = 0.0 if len(values) == 1 else math.sqrt(
        sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    )
    return {
        "count": len(values),
        "min": min(values),
        "max": max(values),
        "mean": mean,
        "sample_stdev": stdev,
        "relative_range": (max(values) - min(values)) / mean if mean != 0.0 else None,
    }


def _log_log_fit(rows: list[dict[str, Any]], x_key: str, y_key: str) -> dict[str, Any]:
    points: list[tuple[float, float]] = []
    for row in rows:
        x = _finite_float(row.get(x_key))
        y = _finite_float(row.get(y_key))
        if x is None or y is None or x <= 0.0 or y <= 0.0:
            continue
        points.append((math.log(x), math.log(y)))
    if len(points) < 2:
        return {"count": len(points)}
    xs = [point[0] for point in points]
    ys = [point[1] for point in points]
    mean_x = sum(xs) / len(xs)
    mean_y = sum(ys) / len(ys)
    denom = sum((x - mean_x) ** 2 for x in xs)
    if denom == 0.0:
        return {"count": len(points)}
    slope = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys, strict=False)) / denom
    intercept = mean_y - slope * mean_x
    return {
        "count": len(points),
        "log_log_slope": slope,
        "exp_intercept": math.exp(intercept),
    }


def _load_scaling_rows(path: Path) -> dict[int, dict[str, Any]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    rows = payload.get("rows", [])
    if not isinstance(rows, list):
        return {}
    out: dict[int, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        shell = row.get("N", row.get("shell"))
        shell_int = int(shell) if shell is not None else None
        if shell_int is not None:
            out[shell_int] = row
    return out


def _uniform_profile(mode_count: int) -> np.ndarray:
    if mode_count <= 0:
        return np.zeros(0, dtype=np.float64)
    return np.full(mode_count, 1.0 / float(mode_count), dtype=np.float64)


def _support_indicator_profile(mode_count: int, support: set[int]) -> np.ndarray:
    probability = np.zeros(mode_count, dtype=np.float64)
    if not support:
        return probability
    mass = 1.0 / float(len(support))
    for index in support:
        probability[int(index)] = mass
    return probability


def _mode_summary(mode: Any, shell_level: float, index: int) -> dict[str, Any]:
    return {
        "mode_index": int(index),
        "mode_key": [int(mode.key[0]), int(mode.key[1]), int(mode.key[2])],
        "shell_level": int(shell_level),
        "shell_radius": float(mode.shell_radius),
    }


def _cross_block_summary(
    profile: Any,
    modes: list[Any],
    shell_levels: np.ndarray,
    *,
    shell: int,
    tail_cutoff: int,
    zero_eps: float,
    profile_id: str,
) -> dict[str, Any]:
    levels = np.asarray(shell_levels, dtype=np.float64)
    core = np.flatnonzero(levels < float(tail_cutoff))
    tail = np.flatnonzero(levels >= float(tail_cutoff))
    core_pos = {int(index): pos for pos, index in enumerate(core)}
    tail_pos = {int(index): pos for pos, index in enumerate(tail)}
    row_sums = np.zeros(len(core), dtype=np.float64)
    col_sums = np.zeros(len(tail), dtype=np.float64)
    row_neighbors: dict[int, set[int]] = {}
    col_neighbors: dict[int, set[int]] = {}
    cross_edge_count = 0
    cross_weight_total = 0.0
    max_entry_abs = 0.0

    for left, right, w_abs, w_neg in zip(
        profile.edge_left,
        profile.edge_right,
        profile.weights_abs,
        profile.weights_neg,
        strict=False,
    ):
        weight = max(float(w_abs) - float(w_neg), 0.0)
        if weight <= float(zero_eps):
            continue
        left = int(left)
        right = int(right)
        left_core = core_pos.get(left)
        right_core = core_pos.get(right)
        left_tail = tail_pos.get(left)
        right_tail = tail_pos.get(right)
        if left_core is not None and right_tail is not None:
            row_sums[left_core] += weight
            col_sums[right_tail] += weight
            row_neighbors.setdefault(left_core, set()).add(right_tail)
            col_neighbors.setdefault(right_tail, set()).add(left_core)
            cross_edge_count += 1
            cross_weight_total += weight
            max_entry_abs = max(max_entry_abs, weight)
        elif left_tail is not None and right_core is not None:
            row_sums[right_core] += weight
            col_sums[left_tail] += weight
            row_neighbors.setdefault(right_core, set()).add(left_tail)
            col_neighbors.setdefault(left_tail, set()).add(right_core)
            cross_edge_count += 1
            cross_weight_total += weight
            max_entry_abs = max(max_entry_abs, weight)

    row_sum_sup = float(np.max(row_sums)) if len(row_sums) else 0.0
    column_sum_sup = float(np.max(col_sums)) if len(col_sums) else 0.0
    worst_core_pos = int(np.argmax(row_sums)) if len(row_sums) else None
    worst_tail_pos = int(np.argmax(col_sums)) if len(col_sums) else None
    worst_core_index = int(core[worst_core_pos]) if worst_core_pos is not None else None
    worst_tail_index = int(tail[worst_tail_pos]) if worst_tail_pos is not None else None
    schur_bound_squared = float(row_sum_sup * column_sum_sup)
    schur_bound = math.sqrt(schur_bound_squared)
    summary = {
        "N": int(shell),
        "K": int(tail_cutoff),
        "profile_id": str(profile_id),
        "core_mode_count": int(len(core)),
        "tail_mode_count": int(len(tail)),
        "cross_edge_count": int(cross_edge_count),
        "cross_weight_total": float(cross_weight_total),
        "row_sum_sup": row_sum_sup,
        "column_sum_sup": column_sum_sup,
        "schur_bound_squared": schur_bound_squared,
        "schur_bound": schur_bound,
        "N_times_schur_bound": float(shell * schur_bound),
        "N_squared_times_column_sum_sup": float(shell * shell * column_sum_sup),
        "max_cross_entry_abs": float(max_entry_abs),
        "cross_entry_sign": "nonpositive",
    }
    if worst_core_pos is not None and worst_core_index is not None:
        summary["worst_core_active_tail_count"] = int(len(row_neighbors.get(worst_core_pos, set())))
        summary["worst_core_mode"] = _mode_summary(
            modes[worst_core_index],
            levels[worst_core_index],
            worst_core_index,
        )
    if worst_tail_pos is not None and worst_tail_index is not None:
        summary["worst_tail_active_finite_k_count"] = int(len(col_neighbors.get(worst_tail_pos, set())))
        summary["worst_tail_mode"] = _mode_summary(
            modes[worst_tail_index],
            levels[worst_tail_index],
            worst_tail_index,
        )
    return summary


def _adversarial_tail_support_sweep(
    modes: list[Any],
    shell_levels: np.ndarray,
    *,
    shell: int,
    tail_cutoff: int,
    zero_eps: float,
) -> tuple[dict[str, Any], set[int]]:
    levels = np.asarray(shell_levels, dtype=np.float64)
    core = np.flatnonzero(levels < float(tail_cutoff))
    tail = np.flatnonzero(levels >= float(tail_cutoff))
    core_pos = {int(index): pos for pos, index in enumerate(core)}
    tail_pos = {int(index): pos for pos, index in enumerate(tail)}
    row_sums = np.zeros(len(core), dtype=np.float64)
    col_sums = np.zeros(len(tail), dtype=np.float64)
    core_neighbors: dict[int, set[int]] = {}
    support_sets: dict[int, set[int]] = {}
    key_to_index = {mode.key: index for index, mode in enumerate(modes)}
    uniform_probability = _uniform_profile(len(modes))
    uniform_amp = float(math.sqrt(uniform_probability[0])) if len(uniform_probability) else 0.0
    uniform_weight_factor = uniform_amp * uniform_amp * uniform_amp / 3.0
    positive_cross_edge_count = 0

    for left in range(len(modes)):
        mode_left = modes[left]
        for right in range(left + 1, len(modes)):
            mode_right = modes[right]
            key_out = (
                mode_left.key[0] + mode_right.key[0],
                mode_left.key[1] + mode_right.key[1],
                mode_left.key[2] + mode_right.key[2],
            )
            out = key_to_index.get(key_out)
            if out is None or out == left or out == right:
                continue
            mode_out = modes[out]
            mode_weight = float(mode_left.amplitude * mode_right.amplitude * mode_out.amplitude)
            if not math.isfinite(mode_weight) or mode_weight <= float(zero_eps):
                continue
            coherence = math.cos(mode_left.phase + mode_right.phase - mode_out.phase)
            positive_factor = max(float(coherence), 0.0)
            if positive_factor <= float(zero_eps):
                continue
            weight = uniform_weight_factor * positive_factor
            touched_tails: set[int] = set()
            for a, b in ((left, right), (left, out), (right, out)):
                a_core = core_pos.get(int(a))
                b_core = core_pos.get(int(b))
                a_tail = tail_pos.get(int(a))
                b_tail = tail_pos.get(int(b))
                if a_core is not None and b_tail is not None:
                    row_sums[a_core] += weight
                    col_sums[b_tail] += weight
                    core_neighbors.setdefault(b_tail, set()).add(a_core)
                    touched_tails.add(b_tail)
                    positive_cross_edge_count += 1
                elif a_tail is not None and b_core is not None:
                    row_sums[b_core] += weight
                    col_sums[a_tail] += weight
                    core_neighbors.setdefault(a_tail, set()).add(b_core)
                    touched_tails.add(a_tail)
                    positive_cross_edge_count += 1
            for tail_pos_index in touched_tails:
                support_sets.setdefault(tail_pos_index, set()).update((left, right, out))

    worst_core_pos = int(np.argmax(row_sums)) if len(row_sums) else None
    worst_tail_pos = int(np.argmax(col_sums)) if len(col_sums) else None
    worst_core_index = int(core[worst_core_pos]) if worst_core_pos is not None else None
    worst_tail_index = int(tail[worst_tail_pos]) if worst_tail_pos is not None else None
    row_sum_sup = float(np.max(row_sums)) if len(row_sums) else 0.0
    column_sum_sup = float(np.max(col_sums)) if len(col_sums) else 0.0
    schur_bound = math.sqrt(float(row_sum_sup * column_sum_sup))
    support = set() if worst_tail_pos is None else support_sets.get(worst_tail_pos, set())
    summary = {
        "N": int(shell),
        "K": int(tail_cutoff),
        "profile_id": "uniform_all_modes_geometry_sweep",
        "profile_scope": "all selected shell modes carry equal probability mass",
        "candidate_only": True,
        "profile_independent_certificate": False,
        "positive_cross_edge_count": int(positive_cross_edge_count),
        "row_sum_sup": row_sum_sup,
        "column_sum_sup": column_sum_sup,
        "schur_bound": schur_bound,
        "N_times_schur_bound": float(shell * schur_bound),
        "support_mode_count_for_worst_tail": int(len(support)),
    }
    if worst_core_pos is not None and worst_core_index is not None:
        summary["worst_core_mode"] = _mode_summary(
            modes[worst_core_index],
            levels[worst_core_index],
            worst_core_index,
        )
    if worst_tail_pos is not None and worst_tail_index is not None:
        summary["worst_tail_active_finite_k_count"] = int(len(core_neighbors.get(worst_tail_pos, set())))
        summary["worst_tail_mode"] = _mode_summary(
            modes[worst_tail_index],
            levels[worst_tail_index],
            worst_tail_index,
        )
    return summary, support


def _derive_adversarial_row(
    modes: list[Any],
    shell_levels: np.ndarray,
    *,
    shell: int,
    tail_cutoff: int,
    zero_eps: float,
) -> dict[str, Any]:
    geometry_summary, _support = _adversarial_tail_support_sweep(
        modes,
        shell_levels,
        shell=int(shell),
        tail_cutoff=int(tail_cutoff),
        zero_eps=float(zero_eps),
    )
    geometry_summary["uniform_geometry_sweep"] = dict(geometry_summary)
    return geometry_summary


def _derive_rows(args: argparse.Namespace) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[str]]:
    warnings: list[str] = []
    scaling_rows = _load_scaling_rows(Path(args.scaling_summary))
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    u, v, w = _frame_velocity(bundle, 0)
    spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
    rows: list[dict[str, Any]] = []
    adversarial_rows: list[dict[str, Any]] = []

    for shell in sorted({int(value) for value in args.shells}):
        shell_modes = _cube_modes(spectrum, shell_n=int(shell), zero_eps=float(args.zero_eps))
        shell_radii = np.asarray([float(mode.shell_radius) for mode in shell_modes], dtype=np.float64)
        shell_levels = _shell_levels(shell_radii)
        tail_cutoff = int(shell - 1)
        probability = _forced_tail_profile(
            shell_levels,
            tail_cutoff,
            float(args.tail_eta),
            float(args.zero_eps),
        )
        profile, _frame_metrics = _streaming_profile(
            modes=shell_modes,
            probability=probability,
            shell_levels=shell_levels,
            zero_eps=float(args.zero_eps),
            profile_id=f"forced_tail_K{tail_cutoff}_eta_{float(args.tail_eta):.3f}",
        )
        row = _cross_block_summary(
            profile,
            shell_modes,
            shell_levels,
            shell=int(shell),
            tail_cutoff=tail_cutoff,
            zero_eps=float(args.zero_eps),
            profile_id=f"forced_tail_K{tail_cutoff}_eta_{float(args.tail_eta):.3f}",
        )
        scaling = scaling_rows.get(int(shell), {})
        row["q_gap"] = _finite_float(scaling.get("q_gap"))
        row["D"] = _finite_float(scaling.get("D"))
        row["D_q_gap"] = _finite_float(scaling.get("D_q_gap"))
        row["N2_q_gap"] = _finite_float(scaling.get("N2_q_gap"))
        row["detail_json"] = scaling.get("detail_json")
        rows.append(row)
        adversarial_rows.append(
            _derive_adversarial_row(
                shell_modes,
                shell_levels,
                shell=int(shell),
                tail_cutoff=tail_cutoff,
                zero_eps=float(args.zero_eps),
            )
        )
    return rows, adversarial_rows, warnings


def _analysis_read(rows: list[dict[str, Any]], adversarial_rows: list[dict[str, Any]]) -> str:
    if not rows:
        return "No sampled shells were reconstructed."

    row_sups = [float(row["row_sum_sup"]) for row in rows]
    col_sups = [float(row["column_sum_sup"]) for row in rows]
    schur = [float(row["schur_bound"]) for row in rows]
    n_times = [float(row["N_times_schur_bound"]) for row in rows]
    n2_col = [float(row["N_squared_times_column_sum_sup"]) for row in rows]
    adv_cols = [float(row["column_sum_sup"]) for row in adversarial_rows]
    adv_active = [int(row.get("worst_tail_active_finite_k_count", 0)) for row in adversarial_rows]

    def fmt(value: float | None) -> str:
        return "null" if value is None else f"{value:.6g}"

    return (
        "Finite-shell Schur-test proof readout: the exact mixed-tail positive "
        f"cross block has row/output absolute-sum supremum in {fmt(min(row_sups))}..{fmt(max(row_sups))}, "
        f"column/input absolute-sum supremum in {fmt(min(col_sups))}..{fmt(max(col_sups))}, "
        f"and therefore Schur bound ||L_FT^+||_op <= sqrt(row_sup * col_sup) in "
        f"{fmt(min(schur))}..{fmt(max(schur))}.  The sampled normalization is consistent "
        f"with N * ||L_FT^+||_op staying in {fmt(min(n_times))}..{fmt(max(n_times))} while "
        f"N^2 * column_sum_sup stays in {fmt(min(n2_col))}..{fmt(max(n2_col))}.  "
        f"The added adversarial tail-mode sweep records uniform-sweep worst-tail column sums in "
        f"{fmt(min(adv_cols))}..{fmt(max(adv_cols))} with worst-tail active finite-mode counts in "
        f"{min(adv_active)}..{max(adv_active)}.  This remains a sampled finite-shell certificate only; "
        "uniform/profile-independent theorem promotion remains open."
    )


def _iso_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _make_logger(entries: list[dict[str, Any]]):
    started = time.perf_counter()

    def log(message: str, **fields: Any) -> None:
        entry: dict[str, Any] = {
            "at": _iso_now(),
            "elapsed_ms": round((time.perf_counter() - started) * 1000.0, 3),
            "message": message,
        }
        if fields:
            entry.update(fields)
        entries.append(entry)
        details = json.dumps(fields, sort_keys=True, default=str) if fields else "{}"
        print(f"[acl-schur] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}", flush=True)

    return log, started


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    lines = [
        "# NS Triad K_N ACL Schur-Test Proof",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- BKM exclusion proved: `{payload['bkm_exclusion_proved']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "## Statement",
        "",
        f"`{payload['canonical_schur_test_statement']}`",
        "",
        "## Proof Shape",
        "",
        "1. Reconstruct the exact positive-sector cross block `L_FT^+` for each sampled shell.",
        "2. Use that every cross entry is nonpositive, so absolute row/column sums equal weighted cross-incidence sums.",
        "3. Apply the matrix Schur test to the explicit finite matrix.",
        "4. Record the resulting sampled `N^-1` operator-norm scale without theorem promotion.",
        "",
        "## Rows",
        "",
        "| N | K | core modes | tail modes | row sup | column sup | sqrt(row*col) | N*bound | N²*col | q_gap | D*q_gap |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['N']} | {row['K']} | {row['core_mode_count']} | {row['tail_mode_count']} | "
            f"{fmt(row['row_sum_sup'])} | {fmt(row['column_sum_sup'])} | {fmt(row['schur_bound'])} | "
            f"{fmt(row['N_times_schur_bound'])} | {fmt(row['N_squared_times_column_sum_sup'])} | "
            f"{fmt(row['q_gap'])} | {fmt(row['D_q_gap'])} |"
        )
    lines.extend(
        [
            "",
            "## Adversarial Tail Sweep",
            "",
            "| N | K | sweep profile | worst tail mode | active finite k | row sup | column sup | sqrt(row*col) | N*bound |",
            "|---:|---:|---|---|---:|---:|---:|---:|---:|",
        ]
    )
    for row in payload["adversarial_rows"]:
        tail_mode = row.get("worst_tail_mode", {})
        lines.append(
            f"| {row['N']} | {row['K']} | {row['profile_id']} | "
            f"{tail_mode.get('mode_key')} | {fmt(row.get('worst_tail_active_finite_k_count'))} | "
            f"{fmt(row['row_sum_sup'])} | {fmt(row['column_sum_sup'])} | {fmt(row['schur_bound'])} | "
            f"{fmt(row['N_times_schur_bound'])} |"
        )
    lines.extend(
        [
            "",
            "## Readout",
            "",
            payload["analysis_read"],
            "",
            "## Scaling",
            "",
            f"- row sup stats: `{payload['row_sum_sup_stats']}`",
            f"- column sup stats: `{payload['column_sum_sup_stats']}`",
            f"- Schur bound stats: `{payload['schur_bound_stats']}`",
            f"- N*Schur bound stats: `{payload['n_times_schur_bound_stats']}`",
            f"- N²*column sup stats: `{payload['n_squared_times_column_sum_sup_stats']}`",
            f"- adversarial column sup stats: `{payload['adversarial_column_sum_sup_stats']}`",
            f"- adversarial Schur bound stats: `{payload['adversarial_schur_bound_stats']}`",
            f"- adversarial N*Schur bound stats: `{payload['adversarial_n_times_schur_bound_stats']}`",
            f"- log-log fit column sup vs N: `{payload['fits']['column_sum_sup_vs_N']}`",
            f"- log-log fit Schur bound vs N: `{payload['fits']['schur_bound_vs_N']}`",
            f"- log-log fit adversarial column sup vs N: `{payload['fits']['adversarial_column_sum_sup_vs_N']}`",
            f"- log-log fit adversarial Schur bound vs N: `{payload['fits']['adversarial_schur_bound_vs_N']}`",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    args = _parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    log_entries: list[dict[str, Any]] = []
    log, started_perf = _make_logger(log_entries)
    started_at = _iso_now()
    log(
        "started analytic proof run",
        output_dir=str(args.output_dir),
        shells=[int(shell) for shell in args.shells],
        tail_eta=float(args.tail_eta),
    )
    rows, adversarial_rows, warnings = _derive_rows(args)
    log(
        "derived sampled proof rows",
        row_count=len(rows),
        adversarial_row_count=len(adversarial_rows),
    )
    row_sups = [float(row["row_sum_sup"]) for row in rows]
    col_sups = [float(row["column_sum_sup"]) for row in rows]
    schur = [float(row["schur_bound"]) for row in rows]
    n_times = [float(row["N_times_schur_bound"]) for row in rows]
    n2_col = [float(row["N_squared_times_column_sum_sup"]) for row in rows]
    adv_col_sups = [float(row["column_sum_sup"]) for row in adversarial_rows]
    adv_schur = [float(row["schur_bound"]) for row in adversarial_rows]
    adv_n_times = [float(row["N_times_schur_bound"]) for row in adversarial_rows]

    payload: dict[str, Any] = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "started_at": started_at,
        "status": OK_STATUS if len(rows) == len({int(value) for value in args.shells}) else "partial",
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "terminal_promoted": False,
        "proof_scope": "finite_shell_only",
        "canonical_schur_test_statement": CANONICAL_SCHUR_TEST_STATEMENT,
        "raw_archive": str(args.raw_archive),
        "scaling_summary": str(args.scaling_summary),
        "row_count": len(rows),
        "rows": rows,
        "adversarial_row_count": len(adversarial_rows),
        "adversarial_rows": adversarial_rows,
        "row_sum_sup_stats": _ratio_stats(row_sups),
        "column_sum_sup_stats": _ratio_stats(col_sups),
        "schur_bound_stats": _ratio_stats(schur),
        "n_times_schur_bound_stats": _ratio_stats(n_times),
        "n_squared_times_column_sum_sup_stats": _ratio_stats(n2_col),
        "adversarial_column_sum_sup_stats": _ratio_stats(adv_col_sups),
        "adversarial_schur_bound_stats": _ratio_stats(adv_schur),
        "adversarial_n_times_schur_bound_stats": _ratio_stats(adv_n_times),
        "fits": {
            "column_sum_sup_vs_N": _log_log_fit(rows, "N", "column_sum_sup"),
            "schur_bound_vs_N": _log_log_fit(rows, "N", "schur_bound"),
            "adversarial_column_sum_sup_vs_N": _log_log_fit(adversarial_rows, "N", "column_sum_sup"),
            "adversarial_schur_bound_vs_N": _log_log_fit(adversarial_rows, "N", "schur_bound"),
        },
        "analysis_read": _analysis_read(rows, adversarial_rows),
        "warnings": warnings,
        "log_entries": log_entries,
    }

    output_json = args.output_dir / "summary.json"
    output_md = args.output_dir / "summary.md"
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    output_md.write_text(_markdown(payload), encoding="utf-8")
    finished_at = _iso_now()
    elapsed_ms = round((time.perf_counter() - started_perf) * 1000.0, 3)
    payload["finished_at"] = finished_at
    payload["elapsed_ms"] = elapsed_ms
    payload["log_entries"].append(
        {
            "at": finished_at,
            "elapsed_ms": elapsed_ms,
            "message": "wrote proof artifacts",
            "output_json": str(output_json),
            "output_md": str(output_md),
        }
    )
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
