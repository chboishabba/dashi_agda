#!/usr/bin/env python3
"""Reconcile the sampled Schur-test L_FT^+ object against a bare shell-geometry proxy.

This is a fail-closed object-identity audit. It compares the exact mixed-tail
finite-to-tail cross block reconstructed by the sampled Schur-test script with a
separate positive shell-geometry proxy on the same finite/tail mode splits. The
goal is not theorem promotion; it is to decide whether the empirical Schur
object is the same matrix, a uniformly normalized version, or a different
object.
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
from scipy.sparse import coo_matrix, csr_matrix

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
from ns_triad_kn_acl_schur_test_proof import _adversarial_tail_support_sweep  # type: ignore
from ns_triad_kn_shell6_mixed_tail_decomposition import (  # type: ignore
    _forced_tail_profile,
    _streaming_profile,
)


SCRIPT_NAME = "scripts/ns_triad_kn_lft_definition_reconciliation.py"
CONTRACT = "ns_triad_kn_lft_definition_reconciliation"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_LFT_DEFINITION_RECONCILIATION"
SCHEMA_VERSION = "1.0.0"
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_lft_definition_reconciliation_20260624"
)
EXACT_SCRIPT_OBJECT_TEXT = (
    "Exact script object: the sampled Schur-test matrix assembled from pair-incidence sums "
    "of (sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i+phi_j-phi_l),0)."
)
BARE_PROXY_OBJECT_TEXT = (
    "Bare proxy object: shell-geometry positive kernel G_+(k,p) = max(cos(theta_kp),0) * |k x p| / |k|^2, "
    "evaluated on the same finite/tail mode split."
)
CONTROL_CARD = {
    "O": "Reconcile the sampled Schur-test L_FT^+ object against a separate bare shell-geometry proxy.",
    "R": (
        "Rebuild the exact mixed-tail cross block on N=6,8,10,12 for the forced-tail profile "
        "and the adversarial worst-tail support profile, compare it entrywise and via row/column "
        "Schur summaries against G_+(k,p)=max(cos(theta_kp),0)|k x p|/|k|^2, and classify the relation."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed object-identity audit only; no theorem, full-NS, BKM, or Clay promotion.",
    "L": (
        "same mode split -> exact sparse pair-incidence matrix -> bare shell-geometry proxy -> "
        "support overlap and ratio diagnostics -> row/column Schur comparison -> verdict."
    ),
    "P": ROUTE_DECISION,
    "G": "Downgrade the sampled Schur witness if the compared objects are not the same matrix.",
    "F": "A negative verdict blocks theorem use of the sampled Schur object until a valid carrier is identified.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--shells", type=int, nargs="+", default=[6, 8, 10, 12])
    parser.add_argument("--tail-eta", type=float, default=0.25)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument(
        "--proxy-batch-size",
        type=int,
        default=512,
        help="Tail-column batch size for the dense bare-proxy row/column sweeps.",
    )
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


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
        print(
            f"[lft-reconcile] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}",
            flush=True,
        )

    return log, started


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


def _profile_summary(profile_id: str) -> str:
    if profile_id == "forced_tail":
        return "forced-tail profile from the sampled Schur test"
    if profile_id == "adversarial_worst_tail_support":
        return "equal-mass support profile on the worst tail located by the uniform geometry sweep"
    return profile_id


def _exact_cross_matrix(
    profile: Any,
    shell_levels: np.ndarray,
    *,
    tail_cutoff: int,
    zero_eps: float,
) -> tuple[csr_matrix, np.ndarray, np.ndarray]:
    levels = np.asarray(shell_levels, dtype=np.float64)
    core = np.flatnonzero(levels < float(tail_cutoff))
    tail = np.flatnonzero(levels >= float(tail_cutoff))
    core_pos = np.full(len(levels), -1, dtype=np.int64)
    tail_pos = np.full(len(levels), -1, dtype=np.int64)
    core_pos[core] = np.arange(len(core), dtype=np.int64)
    tail_pos[tail] = np.arange(len(tail), dtype=np.int64)

    left = np.asarray(profile.edge_left, dtype=np.int64)
    right = np.asarray(profile.edge_right, dtype=np.int64)
    weights = np.asarray(profile.weights_abs, dtype=np.float64) - np.asarray(profile.weights_neg, dtype=np.float64)
    keep = np.asarray(weights > float(zero_eps), dtype=bool)
    left = left[keep]
    right = right[keep]
    weights = weights[keep]

    mask_lr = (core_pos[left] >= 0) & (tail_pos[right] >= 0)
    mask_rl = (tail_pos[left] >= 0) & (core_pos[right] >= 0)
    rows = np.concatenate((core_pos[left[mask_lr]], core_pos[right[mask_rl]]))
    cols = np.concatenate((tail_pos[right[mask_lr]], tail_pos[left[mask_rl]]))
    data = np.concatenate((weights[mask_lr], weights[mask_rl]))
    if len(data) == 0:
        matrix = csr_matrix((len(core), len(tail)), dtype=np.float64)
    else:
        matrix = coo_matrix((data, (rows, cols)), shape=(len(core), len(tail)), dtype=np.float64).tocsr()
        matrix.sum_duplicates()
    return matrix, core, tail


def _bare_entry_values(core_modes: np.ndarray, tail_modes: np.ndarray) -> np.ndarray:
    core_norm = np.linalg.norm(core_modes, axis=1)
    tail_norm = np.linalg.norm(tail_modes, axis=1)
    dots = np.sum(core_modes * tail_modes, axis=1)
    denom = core_norm * tail_norm
    cos_theta = np.divide(dots, denom, out=np.zeros_like(dots), where=denom > 0.0)
    positive_cos = np.maximum(cos_theta, 0.0)
    cross_sq = np.maximum((core_norm * core_norm) * (tail_norm * tail_norm) - dots * dots, 0.0)
    cross = np.sqrt(cross_sq)
    return np.divide(
        positive_cos * cross,
        core_norm * core_norm,
        out=np.zeros_like(cross),
        where=(core_norm * core_norm) > 0.0,
    )


def _batched_bare_proxy_summary(
    core_modes: np.ndarray,
    tail_modes: np.ndarray,
    *,
    batch_size: int,
    zero_eps: float,
) -> dict[str, Any]:
    core_norm = np.linalg.norm(core_modes, axis=1)
    tail_norm = np.linalg.norm(tail_modes, axis=1)
    core_sq = core_norm * core_norm

    row_sums = np.zeros(len(core_modes), dtype=np.float64)
    col_sums = np.zeros(len(tail_modes), dtype=np.float64)
    positive_pair_count = 0
    max_entry = 0.0

    for start in range(0, len(tail_modes), max(1, int(batch_size))):
        stop = min(start + max(1, int(batch_size)), len(tail_modes))
        batch = tail_modes[start:stop]
        batch_norm = tail_norm[start:stop]
        dots = core_modes @ batch.T
        denom = core_norm[:, None] * batch_norm[None, :]
        cos_theta = np.divide(dots, denom, out=np.zeros_like(dots), where=denom > 0.0)
        positive_cos = np.maximum(cos_theta, 0.0)
        cross_sq = np.maximum(core_sq[:, None] * (batch_norm[None, :] ** 2) - dots * dots, 0.0)
        cross = np.sqrt(cross_sq)
        entries = np.divide(
            positive_cos * cross,
            core_sq[:, None],
            out=np.zeros_like(cross),
            where=core_sq[:, None] > 0.0,
        )
        row_sums += np.sum(entries, axis=1)
        col_sums[start:stop] = np.sum(entries, axis=0)
        positive_pair_count += int(np.count_nonzero(entries > float(zero_eps)))
        if entries.size:
            max_entry = max(max_entry, float(np.max(entries)))

    row_sum_sup = float(np.max(row_sums)) if len(row_sums) else 0.0
    column_sum_sup = float(np.max(col_sums)) if len(col_sums) else 0.0
    return {
        "row_sum_sup": row_sum_sup,
        "column_sum_sup": column_sum_sup,
        "schur_bound_squared": float(row_sum_sup * column_sum_sup),
        "schur_bound": math.sqrt(float(row_sum_sup * column_sum_sup)),
        "max_cross_entry_abs": float(max_entry),
        "positive_pair_count": int(positive_pair_count),
    }


def _prepare_shell_context(
    modes: list[Any],
    shell_levels: np.ndarray,
    *,
    tail_cutoff: int,
    batch_size: int,
    zero_eps: float,
) -> dict[str, Any]:
    levels = np.asarray(shell_levels, dtype=np.float64)
    core = np.flatnonzero(levels < float(tail_cutoff))
    tail = np.flatnonzero(levels >= float(tail_cutoff))
    mode_vectors = np.asarray([mode.key for mode in modes], dtype=np.float64)
    core_modes = mode_vectors[core]
    tail_modes = mode_vectors[tail]
    bare_summary = _batched_bare_proxy_summary(
        core_modes,
        tail_modes,
        batch_size=int(batch_size),
        zero_eps=float(zero_eps),
    )
    return {
        "core": core,
        "tail": tail,
        "mode_vectors": mode_vectors,
        "bare_summary": bare_summary,
    }


def _verdict(
    *,
    support_jaccard: float | None,
    ratio_stats: dict[str, Any],
) -> str:
    ratio_count = int(ratio_stats.get("count", 0))
    relative_range = _finite_float(ratio_stats.get("relative_range"))
    mean_ratio = _finite_float(ratio_stats.get("mean"))
    if support_jaccard is not None and support_jaccard >= 0.995 and ratio_count > 0:
        if mean_ratio is not None and abs(mean_ratio - 1.0) <= 0.05 and relative_range is not None and relative_range <= 0.05:
            return "same_object"
        if relative_range is not None and relative_range <= 0.10:
            return "normalized_same_object"
    return "different_object"


def _row_for_profile(
    *,
    shell: int,
    profile_id: str,
    modes: list[Any],
    shell_levels: np.ndarray,
    profile: Any,
    tail_cutoff: int,
    zero_eps: float,
    shell_context: dict[str, Any],
) -> dict[str, Any]:
    matrix, core, tail = _exact_cross_matrix(
        profile,
        shell_levels,
        tail_cutoff=int(tail_cutoff),
        zero_eps=float(zero_eps),
    )
    core_from_context = np.asarray(shell_context["core"], dtype=np.int64)
    tail_from_context = np.asarray(shell_context["tail"], dtype=np.int64)
    if not np.array_equal(core, core_from_context) or not np.array_equal(tail, tail_from_context):
        raise ValueError("shell context/core-tail split mismatch")
    mode_vectors = np.asarray(shell_context["mode_vectors"], dtype=np.float64)
    bare_summary = dict(shell_context["bare_summary"])
    script_row_sums = np.asarray(matrix.sum(axis=1)).ravel()
    script_col_sums = np.asarray(matrix.sum(axis=0)).ravel()
    script_row_sup = float(np.max(script_row_sums)) if len(script_row_sums) else 0.0
    script_col_sup = float(np.max(script_col_sums)) if len(script_col_sums) else 0.0
    script_schur = math.sqrt(float(script_row_sup * script_col_sup))
    script_max_entry = float(matrix.data.max()) if matrix.nnz else 0.0

    row_idx, col_idx = matrix.nonzero()
    script_entries = matrix.data.astype(np.float64, copy=False)
    if len(script_entries):
        core_vectors = mode_vectors[core[row_idx]]
        tail_vectors = mode_vectors[tail[col_idx]]
        bare_entries = _bare_entry_values(core_vectors, tail_vectors)
        overlap_mask = bare_entries > float(zero_eps)
        ratio_values = [
            float(script_entries[i] / bare_entries[i])
            for i in range(len(script_entries))
            if overlap_mask[i] and bare_entries[i] > 0.0
        ]
        overlap_count = int(np.count_nonzero(overlap_mask))
        union_count = int(matrix.nnz + bare_summary["positive_pair_count"] - overlap_count)
        support_jaccard = (
            float(overlap_count) / float(union_count)
            if union_count > 0
            else None
        )
        worst = int(np.argmax(script_entries))
        worst_row = int(row_idx[worst])
        worst_col = int(col_idx[worst])
        worst_core_index = int(core[worst_row])
        worst_tail_index = int(tail[worst_col])
        worst_ratio = (
            float(script_entries[worst] / bare_entries[worst])
            if bare_entries[worst] > float(zero_eps)
            else None
        )
        bare_stats = _ratio_stats([float(value) for value in bare_entries])
        ratio_stats = _ratio_stats(ratio_values)
        worst_pair = {
            "script_entry_abs": float(script_entries[worst]),
            "bare_entry_abs": float(bare_entries[worst]),
            "entry_ratio": worst_ratio,
            "core_mode": _mode_summary(modes[worst_core_index], shell_levels[worst_core_index], worst_core_index),
            "tail_mode": _mode_summary(modes[worst_tail_index], shell_levels[worst_tail_index], worst_tail_index),
        }
    else:
        bare_stats = {"count": 0}
        ratio_stats = {"count": 0}
        overlap_count = 0
        union_count = int(bare_summary["positive_pair_count"])
        support_jaccard = 0.0 if union_count > 0 else None
        worst_pair = None

    verdict = _verdict(support_jaccard=support_jaccard, ratio_stats=ratio_stats)
    return {
        "N": int(shell),
        "K": int(tail_cutoff),
        "profile_id": profile_id,
        "profile_scope": _profile_summary(profile_id),
        "core_mode_count": int(len(core)),
        "tail_mode_count": int(len(tail)),
        "script_active_cross_pair_count": int(matrix.nnz),
        "bare_positive_cross_pair_count": int(bare_summary["positive_pair_count"]),
        "overlap_positive_pair_count": int(overlap_count),
        "support_union_pair_count": int(union_count),
        "support_jaccard": support_jaccard,
        "row_sum_script": script_row_sup,
        "row_sum_bare": float(bare_summary["row_sum_sup"]),
        "column_sum_script": script_col_sup,
        "column_sum_bare": float(bare_summary["column_sum_sup"]),
        "schur_bound_script": float(script_schur),
        "schur_bound_bare": float(bare_summary["schur_bound"]),
        "N_times_schur_bound_script": float(shell * script_schur),
        "N_times_schur_bound_bare": float(shell * float(bare_summary["schur_bound"])),
        "script_max_cross_entry_abs": script_max_entry,
        "bare_max_cross_entry_abs": float(bare_summary["max_cross_entry_abs"]),
        "bare_entry_on_script_support_stats": bare_stats,
        "entry_ratio_stats": ratio_stats,
        "worst_script_pair": worst_pair,
        "verdict": verdict,
    }


def _build_rows(args: argparse.Namespace, log) -> tuple[list[dict[str, Any]], list[str]]:
    warnings: list[str] = []
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    u, v, w = _frame_velocity(bundle, 0)
    spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
    rows: list[dict[str, Any]] = []

    for shell in sorted({int(value) for value in args.shells}):
        log("building shell carrier", shell=shell)
        shell_modes = _cube_modes(spectrum, shell_n=int(shell), zero_eps=float(args.zero_eps))
        shell_radii = np.asarray([float(mode.shell_radius) for mode in shell_modes], dtype=np.float64)
        shell_levels = _shell_levels(shell_radii)
        tail_cutoff = int(shell - 1)

        forced_probability = _forced_tail_profile(
            shell_levels,
            tail_cutoff,
            float(args.tail_eta),
            float(args.zero_eps),
        )
        shell_context = _prepare_shell_context(
            shell_modes,
            shell_levels,
            tail_cutoff=tail_cutoff,
            batch_size=int(args.proxy_batch_size),
            zero_eps=float(args.zero_eps),
        )
        forced_profile, forced_metrics = _streaming_profile(
            modes=shell_modes,
            probability=forced_probability,
            shell_levels=shell_levels,
            zero_eps=float(args.zero_eps),
            profile_id=f"forced_tail_K{tail_cutoff}_eta_{float(args.tail_eta):.3f}",
        )
        forced_row = _row_for_profile(
            shell=int(shell),
            profile_id="forced_tail",
            modes=shell_modes,
            shell_levels=shell_levels,
            profile=forced_profile,
            tail_cutoff=tail_cutoff,
            zero_eps=float(args.zero_eps),
            shell_context=shell_context,
        )
        forced_row["profile_retained_triad_count"] = int(forced_metrics["profile_retained_triad_count"])
        forced_row["triad_count"] = int(forced_metrics["triad_count"])
        rows.append(forced_row)
        log(
            "reconciled forced-tail row",
            shell=shell,
            verdict=forced_row["verdict"],
            script_column_sum=forced_row["column_sum_script"],
            bare_column_sum=forced_row["column_sum_bare"],
        )

        geometry_summary, support = _adversarial_tail_support_sweep(
            shell_modes,
            shell_levels,
            shell=int(shell),
            tail_cutoff=tail_cutoff,
            zero_eps=float(args.zero_eps),
        )
        support_probability = _support_indicator_profile(len(shell_modes), support)
        support_profile, support_metrics = _streaming_profile(
            modes=shell_modes,
            probability=support_probability,
            shell_levels=shell_levels,
            zero_eps=float(args.zero_eps),
            profile_id=f"adversarial_support_K{tail_cutoff}",
        )
        support_row = _row_for_profile(
            shell=int(shell),
            profile_id="adversarial_worst_tail_support",
            modes=shell_modes,
            shell_levels=shell_levels,
            profile=support_profile,
            tail_cutoff=tail_cutoff,
            zero_eps=float(args.zero_eps),
            shell_context=shell_context,
        )
        support_row["support_mode_count"] = int(len(support))
        support_row["uniform_geometry_worst_tail_column_sum"] = float(geometry_summary["column_sum_sup"])
        support_row["profile_retained_triad_count"] = int(support_metrics["profile_retained_triad_count"])
        support_row["triad_count"] = int(support_metrics["triad_count"])
        rows.append(support_row)
        log(
            "reconciled adversarial-support row",
            shell=shell,
            verdict=support_row["verdict"],
            script_column_sum=support_row["column_sum_script"],
            bare_column_sum=support_row["column_sum_bare"],
            support_mode_count=support_row["support_mode_count"],
        )
    return rows, warnings


def _analysis_read(rows: list[dict[str, Any]]) -> str:
    if not rows:
        return "No sampled rows were reconstructed."

    forced_rows = [row for row in rows if row["profile_id"] == "forced_tail"]
    support_rows = [row for row in rows if row["profile_id"] == "adversarial_worst_tail_support"]
    verdicts = {str(row["verdict"]) for row in rows}

    def span(rows_in: list[dict[str, Any]], key: str) -> str:
        values = [float(row[key]) for row in rows_in if _finite_float(row.get(key)) is not None]
        if not values:
            return "null"
        return f"{min(values):.6g}..{max(values):.6g}"

    return (
        "Definition-reconciliation decision: "
        f"{'different_object' if verdicts == {'different_object'} else ','.join(sorted(verdicts))}. "
        "Across the sampled shells, the exact Schur-test matrix and the bare shell-geometry proxy do not agree as the same object: "
        f"forced-tail column sums span {span(forced_rows, 'column_sum_script')} for the script object versus "
        f"{span(forced_rows, 'column_sum_bare')} for the bare proxy, while forced-tail N*Schur spans "
        f"{span(forced_rows, 'N_times_schur_bound_script')} versus {span(forced_rows, 'N_times_schur_bound_bare')}. "
        f"On the adversarial-support rows the script column sums span {span(support_rows, 'column_sum_script')} "
        f"versus bare {span(support_rows, 'column_sum_bare')}. "
        "The sampled Schur witness therefore applies to the exact pair-incidence operator it reconstructs, not automatically to the separate bare shell-geometry proxy."
    )


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    lines = [
        "# NS Triad K_N L_FT Definition Reconciliation",
        "",
        f"- status: `{payload['status']}`",
        f"- overall verdict: `{payload['overall_verdict']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- BKM exclusion proved: `{payload['bkm_exclusion_proved']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "## Compared Objects",
        "",
        f"- script object: {payload['exact_script_object']}",
        f"- bare proxy object: {payload['bare_proxy_object']}",
        "",
        "## Sampled Rows",
        "",
        "| N | profile | verdict | script pairs | bare pairs | overlap | Jaccard | row script | row bare | col script | col bare | N*Schur script | N*Schur bare |",
        "|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['N']} | {row['profile_id']} | {row['verdict']} | {row['script_active_cross_pair_count']} | "
            f"{row['bare_positive_cross_pair_count']} | {row['overlap_positive_pair_count']} | {fmt(row['support_jaccard'])} | "
            f"{fmt(row['row_sum_script'])} | {fmt(row['row_sum_bare'])} | {fmt(row['column_sum_script'])} | "
            f"{fmt(row['column_sum_bare'])} | {fmt(row['N_times_schur_bound_script'])} | {fmt(row['N_times_schur_bound_bare'])} |"
        )
    lines.extend(
        [
            "",
            "## Fits",
            "",
            f"- forced-tail script column fit: `{payload['fits']['forced_tail_column_sum_script_vs_N']}`",
            f"- forced-tail bare column fit: `{payload['fits']['forced_tail_column_sum_bare_vs_N']}`",
            f"- forced-tail script Schur fit: `{payload['fits']['forced_tail_schur_bound_script_vs_N']}`",
            f"- forced-tail bare Schur fit: `{payload['fits']['forced_tail_schur_bound_bare_vs_N']}`",
            "",
            "## Readout",
            "",
            payload["analysis_read"],
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
        "started definition reconciliation audit",
        output_dir=str(args.output_dir),
        shells=[int(shell) for shell in args.shells],
        tail_eta=float(args.tail_eta),
        proxy_batch_size=int(args.proxy_batch_size),
    )
    rows, warnings = _build_rows(args, log)
    forced_rows = [row for row in rows if row["profile_id"] == "forced_tail"]
    overall_verdict = "different_object"
    if rows:
        verdicts = {str(row["verdict"]) for row in rows}
        if verdicts == {"same_object"}:
            overall_verdict = "same_object"
        elif verdicts <= {"same_object", "normalized_same_object"} and "normalized_same_object" in verdicts:
            overall_verdict = "normalized_same_object"

    payload: dict[str, Any] = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "started_at": started_at,
        "status": OK_STATUS if len(rows) == 2 * len({int(value) for value in args.shells}) else "partial",
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "terminal_promoted": False,
        "exact_script_object": EXACT_SCRIPT_OBJECT_TEXT,
        "bare_proxy_object": BARE_PROXY_OBJECT_TEXT,
        "overall_verdict": overall_verdict,
        "rows": rows,
        "row_count": len(rows),
        "analysis_read": _analysis_read(rows),
        "fits": {
            "forced_tail_column_sum_script_vs_N": _log_log_fit(forced_rows, "N", "column_sum_script"),
            "forced_tail_column_sum_bare_vs_N": _log_log_fit(forced_rows, "N", "column_sum_bare"),
            "forced_tail_schur_bound_script_vs_N": _log_log_fit(forced_rows, "N", "schur_bound_script"),
            "forced_tail_schur_bound_bare_vs_N": _log_log_fit(forced_rows, "N", "schur_bound_bare"),
        },
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
            "message": "wrote definition reconciliation artifacts",
            "output_json": str(output_json),
            "output_md": str(output_md),
        }
    )
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
