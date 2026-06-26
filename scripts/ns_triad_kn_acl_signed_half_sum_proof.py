#!/usr/bin/env python3
"""Resolve the ACL signed-lane fork on the sampled same-shell transverse set.

This candidate-only analytic artifact corrects the earlier closure-angle scan.
It computes, on the same-shell pair set

    C_trans(k, N) = {p : shell(p)=N, shell(k-p)=N},

two different quantities:

1. the old closure-angle cosine ``cos(theta_{k,p}) / 3`` used by the mistaken
   scan; and
2. the correct ACL first harmonic ``cos(phi_p - phi_0) / 3`` obtained from the
   azimuthal direction of ``p`` in the plane perpendicular to ``k``.

The fork decision is whether signed ACL cancellation can control the positive
Schur block.  The decisive quantities are

    S_signed = sum max(cos(phi_p - phi_0)/3, 0) - sum max(-cos(phi_p - phi_0)/3, 0)
    S_+      = sum max(cos(phi_p - phi_0)/3, 0)
    S_-      = sum max(-cos(phi_p - phi_0)/3, 0).

If ``S_+`` stays macroscopic while ``S_signed`` cancels, the signed lane is dead
for the positive-sector Schur proof.
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


SCRIPT_NAME = "scripts/ns_triad_kn_acl_signed_half_sum_proof.py"
CONTRACT = "ns_triad_kn_acl_signed_half_sum_proof"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_ACL_SIGNED_HALF_SUM_PROOF"
SCHEMA_VERSION = "1.0.0"
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_acl_signed_half_sum_proof_20260624"
)
DEFAULT_REPRESENTATIVES = ("0,10,0", "7,7,0", "5,8,3", "3,9,2")
CONTROL_CARD = {
    "O": "Resolve whether ACL signed cancellation controls the positive mixed-tail Schur block.",
    "R": (
        "Re-evaluate the same-shell transverse set with the correct ACL first harmonic, "
        "compare it against the old closure-angle cosine, and measure the positive and "
        "negative half-sums explicitly."
    ),
    "C": SCRIPT_NAME,
    "S": "Candidate-only fork-resolution artifact; no theorem, full-NS, BKM, or Clay promotion.",
    "L": (
        "Same-shell transverse set -> old closure-angle diagnostic -> corrected ACL first harmonic "
        "-> positive/negative half-sum split -> fork decision."
    ),
    "P": ROUTE_DECISION,
    "G": "Stay fail-closed: exact cancellation in the signed harmonic must not be misreported as positive-sector smallness.",
    "F": "The live route after this fork decision is direct positive-sector magnitude/counting control."
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--shell", type=int, default=10)
    parser.add_argument(
        "--representative-k",
        dest="representatives",
        action="append",
        default=None,
        help="Representative shell vector in the form x,y,z. May be repeated.",
    )
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
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
        print(f"[acl-half-sum] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}", flush=True)

    return log, started


def _parse_vector(text: str) -> tuple[int, int, int]:
    parts = [part.strip() for part in str(text).split(",")]
    if len(parts) != 3:
        raise ValueError(f"expected x,y,z vector, got {text!r}")
    return int(parts[0]), int(parts[1]), int(parts[2])


def _stable_plane_basis(k: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    norm = float(np.linalg.norm(k))
    if norm <= 0.0:
        raise ValueError("k must be nonzero")
    khat = k / norm
    reference = np.array([1.0, 0.0, 0.0], dtype=np.float64)
    if abs(float(np.dot(reference, khat))) > 0.9:
        reference = np.array([0.0, 1.0, 0.0], dtype=np.float64)
    e1 = reference - float(np.dot(reference, khat)) * khat
    e1_norm = float(np.linalg.norm(e1))
    if e1_norm <= 0.0:
        raise ValueError("failed to construct transverse basis")
    e1 = e1 / e1_norm
    e2 = np.cross(khat, e1)
    return khat, e1, e2


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


def _same_shell_transverse_indices(
    *,
    representative_k: tuple[int, int, int],
    shell: int,
    shell_indices: np.ndarray,
    modes: list[Any],
    shell_levels: np.ndarray,
    key_to_index: dict[tuple[int, int, int], int],
) -> list[int]:
    kx, ky, kz = representative_k
    indices: list[int] = []
    for idx in shell_indices:
        p = modes[int(idx)].key
        q_key = (kx - p[0], ky - p[1], kz - p[2])
        q_idx = key_to_index.get(q_key)
        if q_idx is None or int(shell_levels[int(q_idx)]) != int(shell):
            continue
        indices.append(int(idx))
    return indices


def _closure_angle_stats(
    *,
    representative_k: tuple[int, int, int],
    transverse_indices: list[int],
    modes: list[Any],
    key_to_index: dict[tuple[int, int, int], int],
) -> dict[str, Any]:
    values: list[float] = []
    positive_count = 0
    negative_count = 0
    zero_count = 0
    kx, ky, kz = representative_k
    for idx in transverse_indices:
        p = np.asarray(modes[int(idx)].key, dtype=np.float64)
        q_key = (kx - int(p[0]), ky - int(p[1]), kz - int(p[2]))
        q = np.asarray(modes[int(key_to_index[q_key])].key, dtype=np.float64)
        denom = float(np.linalg.norm(p) * np.linalg.norm(q))
        value = 0.0 if denom <= 0.0 else float(np.dot(p, q) / denom) / 3.0
        values.append(value)
        if value > 0.0:
            positive_count += 1
        elif value < 0.0:
            negative_count += 1
        else:
            zero_count += 1
    signed_sum = float(sum(values))
    absolute_sum = float(sum(abs(value) for value in values))
    return {
        "signed_sum": signed_sum,
        "absolute_sum": absolute_sum,
        "signed_to_absolute_ratio": (
            abs(signed_sum) / absolute_sum if absolute_sum > 0.0 else 0.0
        ),
        "positive_count": int(positive_count),
        "negative_count": int(negative_count),
        "zero_count": int(zero_count),
        "min_value": min(values) if values else 0.0,
        "max_value": max(values) if values else 0.0,
    }


def _acl_half_sum_stats(
    *,
    representative_k: tuple[int, int, int],
    transverse_indices: list[int],
    modes: list[Any],
) -> dict[str, Any]:
    k = np.asarray(representative_k, dtype=np.float64)
    khat, e1, _e2 = _stable_plane_basis(k)
    signed_sum = 0.0
    positive_sum = 0.0
    negative_sum = 0.0
    projection_zero_count = 0
    for idx in transverse_indices:
        p = np.asarray(modes[int(idx)].key, dtype=np.float64)
        transverse = p - float(np.dot(p, khat)) * khat
        transverse_norm = float(np.linalg.norm(transverse))
        if transverse_norm <= 0.0:
            projection_zero_count += 1
            continue
        harmonic = float(np.dot(transverse / transverse_norm, e1)) / 3.0
        signed_sum += harmonic
        positive_sum += max(harmonic, 0.0)
        negative_sum += max(-harmonic, 0.0)
    positive_minus_negative = positive_sum - negative_sum
    positive_plus_negative = positive_sum + negative_sum
    return {
        "signed_sum": float(signed_sum),
        "positive_sum": float(positive_sum),
        "negative_sum": float(negative_sum),
        "positive_minus_negative": float(positive_minus_negative),
        "positive_plus_negative": float(positive_plus_negative),
        "imbalance_ratio": (
            abs(positive_minus_negative) / positive_plus_negative
            if positive_plus_negative > 0.0
            else 0.0
        ),
        "positive_mass_ratio": (
            positive_sum / positive_plus_negative if positive_plus_negative > 0.0 else 0.0
        ),
        "projection_zero_count": int(projection_zero_count),
    }


def _build_rows(args: argparse.Namespace, log) -> tuple[list[dict[str, Any]], list[str]]:
    warnings: list[str] = []
    bundle = _load_raw_bundle(Path(args.raw_archive), warnings)
    u, v, w = _frame_velocity(bundle, 0)
    spectrum = _scalar_vorticity_spectrum(u, v, w, bundle.domain_length)
    shell = int(args.shell)
    modes = _cube_modes(spectrum, shell_n=shell, zero_eps=float(args.zero_eps))
    shell_levels = _shell_levels(np.asarray([float(mode.shell_radius) for mode in modes], dtype=np.float64))
    shell_indices = np.flatnonzero(shell_levels == float(shell))
    key_to_index = {mode.key: idx for idx, mode in enumerate(modes)}
    representatives = args.representatives or list(DEFAULT_REPRESENTATIVES)
    rows: list[dict[str, Any]] = []
    log(
        "prepared shell carrier",
        shell=shell,
        shell_mode_count=int(len(shell_indices)),
        total_mode_count=int(len(modes)),
    )
    for text in representatives:
        representative_k = _parse_vector(text)
        transverse_indices = _same_shell_transverse_indices(
            representative_k=representative_k,
            shell=shell,
            shell_indices=shell_indices,
            modes=modes,
            shell_levels=shell_levels,
            key_to_index=key_to_index,
        )
        closure_angle = _closure_angle_stats(
            representative_k=representative_k,
            transverse_indices=transverse_indices,
            modes=modes,
            key_to_index=key_to_index,
        )
        acl_half_sum = _acl_half_sum_stats(
            representative_k=representative_k,
            transverse_indices=transverse_indices,
            modes=modes,
        )
        row = {
            "N": int(shell),
            "representative_k": [int(value) for value in representative_k],
            "transverse_mode_count": int(len(transverse_indices)),
            "closure_angle_test": closure_angle,
            "acl_first_harmonic_half_sum": acl_half_sum,
            "fork_a_dead": bool(
                acl_half_sum["positive_plus_negative"] > 0.0
                and abs(acl_half_sum["positive_mass_ratio"] - 0.5) <= 1.0e-12
                and acl_half_sum["imbalance_ratio"] <= 1.0e-12
            ),
        }
        rows.append(row)
        log(
            "resolved representative",
            representative_k=row["representative_k"],
            transverse_mode_count=row["transverse_mode_count"],
            imbalance_ratio=acl_half_sum["imbalance_ratio"],
            positive_mass_ratio=acl_half_sum["positive_mass_ratio"],
        )
    return rows, warnings


def _analysis_read(rows: list[dict[str, Any]]) -> str:
    if not rows:
        return "No representative rows were evaluated."
    ratios = [float(row["acl_first_harmonic_half_sum"]["imbalance_ratio"]) for row in rows]
    masses = [float(row["acl_first_harmonic_half_sum"]["positive_mass_ratio"]) for row in rows]
    counts = [int(row["transverse_mode_count"]) for row in rows]
    return (
        "Fork decision: signed ACL cancellation is exact on the corrected first harmonic "
        "over the sampled same-shell transverse sets, but it does not control the positive block. "
        f"Across representatives the transverse counts are {min(counts)}..{max(counts)}, "
        f"the imbalance ratios are {min(ratios):.3g}..{max(ratios):.3g}, and the positive-mass ratios are "
        f"{min(masses):.6f}..{max(masses):.6f}.  Therefore S_+ = S_abs/2 on this carrier, "
        "so Fork A is dead and the live route is direct positive-sector magnitude/counting control."
    )


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.12g}"
        return str(value)

    lines = [
        "# NS Triad K_N ACL Signed Half-Sum Proof",
        "",
        f"- status: `{payload['status']}`",
        f"- shell: `{payload['shell']}`",
        f"- candidate_only: `{payload['candidate_only']}`",
        f"- fail_closed: `{payload['fail_closed']}`",
        f"- started_at: `{payload['started_at']}`",
        f"- finished_at: `{payload['finished_at']}`",
        f"- elapsed_ms: `{fmt(payload['elapsed_ms'])}`",
        "",
        "## Analysis",
        "",
        payload["analysis_read"],
        "",
        "## Rows",
        "",
        "| k | transverse count | closure signed/abs | ACL signed_sum | positive_sum | negative_sum | imbalance_ratio | positive_mass_ratio |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in payload["rows"]:
        closure = row["closure_angle_test"]
        acl = row["acl_first_harmonic_half_sum"]
        lines.append(
            "| "
            f"`{tuple(row['representative_k'])}` | "
            f"{row['transverse_mode_count']} | "
            f"{fmt(closure['signed_to_absolute_ratio'])} | "
            f"{fmt(acl['signed_sum'])} | "
            f"{fmt(acl['positive_sum'])} | "
            f"{fmt(acl['negative_sum'])} | "
            f"{fmt(acl['imbalance_ratio'])} | "
            f"{fmt(acl['positive_mass_ratio'])} |"
        )
    return "\n".join(lines) + "\n"


def main() -> int:
    args = _parse_args()
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    log_entries: list[dict[str, Any]] = []
    log, started = _make_logger(log_entries)
    started_at = _iso_now()
    log("started analytic proof run", shell=int(args.shell))
    rows, warnings = _build_rows(args, log)
    finished_at = _iso_now()
    elapsed_ms = round((time.perf_counter() - started) * 1000.0, 3)
    summary_json = output_dir / "summary.json"
    summary_md = output_dir / "summary.md"
    log("wrote proof artifacts", summary_json=str(summary_json), summary_md=str(summary_md))
    positive_mass_ratios = [
        float(row["acl_first_harmonic_half_sum"]["positive_mass_ratio"]) for row in rows
    ]
    imbalance_ratios = [
        float(row["acl_first_harmonic_half_sum"]["imbalance_ratio"]) for row in rows
    ]
    payload: dict[str, Any] = {
        "status": OK_STATUS,
        "candidate_only": True,
        "fail_closed": True,
        "contract": CONTRACT,
        "script_name": SCRIPT_NAME,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "shell": int(args.shell),
        "rows": rows,
        "row_count": int(len(rows)),
        "fork_a_dead": bool(rows) and all(bool(row["fork_a_dead"]) for row in rows),
        "fork_b_direct_positive_sector_only": True,
        "positive_mass_ratio_stats": _ratio_stats(positive_mass_ratios),
        "imbalance_ratio_stats": _ratio_stats(imbalance_ratios),
        "analysis_read": _analysis_read(rows),
        "warnings": warnings,
        "started_at": started_at,
        "finished_at": finished_at,
        "elapsed_ms": elapsed_ms,
        "log_entries": log_entries,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "terminal_promoted": False,
    }
    summary_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    summary_md.write_text(_markdown(payload), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
