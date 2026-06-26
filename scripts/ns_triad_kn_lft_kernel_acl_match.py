#!/usr/bin/env python3
"""Audit whether DASHI's exact L_FT^+ cross block matches the Fields ACL kernel.

This is a fail-closed analytic artifact.  It writes the exact entry formula used
by the mixed-tail lane, reconstructs sampled shells N=6,8,10,12, and records
why the current positive-sector kernel does not equal a profile-independent ACL
carrier up to an N-only normalization.
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


SCRIPT_NAME = "scripts/ns_triad_kn_lft_kernel_acl_match.py"
CONTRACT = "ns_triad_kn_lft_kernel_acl_match"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_LFT_KERNEL_ACL_MATCH"
SCHEMA_VERSION = "1.0.0"
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_lft_kernel_acl_match_20260624"
)
EXACT_DASHI_ENTRY_FORMULA = (
    "For a finite mode k and tail mode p, the exact mixed-tail cross-block entry is "
    "L_FT^+(k,p) = -sum_{triads touching {k,p}} (sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i+phi_j-phi_l),0), "
    "with the sum taken over retained resonant triads whose pair-incidence edge joins k to p."
)
ACL_CANDIDATE_FORMULA = (
    "Candidate ACL carrier target: L_FT^+(k,p) = C_norm(N) * K_ACL(k,p), "
    "with K_ACL profile-independent and carrying the signed/angular cancellation geometry."
)
CONTROL_CARD = {
    "O": "Decide whether the exact DASHI mixed-tail cross block equals the Fields ACL kernel up to harmless normalization.",
    "R": (
        "Write the exact L_FT^+ entry formula from the streaming profile builder, "
        "sample shells N=6,8,10,12, and test whether profile amplitudes and positive-sector truncation block the ACL match."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed kernel-match audit only; no theorem, full-NS, BKM, or Clay promotion.",
    "L": (
        "Exact edge formula -> cross-block pair aggregation -> profile and sign audit -> "
        "kernel-match status."
    ),
    "P": ROUTE_DECISION,
    "G": "If the ACL sign geometry or profile-independence fails, kill the match rather than overclaim.",
    "F": "The current L_FT^+ kernel may still admit a different proof route, but not the claimed ACL equality."
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--shells", type=int, nargs="+", default=[6, 8, 10, 12])
    parser.add_argument("--tail-eta", type=float, default=0.25)
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
        print(f"[lft-acl-match] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}", flush=True)

    return log, started


def _uniform_profile(mode_count: int) -> np.ndarray:
    if mode_count <= 0:
        return np.zeros(0, dtype=np.float64)
    return np.full(mode_count, 1.0 / float(mode_count), dtype=np.float64)


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


def _cross_pair_stats(
    profile: Any,
    shell_levels: np.ndarray,
    *,
    shell: int,
    tail_cutoff: int,
    zero_eps: float,
    profile_label: str,
) -> dict[str, Any]:
    levels = np.asarray(shell_levels, dtype=np.float64)
    core = np.flatnonzero(levels < float(tail_cutoff))
    tail = np.flatnonzero(levels >= float(tail_cutoff))
    core_pos = {int(index): pos for pos, index in enumerate(core)}
    tail_pos = {int(index): pos for pos, index in enumerate(tail)}
    row_sums = np.zeros(len(core), dtype=np.float64)
    col_sums = np.zeros(len(tail), dtype=np.float64)
    pair_weights: dict[tuple[int, int], float] = {}
    pair_counts: dict[tuple[int, int], int] = {}

    for left, right, w_abs, w_neg in zip(
        profile.edge_left,
        profile.edge_right,
        profile.weights_abs,
        profile.weights_neg,
        strict=False,
    ):
        weight = float(w_abs) - float(w_neg)
        if weight <= float(zero_eps):
            continue
        left = int(left)
        right = int(right)
        left_core = core_pos.get(left)
        right_core = core_pos.get(right)
        left_tail = tail_pos.get(left)
        right_tail = tail_pos.get(right)
        pair_key: tuple[int, int] | None = None
        if left_core is not None and right_tail is not None:
            row_sums[left_core] += weight
            col_sums[right_tail] += weight
            pair_key = (left_core, right_tail)
        elif left_tail is not None and right_core is not None:
            row_sums[right_core] += weight
            col_sums[left_tail] += weight
            pair_key = (right_core, left_tail)
        if pair_key is not None:
            pair_weights[pair_key] = pair_weights.get(pair_key, 0.0) + weight
            pair_counts[pair_key] = pair_counts.get(pair_key, 0) + 1

    max_pair = max(pair_weights.items(), key=lambda item: item[1], default=None)
    max_entry_abs = 0.0 if max_pair is None else float(max_pair[1])
    max_pair_triad_count = 0 if max_pair is None else int(pair_counts[max_pair[0]])
    return {
        "N": int(shell),
        "K": int(tail_cutoff),
        "profile_label": str(profile_label),
        "core_mode_count": int(len(core)),
        "tail_mode_count": int(len(tail)),
        "active_cross_pair_count": int(len(pair_weights)),
        "row_sum_sup": float(np.max(row_sums)) if len(row_sums) else 0.0,
        "column_sum_sup": float(np.max(col_sums)) if len(col_sums) else 0.0,
        "max_cross_entry_abs": max_entry_abs,
        "N_times_row_sum_sup": float(shell) * (float(np.max(row_sums)) if len(row_sums) else 0.0),
        "N_squared_times_column_sum_sup": float(shell * shell) * (float(np.max(col_sums)) if len(col_sums) else 0.0),
        "N_pow_3_over_2_times_max_cross_entry_abs": (float(shell) ** 1.5) * max_entry_abs,
        "max_cross_entry_contributing_edges": max_pair_triad_count,
        "positive_sector_only": True,
        "signed_acl_factor_survives": False,
        "absolute_acl_factor_survives": False,
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
        forced_profile, forced_metrics = _streaming_profile(
            modes=shell_modes,
            probability=forced_probability,
            shell_levels=shell_levels,
            zero_eps=float(args.zero_eps),
            profile_id=f"forced_tail_K{tail_cutoff}_eta_{float(args.tail_eta):.3f}",
        )
        forced_row = _cross_pair_stats(
            forced_profile,
            shell_levels,
            shell=int(shell),
            tail_cutoff=tail_cutoff,
            zero_eps=float(args.zero_eps),
            profile_label="forced_tail",
        )
        forced_row["triad_count"] = int(forced_metrics["triad_count"])
        forced_row["profile_retained_triad_count"] = int(forced_metrics["profile_retained_triad_count"])

        uniform_probability = _uniform_profile(len(shell_modes))
        uniform_profile, uniform_metrics = _streaming_profile(
            modes=shell_modes,
            probability=uniform_probability,
            shell_levels=shell_levels,
            zero_eps=float(args.zero_eps),
            profile_id="uniform_all_modes",
        )
        uniform_row = _cross_pair_stats(
            uniform_profile,
            shell_levels,
            shell=int(shell),
            tail_cutoff=tail_cutoff,
            zero_eps=float(args.zero_eps),
            profile_label="uniform_all_modes",
        )
        uniform_row["triad_count"] = int(uniform_metrics["triad_count"])
        uniform_row["profile_retained_triad_count"] = int(uniform_metrics["profile_retained_triad_count"])

        rows.append(
            {
                "N": int(shell),
                "K": int(tail_cutoff),
                "forced_tail": forced_row,
                "uniform_all_modes": uniform_row,
                "profile_dependence_ratio_max_cross_entry": (
                    forced_row["max_cross_entry_abs"] / max(uniform_row["max_cross_entry_abs"], 1.0e-300)
                ),
                "profile_dependence_ratio_row_sum_sup": (
                    forced_row["row_sum_sup"] / max(uniform_row["row_sum_sup"], 1.0e-300)
                ),
                "profile_dependence_ratio_column_sum_sup": (
                    forced_row["column_sum_sup"] / max(uniform_row["column_sum_sup"], 1.0e-300)
                ),
            }
        )
        log(
            "derived shell kernel rows",
            shell=shell,
            forced_max_cross_entry_abs=forced_row["max_cross_entry_abs"],
            uniform_max_cross_entry_abs=uniform_row["max_cross_entry_abs"],
        )
    return rows, warnings


def _analysis_read(rows: list[dict[str, Any]]) -> str:
    if not rows:
        return "No sampled shells were reconstructed."

    forced_max = [float(row["forced_tail"]["max_cross_entry_abs"]) for row in rows]
    uniform_max = [float(row["uniform_all_modes"]["max_cross_entry_abs"]) for row in rows]
    forced_scaled = [float(row["forced_tail"]["N_pow_3_over_2_times_max_cross_entry_abs"]) for row in rows]
    ratios = [float(row["profile_dependence_ratio_max_cross_entry"]) for row in rows]

    def fmt(value: float) -> str:
        return f"{value:.6g}"

    return (
        "Kernel-match decision: failed.  The exact DASHI cross-block entry carries "
        "profile amplitudes sqrt(pi_i*pi_j*pi_l)/3 and the positive-sector truncation "
        "max(cos(closure),0), so the signed ACL factor does not survive entrywise and "
        "the kernel is not profile-independent.  On the sampled shells, forced-tail max "
        f"cross entries span {fmt(min(forced_max))}..{fmt(max(forced_max))}, the uniform "
        f"all-mode comparison spans {fmt(min(uniform_max))}..{fmt(max(uniform_max))}, and "
        f"their ratio spans {fmt(min(ratios))}..{fmt(max(ratios))}.  The forced-tail "
        f"N^(3/2) * max-entry normalization stays in {fmt(min(forced_scaled))}..{fmt(max(forced_scaled))}, "
        "which is compatible with a shell-count story but does not repair the lost sign "
        "cancellation or the profile dependence."
    )


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    lines = [
        "# NS Triad K_N L_FT Kernel ACL Match",
        "",
        f"- status: `{payload['status']}`",
        f"- kernel match status: `{payload['kernel_match_status']}`",
        f"- positive sector survives ACL: `{payload['positive_sector_survives_acl']}`",
        f"- absolute sector survives ACL: `{payload['absolute_sector_survives_acl']}`",
        f"- Schur lift available: `{payload['schur_lift_available']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        "",
        "## Exact Formula",
        "",
        payload["exact_dashi_entry_formula"],
        "",
        "## ACL Target",
        "",
        payload["acl_candidate_formula"],
        "",
        "## Sampled Rows",
        "",
        "| N | K | profile | active pairs | row sup | col sup | max entry | N^(3/2)*max entry |",
        "|---:|---:|---|---:|---:|---:|---:|---:|",
    ]
    for row in payload["rows"]:
        for key in ("forced_tail", "uniform_all_modes"):
            block = row[key]
            lines.append(
                f"| {row['N']} | {row['K']} | {key} | {block['active_cross_pair_count']} | "
                f"{fmt(block['row_sum_sup'])} | {fmt(block['column_sum_sup'])} | "
                f"{fmt(block['max_cross_entry_abs'])} | {fmt(block['N_pow_3_over_2_times_max_cross_entry_abs'])} |"
            )
    lines.extend(
        [
            "",
            "## Profile Dependence",
            "",
            "| N | max-entry ratio forced/uniform | row-sup ratio | col-sup ratio |",
            "|---:|---:|---:|---:|",
        ]
    )
    for row in payload["rows"]:
        lines.append(
            f"| {row['N']} | {fmt(row['profile_dependence_ratio_max_cross_entry'])} | "
            f"{fmt(row['profile_dependence_ratio_row_sum_sup'])} | {fmt(row['profile_dependence_ratio_column_sum_sup'])} |"
        )
    lines.extend(
        [
            "",
            "## Decision",
            "",
            payload["analysis_read"],
            "",
            "## Scaling",
            "",
            f"- forced-tail max entry stats: `{payload['forced_tail_max_cross_entry_abs_stats']}`",
            f"- forced-tail N^(3/2) max entry stats: `{payload['forced_tail_n_pow_3_over_2_max_cross_entry_abs_stats']}`",
            f"- profile-dependence max-entry ratio stats: `{payload['profile_dependence_ratio_max_cross_entry_stats']}`",
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
        "started kernel match audit",
        output_dir=str(args.output_dir),
        shells=[int(shell) for shell in args.shells],
        tail_eta=float(args.tail_eta),
    )
    rows, warnings = _build_rows(args, log)
    forced_max = [float(row["forced_tail"]["max_cross_entry_abs"]) for row in rows]
    forced_scaled = [float(row["forced_tail"]["N_pow_3_over_2_times_max_cross_entry_abs"]) for row in rows]
    profile_ratios = [float(row["profile_dependence_ratio_max_cross_entry"]) for row in rows]
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
        "kernel_match_status": "failed",
        "positive_sector_survives_acl": False,
        "absolute_sector_survives_acl": False,
        "schur_lift_available": False,
        "profile_independent_bound_closed": False,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "terminal_promoted": False,
        "exact_dashi_entry_formula": EXACT_DASHI_ENTRY_FORMULA,
        "acl_candidate_formula": ACL_CANDIDATE_FORMULA,
        "rows": rows,
        "row_count": len(rows),
        "profile_amplitude_factor_present": True,
        "positive_sector_truncation_present": True,
        "signed_acl_factor_survives": False,
        "analysis_read": _analysis_read(rows),
        "forced_tail_max_cross_entry_abs_stats": _ratio_stats(forced_max),
        "forced_tail_n_pow_3_over_2_max_cross_entry_abs_stats": _ratio_stats(forced_scaled),
        "profile_dependence_ratio_max_cross_entry_stats": _ratio_stats(profile_ratios),
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
            "message": "wrote kernel match artifacts",
            "output_json": str(output_json),
            "output_md": str(output_md),
        }
    )
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
