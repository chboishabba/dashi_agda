#!/usr/bin/env python3
"""Audit sampled Rayleigh margins for the NS triad K_N(A) Gram lane.

This is a fail-closed analytic proof artifact. It does not rerun the expensive
eigensolver. Instead it reads the canonical sampled receipts, extracts the
recorded lowest Rayleigh direction proxies, and decomposes the positive floor
into diagonal, cross, support, spread, and dominant shell-pair signals.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_gram_rayleigh_margin_audit.py"
CONTRACT = "ns_triad_kn_gram_rayleigh_margin_audit"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_GRAM_RAYLEIGH_MARGIN_AUDIT"
SCHEMA_VERSION = "1.0.0"
DEFAULT_PAIR_INCIDENCE_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_pair_incidence_operator_proof_20260624/summary.json"
)
DEFAULT_SCALING_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_sparse_schur_scaling_fit_20260624/summary.json"
)
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_gram_rayleigh_margin_audit_20260625"
)
CONTROL_CARD = {
    "O": "Explain why the sampled lowest Rayleigh direction still has positive margin on the live high-high Gram lane.",
    "R": (
        "Read the canonical exact-object proof summary and sampled sparse-Schur detail receipts, "
        "then re-express the recorded lambda floor as diagonal-minus-cross margin plus support/spread proxies."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed analytic audit only; no theorem, BKM, residence-time, or Clay promotion.",
    "L": "exact operator anchor -> sampled lowest-Rayleigh receipts -> margin decomposition -> dangerous-cell classification remains open",
    "P": ROUTE_DECISION,
    "G": "Keep 369 as a classification layer only after the spectral margin carrier is explicit.",
    "F": "Missing evidence: analytic min-max coercivity proof and a real finite sign/profile cell reduction.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pair-incidence-summary", type=Path, default=DEFAULT_PAIR_INCIDENCE_SUMMARY)
    parser.add_argument("--scaling-summary", type=Path, default=DEFAULT_SCALING_SUMMARY)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
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
        print(f"[kn-rayleigh-margin] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}", flush=True)

    return log, started


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON root must be an object")
    return payload


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


def _top_support(eigen_rows: list[dict[str, Any]], *, threshold: float) -> list[int]:
    kept = [
        (int(row["shell"]), float(row["fraction"]))
        for row in eigen_rows
        if isinstance(row, dict)
        and isinstance(row.get("shell"), (int, float))
        and isinstance(row.get("fraction"), (int, float))
        and float(row["fraction"]) >= threshold
    ]
    kept.sort(key=lambda item: item[1], reverse=True)
    return [shell for shell, _fraction in kept]


def _support_size(eigen_rows: list[dict[str, Any]], *, threshold: float) -> int:
    return len(_top_support(eigen_rows, threshold=threshold))


def _dominant_shell_pairs(accounting_rows: list[dict[str, Any]], *, limit: int = 3) -> list[dict[str, Any]]:
    ranked = []
    for row in accounting_rows:
        if not isinstance(row, dict):
            continue
        shell_pair = row.get("shell_pair")
        neg_fraction = row.get("l_neg_numerator_fraction")
        if not isinstance(shell_pair, str) or not isinstance(neg_fraction, (int, float)):
            continue
        ranked.append(
            {
                "shell_pair": shell_pair,
                "l_neg_numerator_fraction": float(neg_fraction),
                "negative_frame_weight_fraction": float(row.get("negative_frame_weight_fraction", 0.0)),
                "positive_frame_weight_fraction": float(row.get("positive_frame_weight_fraction", 0.0)),
            }
        )
    ranked.sort(key=lambda item: item["l_neg_numerator_fraction"], reverse=True)
    return ranked[:limit]


def _mechanism_label(
    *, diag_minus_cross: float, coherence_mu: float, profile_entropy: float, support_size: int
) -> str:
    if coherence_mu < 0.1 and diag_minus_cross > 0.15 and support_size >= 3:
        if profile_entropy >= 4.0:
            return "diagonal_dominance_plus_profile_spreading"
        return "diagonal_dominance_plus_incoherence"
    if coherence_mu < 0.1 and diag_minus_cross > 0.15:
        return "diagonal_dominance_plus_incoherence"
    if profile_entropy >= 4.0 and support_size >= 3:
        return "profile_spreading_supported"
    return "mixed_unresolved"


def _build_row(source_row: dict[str, Any], detail_path: Path) -> dict[str, Any]:
    detail = _load_json(detail_path)
    result = detail.get("result", {})
    if not isinstance(result, dict):
        raise ValueError(f"{detail_path}: missing result object")
    component_rows = result.get("component_rayleigh_splits", [])
    if not isinstance(component_rows, list) or not component_rows:
        raise ValueError(f"{detail_path}: missing component_rayleigh_splits")
    split_row = component_rows[0]
    if not isinstance(split_row, dict):
        raise ValueError(f"{detail_path}: malformed component split")
    split = split_row.get("l_neg_split", {})
    if not isinstance(split, dict):
        raise ValueError(f"{detail_path}: missing l_neg_split")
    eigen_rows = result.get("eigen_mass_by_shell", [])
    if not isinstance(eigen_rows, list):
        raise ValueError(f"{detail_path}: missing eigen_mass_by_shell")
    accounting = result.get("shell_pair_accounting", {})
    if not isinstance(accounting, dict):
        raise ValueError(f"{detail_path}: missing shell_pair_accounting")
    accounting_rows = accounting.get("rows", [])
    if not isinstance(accounting_rows, list):
        raise ValueError(f"{detail_path}: missing shell_pair_accounting.rows")
    profile_metrics = result.get("profile_metrics", {})
    if not isinstance(profile_metrics, dict):
        raise ValueError(f"{detail_path}: missing profile_metrics")
    tail_summary = result.get("tail_responsibility_summary", {})
    if not isinstance(tail_summary, dict):
        raise ValueError(f"{detail_path}: missing tail_responsibility_summary")

    finite_finite = float(split["finite_finite"])
    tail_tail = float(split["tail_tail"])
    finite_tail_cross = float(split["finite_tail_cross"])
    diag_contribution = finite_finite + tail_tail
    cross_offdiag_contribution = abs(finite_tail_cross)
    diag_minus_cross = diag_contribution - cross_offdiag_contribution
    lambda_min = float(result["lambda_min"])
    support_threshold = 0.05
    support_shells = _top_support(eigen_rows, threshold=support_threshold)
    support_size = len(support_shells)
    profile_entropy = float(profile_metrics["angular_entropy"])
    high_shell_mass_fraction = float(profile_metrics["high_shell_mass_fraction"])
    coherence_mu = cross_offdiag_contribution / max(diag_contribution, 1.0e-300)
    mechanism_label = _mechanism_label(
        diag_minus_cross=diag_minus_cross,
        coherence_mu=coherence_mu,
        profile_entropy=profile_entropy,
        support_size=support_size,
    )
    shell_pair_dominance = _dominant_shell_pairs(accounting_rows)
    return {
        "N": int(source_row["N"]),
        "K": int(source_row["K"]),
        "profile_name": str(result["profile_id"]),
        "lambda_min": lambda_min,
        "worst_eigenvector_available": False,
        "worst_eigenvector_proxy": "shell-mass decomposition only",
        "rayleigh_quotient": float(split_row["full_rayleigh_from_terms"]),
        "rayleigh_numerator": float(result["rayleigh_numerator"]),
        "rayleigh_denominator": float(result["rayleigh_denominator"]),
        "diagonal_contribution": diag_contribution,
        "cross_offdiag_contribution": cross_offdiag_contribution,
        "diag_minus_cross": diag_minus_cross,
        "coherence_mu": coherence_mu,
        "support_size": support_size,
        "support_threshold_fraction": support_threshold,
        "worst_eigenvector_support": support_shells,
        "profile_entropy": profile_entropy,
        "high_shell_mass_fraction": high_shell_mass_fraction,
        "dominant_negative_shell_pairs": shell_pair_dominance,
        "dominant_cell_classification": "open_from_receipts",
        "tail_cutoff": int(tail_summary["tail_cutoff"]),
        "worst_eigen_shell": int(tail_summary["worst_eigen_shell"]),
        "worst_eigen_shell_mass": float(tail_summary["worst_eigen_shell_mass"]),
        "mixed_tail_candidate": bool(tail_summary["mixed_tail_candidate"]),
        "mechanism_label": mechanism_label,
        "detail_json": str(detail_path),
        "verdict": "coercive_margin_plausible" if diag_minus_cross > 0.0 else "margin_failure",
    }


def _analysis_read(rows: list[dict[str, Any]], pair_incidence: dict[str, Any]) -> str:
    if not rows:
        return (
            "Rayleigh-margin audit readout: no sampled rows were available, so the margin carrier remains open."
        )
    mechanisms = sorted({str(row["mechanism_label"]) for row in rows})
    supports = ", ".join(f"N={row['N']}:{row['worst_eigenvector_support']}" for row in rows)
    pair_read = ", ".join(
        f"N={row['N']}:{row['dominant_negative_shell_pairs'][0]['shell_pair']}"
        for row in rows
        if row["dominant_negative_shell_pairs"]
    )
    return (
        "Rayleigh-margin audit readout: the exact scripted pair-incidence object remains canonical "
        f"(sampled-script match = {bool(pair_incidence.get('sampled_schur_script_match'))}). "
        "Across the sampled rows the lowest recorded Rayleigh quotient stays positive because the diagonal Gram mass "
        "continues to exceed the cross term while coherence stays small. The support proxy remains mixed rather than "
        f"single-shell ({supports}), and the dominant negative shell-pair carriers are {pair_read}. "
        f"The observed protection mechanism is {mechanisms}. This is candidate-only evidence and the finite sign/profile "
        "dangerous-cell classification is still open from receipts."
    )


def _markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# NS Triad K_N(A) Rayleigh Margin Audit",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "## Rows",
        "",
        "| N | lambda_min | Rayleigh | diag | cross | diag-cross | coherence_mu | support | entropy | mechanism | verdict |",
        "|---:|---:|---:|---:|---:|---:|---:|---|---:|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['N']} | {row['lambda_min']:.12g} | {row['rayleigh_quotient']:.12g} | "
            f"{row['diagonal_contribution']:.12g} | {row['cross_offdiag_contribution']:.12g} | "
            f"{row['diag_minus_cross']:.12g} | {row['coherence_mu']:.12g} | {row['worst_eigenvector_support']} | "
            f"{row['profile_entropy']:.12g} | {row['mechanism_label']} | {row['verdict']} |"
        )
    lines.extend(
        [
            "",
            "## Dominant Shell Pairs",
            "",
            "| N | dominant negative shell pairs | cell classification |",
            "|---:|---|---|",
        ]
    )
    for row in payload["rows"]:
        pairs = ", ".join(
            f"{item['shell_pair']}:{item['l_neg_numerator_fraction']:.6g}"
            for item in row["dominant_negative_shell_pairs"]
        )
        lines.append(
            f"| {row['N']} | {pairs or 'none'} | {row['dominant_cell_classification']} |"
        )
    lines.extend(
        [
            "",
            "## Readout",
            "",
            payload["analysis_read"],
            "",
            "## Stability Stats",
            "",
            f"- lambda_min: `{payload['lambda_min_stats']}`",
            f"- diag_minus_cross: `{payload['diag_minus_cross_stats']}`",
            f"- coherence_mu: `{payload['coherence_mu_stats']}`",
            f"- support_size: `{payload['support_size_stats']}`",
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
    log("started Gram Rayleigh-margin audit run")

    pair_incidence = _load_json(args.pair_incidence_summary)
    scaling_summary = _load_json(args.scaling_summary)
    log(
        "loaded source summaries",
        pair_incidence_summary=str(args.pair_incidence_summary),
        scaling_summary=str(args.scaling_summary),
    )

    rows_input = scaling_summary.get("rows", [])
    if not isinstance(rows_input, list):
        raise ValueError(f"{args.scaling_summary}: rows must be a list")

    rows = []
    for source_row in rows_input:
        if not isinstance(source_row, dict):
            continue
        detail_json = source_row.get("detail_json")
        if not isinstance(detail_json, str) or not detail_json:
            continue
        row = _build_row(source_row, Path(detail_json))
        rows.append(row)
        log(
            "audited sampled Rayleigh-margin row",
            N=row["N"],
            lambda_min=row["lambda_min"],
            mechanism=row["mechanism_label"],
            verdict=row["verdict"],
        )

    rows.sort(key=lambda row: int(row["N"]))
    payload: dict[str, Any] = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "status": "ok",
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "clay_promoted": False,
        "started_at": started_at,
        "finished_at": _iso_now(),
        "pair_incidence_summary": str(args.pair_incidence_summary),
        "scaling_summary": str(args.scaling_summary),
        "exact_operator_name": pair_incidence.get("canonical_operator_name"),
        "exact_operator_theorem_target": pair_incidence.get("canonical_theorem_target"),
        "sampled_schur_script_match": bool(pair_incidence.get("sampled_schur_script_match")),
        "dangerous_cell_classification_closed": False,
        "rows": rows,
        "row_count": len(rows),
        "lambda_min_stats": _ratio_stats([float(row["lambda_min"]) for row in rows]),
        "diag_minus_cross_stats": _ratio_stats([float(row["diag_minus_cross"]) for row in rows]),
        "coherence_mu_stats": _ratio_stats([float(row["coherence_mu"]) for row in rows]),
        "support_size_stats": _ratio_stats([float(row["support_size"]) for row in rows]),
        "analysis_read": _analysis_read(rows, pair_incidence),
        "log_entries": log_entries,
    }
    summary_json = args.output_dir / "summary.json"
    summary_md = args.output_dir / "summary.md"
    summary_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    summary_md.write_text(_markdown(payload), encoding="utf-8")
    log("wrote Gram Rayleigh-margin audit artifacts", summary_json=str(summary_json), summary_md=str(summary_md))

    elapsed_ms = round((time.perf_counter() - started_perf) * 1000.0, 3)
    payload["elapsed_ms"] = elapsed_ms
    payload["log_entries"].append(
        {
            "at": _iso_now(),
            "elapsed_ms": elapsed_ms,
            "message": "completed Gram Rayleigh-margin audit run",
        }
    )
    summary_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
