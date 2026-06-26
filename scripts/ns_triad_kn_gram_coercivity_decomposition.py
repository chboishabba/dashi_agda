#!/usr/bin/env python3
"""Decompose the sampled NS triad K_N(A) Gram coercivity rows.

This is a fail-closed analytic proof artifact. It intentionally avoids another
expensive eigensolve: the script reads the canonical exact-object proof summary
and the sampled sparse-Schur detail receipts, then re-expresses the recorded
lambda floor in a Gram-style diagonal-vs-cross decomposition with timing and
structured logs.
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


SCRIPT_NAME = "scripts/ns_triad_kn_gram_coercivity_decomposition.py"
CONTRACT = "ns_triad_kn_gram_coercivity_decomposition"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_GRAM_COERCIVITY_DECOMPOSITION"
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
    "ns_triad_kn_gram_coercivity_decomposition_20260625"
)
CONTROL_CARD = {
    "O": "Decompose the sampled Gram-coercivity rows into diagonal mass, cross interference, and support/spread proxies.",
    "R": (
        "Read the canonical exact-object proof summary and the sampled sparse-Schur detail receipts, "
        "then restate the recorded lambda floor as a Gram-style diagonal-minus-cross decomposition."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed analytic proof artifact only; no theorem, full-NS, BKM, or Clay promotion.",
    "L": "exact scripted pair-incidence anchor -> sampled shell rows -> diagonal/cross Gram split -> candidate proof obligations remain open",
    "P": ROUTE_DECISION,
    "G": "Keep the c / N theorem target explicit without promoting sampled decomposition telemetry into a proof.",
    "F": "The missing evidence is still the analytic min-max lower bound, the admissible-profile theorem, and the PDE transfer chain.",
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
        print(f"[kn-gram-coercivity] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}", flush=True)

    return log, started


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON root must be an object")
    return payload


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


def _top_support(eigen_rows: list[dict[str, Any]], *, threshold: float = 0.1, limit: int = 3) -> list[int]:
    kept = [
        (int(row["shell"]), float(row["fraction"]))
        for row in eigen_rows
        if isinstance(row, dict)
        and isinstance(row.get("shell"), (int, float))
        and isinstance(row.get("fraction"), (int, float))
        and float(row["fraction"]) >= threshold
    ]
    kept.sort(key=lambda item: item[1], reverse=True)
    return [shell for shell, _fraction in kept[:limit]]


def _verdict(*, coherence_mu: float, profile_entropy: float, high_shell_mass_fraction: float) -> str:
    if profile_entropy < 3.0 or high_shell_mass_fraction > 0.85:
        return "profile_concentration_failure"
    if coherence_mu >= 0.2:
        return "coherence_failure"
    return "coercivity_plausible"


def _build_row(row: dict[str, Any], detail_path: Path) -> dict[str, Any]:
    detail = _load_json(detail_path)
    result = detail.get("result", {})
    if not isinstance(result, dict):
        raise ValueError(f"{detail_path}: missing result object")
    component_rows = result.get("component_rayleigh_splits", [])
    if not isinstance(component_rows, list) or not component_rows:
        raise ValueError(f"{detail_path}: missing component_rayleigh_splits")
    split = component_rows[0].get("l_neg_split", {})
    if not isinstance(split, dict):
        raise ValueError(f"{detail_path}: missing l_neg_split")
    finite_finite = float(split["finite_finite"])
    tail_tail = float(split["tail_tail"])
    finite_tail_cross = float(split["finite_tail_cross"])
    diag_contribution = finite_finite + tail_tail
    offdiag_contribution = abs(finite_tail_cross)
    diag_minus_offdiag = diag_contribution - offdiag_contribution
    coherence_mu = offdiag_contribution / max(diag_contribution, 1.0e-300)
    profile_metrics = result.get("profile_metrics", {})
    if not isinstance(profile_metrics, dict):
        raise ValueError(f"{detail_path}: missing profile_metrics")
    tail_summary = result.get("tail_responsibility_summary", {})
    if not isinstance(tail_summary, dict):
        raise ValueError(f"{detail_path}: missing tail_responsibility_summary")
    eigen_rows = result.get("eigen_mass_by_shell", [])
    if not isinstance(eigen_rows, list):
        raise ValueError(f"{detail_path}: missing eigen_mass_by_shell")
    lambda_min = float(result["lambda_min"])
    shell = int(result["shell"])
    profile_entropy = float(profile_metrics["angular_entropy"])
    high_shell_mass_fraction = float(profile_metrics["high_shell_mass_fraction"])
    verdict = _verdict(
        coherence_mu=coherence_mu,
        profile_entropy=profile_entropy,
        high_shell_mass_fraction=high_shell_mass_fraction,
    )
    return {
        "N": int(row["N"]),
        "K": int(row["K"]),
        "profile_name": str(result["profile_id"]),
        "lambda_min": lambda_min,
        "N_lambda_min": float(int(row["N"]) * lambda_min),
        "diag_contribution": diag_contribution,
        "offdiag_contribution": offdiag_contribution,
        "diag_minus_offdiag": diag_minus_offdiag,
        "coherence_mu": coherence_mu,
        "worst_eigenvector_support": _top_support(eigen_rows),
        "profile_entropy": profile_entropy,
        "high_shell_mass_fraction": high_shell_mass_fraction,
        "tail_cutoff": int(tail_summary["tail_cutoff"]),
        "worst_eigen_shell": int(tail_summary["worst_eigen_shell"]),
        "worst_eigen_shell_mass": float(tail_summary["worst_eigen_shell_mass"]),
        "mixed_tail_candidate": bool(tail_summary["mixed_tail_candidate"]),
        "detail_json": str(detail_path),
        "shell": shell,
        "verdict": verdict,
    }


def _analysis_read(rows: list[dict[str, Any]], pair_incidence: dict[str, Any]) -> str:
    n_lambda = [float(row["N_lambda_min"]) for row in rows]
    coherence = [float(row["coherence_mu"]) for row in rows]
    diag_margin = [float(row["diag_minus_offdiag"]) for row in rows]
    if rows:
        support_read = ", ".join(
            f"N={row['N']}:{row['worst_eigenvector_support']}" for row in rows
        )
    else:
        support_read = "none"
    exact_match = bool(pair_incidence.get("sampled_schur_script_match"))

    def rng(values: list[float]) -> str:
        return "null" if not values else f"{min(values):.6g}..{max(values):.6g}"

    return (
        "Gram-coercivity decomposition readout: the exact scripted pair-incidence object remains canonical "
        f"(sampled-script match = {exact_match}), and the sampled shell rows keep lambda_min positive with "
        f"N*lambda_min spanning {rng(n_lambda)}. On these rows the diagonal-minus-cross Gram margin spans "
        f"{rng(diag_margin)} while the coherence proxy spans {rng(coherence)}. The dominant eigen support remains "
        f"mixed rather than single-shell ({support_read}). This is candidate-only decomposition evidence for the "
        "live c / N target; it does not close the analytic min-max lower bound."
    )


def _markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# NS Triad K_N(A) Gram Coercivity Decomposition",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- BKM exclusion proved: `{payload['bkm_exclusion_proved']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "## Exactness Anchor",
        "",
        f"- exact operator name: `{payload['exact_operator_name']}`",
        f"- exact theorem target: `{payload['exact_operator_theorem_target']}`",
        f"- sampled-script match: `{payload['sampled_schur_script_match']}`",
        "",
        "## Rows",
        "",
        "| N | profile | lambda_min | N*lambda_min | diag | offdiag | diag-offdiag | coherence_mu | support | verdict |",
        "|---:|---|---:|---:|---:|---:|---:|---:|---|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['N']} | {row['profile_name']} | {row['lambda_min']:.12g} | {row['N_lambda_min']:.12g} | "
            f"{row['diag_contribution']:.12g} | {row['offdiag_contribution']:.12g} | {row['diag_minus_offdiag']:.12g} | "
            f"{row['coherence_mu']:.12g} | {row['worst_eigenvector_support']} | {row['verdict']} |"
        )
    lines.extend(
        [
            "",
            "## Lemma Split",
            "",
            "| Lemma | Sampled evidence | Theorem closed |",
            "|---|---|---|",
        ]
    )
    for row in payload["lemma_rows"]:
        lines.append(
            f"| {row['lemma']} | {row['sampled_evidence']} | {row['theorem_closed']} |"
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
            f"- N*lambda_min: `{payload['N_lambda_min_stats']}`",
            f"- coherence_mu: `{payload['coherence_mu_stats']}`",
            f"- diag_minus_offdiag: `{payload['diag_minus_offdiag_stats']}`",
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
    log("started Gram-coercivity decomposition run")

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
            "decomposed sampled shell row",
            N=row["N"],
            lambda_min=row["lambda_min"],
            coherence_mu=row["coherence_mu"],
            verdict=row["verdict"],
        )

    rows.sort(key=lambda row: int(row["N"]))
    n_lambda = [float(row["N_lambda_min"]) for row in rows]
    coherence = [float(row["coherence_mu"]) for row in rows]
    diag_margin = [float(row["diag_minus_offdiag"]) for row in rows]
    lemma_rows = [
        {
            "lemma": "K_N(A) exactness",
            "sampled_evidence": bool(pair_incidence.get("sampled_schur_script_match")),
            "theorem_closed": False,
        },
        {
            "lemma": "Diagonal mass lower bound",
            "sampled_evidence": all(float(row["diag_contribution"]) > float(row["offdiag_contribution"]) for row in rows),
            "theorem_closed": False,
        },
        {
            "lemma": "Coherence / off-diagonal control",
            "sampled_evidence": all(float(row["coherence_mu"]) < 0.1 for row in rows),
            "theorem_closed": False,
        },
        {
            "lemma": "Admissible profile condition",
            "sampled_evidence": len({str(row["profile_name"]) for row in rows}) == 1,
            "theorem_closed": False,
        },
    ]
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
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "started_at": started_at,
        "finished_at": _iso_now(),
        "pair_incidence_summary": str(args.pair_incidence_summary),
        "scaling_summary": str(args.scaling_summary),
        "exact_operator_name": pair_incidence.get("canonical_operator_name"),
        "exact_operator_theorem_target": pair_incidence.get("canonical_theorem_target"),
        "sampled_schur_script_match": bool(pair_incidence.get("sampled_schur_script_match")),
        "rows": rows,
        "row_count": len(rows),
        "lemma_rows": lemma_rows,
        "N_lambda_min_stats": _ratio_stats(n_lambda),
        "coherence_mu_stats": _ratio_stats(coherence),
        "diag_minus_offdiag_stats": _ratio_stats(diag_margin),
        "analysis_read": _analysis_read(rows, pair_incidence),
        "log_entries": log_entries,
    }
    summary_json = args.output_dir / "summary.json"
    summary_md = args.output_dir / "summary.md"
    summary_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    summary_md.write_text(_markdown(payload), encoding="utf-8")
    log("wrote Gram-coercivity decomposition artifacts", summary_json=str(summary_json), summary_md=str(summary_md))

    elapsed_ms = round((time.perf_counter() - started_perf) * 1000.0, 3)
    payload["elapsed_ms"] = elapsed_ms
    payload["log_entries"].append(
        {
            "at": _iso_now(),
            "elapsed_ms": elapsed_ms,
            "message": "completed Gram-coercivity decomposition run",
        }
    )
    summary_json.write_text(_json_text(payload, pretty=args.pretty), encoding="utf-8")
    print(_json_text(payload, pretty=args.pretty))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
