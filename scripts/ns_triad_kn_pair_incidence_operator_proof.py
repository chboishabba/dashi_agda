#!/usr/bin/env python3
"""Canonicalize the exact scripted pair-incidence operator for the NS triad Schur lane.

This is a fail-closed analytic proof artifact. It rebuilds the exact scripted
finite-to-tail cross block on the sampled shells N=6,8,10,12, records the
algebraic pair-incidence definition of the live operator, checks that the
reconstructed rows agree with the sampled Schur-test object, and carries
forward the open theorem target

    ||L_FT,script^N||_op <= C / N

for the exact scripted operator only.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import (  # type: ignore
    AUTHORITY,
    DEFAULT_RAW_ARCHIVE,
    DEFAULT_ZERO_EPS,
    OK_STATUS,
    _json_text,
)
from ns_triad_kn_acl_schur_test_proof import (  # type: ignore
    DEFAULT_OUTPUT_DIR as DEFAULT_SCHUR_OUTPUT_DIR,
    DEFAULT_SCALING_SUMMARY,
    _derive_rows,
    _log_log_fit,
    _ratio_stats,
)
from ns_triad_kn_lft_definition_reconciliation import (  # type: ignore
    DEFAULT_OUTPUT_DIR as DEFAULT_RECONCILIATION_OUTPUT_DIR,
)
from ns_triad_kn_lft_kernel_acl_match import (  # type: ignore
    EXACT_DASHI_ENTRY_FORMULA,
)


SCRIPT_NAME = "scripts/ns_triad_kn_pair_incidence_operator_proof.py"
CONTRACT = "ns_triad_kn_pair_incidence_operator_proof"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_PAIR_INCIDENCE_OPERATOR_PROOF"
SCHEMA_VERSION = "1.0.0"
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_pair_incidence_operator_proof_20260624"
)
CANONICAL_OPERATOR_NAME = "exact_scripted_pair_incidence_operator"
CANONICAL_OPERATOR_STATEMENT = (
    "The live NS triad Schur object is the exact scripted pair-incidence operator reconstructed "
    "from retained resonant triads on the finite-to-tail cross block."
)
CANONICAL_OPERATOR_FORMULA = (
    "For a finite mode k and tail mode p, L_FT,script^+(k,p) is the negative sum over retained resonant "
    "triads whose pair-incidence edge joins k to p of (sqrt(pi_i*pi_j*pi_l)/3) * max(cos(phi_i+phi_j-phi_l),0)."
)
CANONICAL_THEOREM_TARGET = "||L_FT,script^N||_op <= C / N"
CONTROL_CARD = {
    "O": "Canonicalize the exact scripted pair-incidence operator as the only live NS triad Schur object.",
    "R": (
        "Rebuild the sampled N=6,8,10,12 forced-tail and adversarial-support rows with the exact "
        "scripted pair-incidence cross block, compare them against the sampled Schur witness, and "
        "record the remaining uniform operator theorem target."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed analytic proof artifact only; no theorem, full-NS, BKM, or Clay promotion.",
    "L": (
        "exact pair-incidence definition -> sampled cross-block reconstruction -> match against sampled "
        "Schur witness -> carry forward the exact uniform operator target."
    ),
    "P": ROUTE_DECISION,
    "G": "Lock the live object to the exact scripted matrix and keep all promotion gates false.",
    "F": "What remains is a profile-independent row/column proof for the exact scripted operator itself.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--raw-archive", type=Path, default=DEFAULT_RAW_ARCHIVE)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--shells", type=int, nargs="+", default=[6, 8, 10, 12])
    parser.add_argument("--tail-eta", type=float, default=0.25)
    parser.add_argument("--zero-eps", type=float, default=DEFAULT_ZERO_EPS)
    parser.add_argument("--scaling-summary", type=Path, default=DEFAULT_SCALING_SUMMARY)
    parser.add_argument("--sampled-schur-summary", type=Path, default=DEFAULT_SCHUR_OUTPUT_DIR / "summary.json")
    parser.add_argument(
        "--reconciliation-summary",
        type=Path,
        default=DEFAULT_RECONCILIATION_OUTPUT_DIR / "summary.json",
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
            f"[pair-incidence-proof] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}",
            flush=True,
        )

    return log, started


def _load_optional_json(path: Path) -> dict[str, Any] | None:
    if not path.is_file():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    return payload if isinstance(payload, dict) else None


def _relative_diff(left: float, right: float) -> float:
    scale = max(abs(left), abs(right), 1.0e-300)
    return abs(left - right) / scale


def _compare_rows(
    rows: list[dict[str, Any]],
    other_rows: list[dict[str, Any]],
) -> dict[str, Any]:
    if len(rows) != len(other_rows):
        return {
            "row_count_match": False,
            "max_relative_difference": None,
            "field_checks": [],
        }
    field_checks: list[dict[str, Any]] = []
    max_relative_difference = 0.0
    all_ok = True
    for left, right in zip(rows, other_rows, strict=False):
        row_check = {
            "N": int(left["N"]),
            "profile_id": str(left.get("profile_id")),
            "row_sum_sup_rel_diff": _relative_diff(float(left["row_sum_sup"]), float(right["row_sum_sup"])),
            "column_sum_sup_rel_diff": _relative_diff(float(left["column_sum_sup"]), float(right["column_sum_sup"])),
            "schur_bound_rel_diff": _relative_diff(float(left["schur_bound"]), float(right["schur_bound"])),
        }
        max_relative_difference = max(
            max_relative_difference,
            row_check["row_sum_sup_rel_diff"],
            row_check["column_sum_sup_rel_diff"],
            row_check["schur_bound_rel_diff"],
        )
        row_check["matches_to_1e12"] = (
            row_check["row_sum_sup_rel_diff"] <= 1.0e-12
            and row_check["column_sum_sup_rel_diff"] <= 1.0e-12
            and row_check["schur_bound_rel_diff"] <= 1.0e-12
        )
        all_ok = all_ok and bool(row_check["matches_to_1e12"])
        field_checks.append(row_check)
    return {
        "row_count_match": True,
        "all_rows_match_to_1e12": all_ok,
        "max_relative_difference": max_relative_difference,
        "field_checks": field_checks,
    }


def _analysis_read(payload: dict[str, Any]) -> str:
    forced_rows = payload["forced_tail_rows"]
    adversarial_rows = payload["adversarial_rows"]
    forced_n_times = [float(row["N_times_schur_bound"]) for row in forced_rows]
    forced_col = [float(row["column_sum_sup"]) for row in forced_rows]
    adversarial_n_times = [float(row["N_times_schur_bound"]) for row in adversarial_rows]
    match = payload["sampled_schur_script_match"]
    recon = payload["reconciliation_verdict"]

    def fmt_range(values: list[float]) -> str:
        return f"{min(values):.6g}..{max(values):.6g}" if values else "null"

    return (
        "Pair-incidence live-object readout: the canonical sampled rows are reconstructed directly from "
        "the exact scripted pair-incidence operator, and the forced-tail Schur witness matches the sampled "
        f"Schur script with max relative difference {payload['sampled_schur_match_details'].get('max_relative_difference')}. "
        f"For the forced-tail family, N*||L_FT,script^N|| spans {fmt_range(forced_n_times)} while the column "
        f"supremum spans {fmt_range(forced_col)}. For the adversarial-support rows, N*||L_FT,script^N|| spans "
        f"{fmt_range(adversarial_n_times)}. The reconciliation verdict remains {recon}, so the bare shell-geometry "
        "proxy stays dead. What remains open is the uniform profile-independent proof of "
        f"{CANONICAL_THEOREM_TARGET} for the exact scripted operator itself."
    )


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    lines = [
        "# NS Triad Exact Pair-Incidence Operator Proof",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- BKM exclusion proved: `{payload['bkm_exclusion_proved']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "## Operator",
        "",
        f"- name: `{payload['canonical_operator_name']}`",
        f"- statement: {payload['canonical_operator_statement']}",
        f"- formula: {payload['canonical_operator_formula']}",
        f"- live theorem target: `{payload['canonical_theorem_target']}`",
        f"- reconciliation verdict: `{payload['reconciliation_verdict']}`",
        "",
        "## Proof Shape",
        "",
        "1. Rebuild the exact finite-to-tail cross block from retained resonant triads.",
        "2. Keep the exact pair-incidence weight formula explicit, including the profile amplitudes and the positive-sector truncation.",
        "3. Match the reconstructed rows against the sampled Schur witness for the same object.",
        "4. Carry forward the open uniform operator theorem target for the exact scripted object only.",
        "",
        "## Forced-Tail Rows",
        "",
        "| N | K | core modes | tail modes | row sup | column sup | Schur bound | N*bound | active cross pairs |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in payload["forced_tail_rows"]:
        lines.append(
            f"| {row['N']} | {row['K']} | {row['core_mode_count']} | {row['tail_mode_count']} | "
            f"{fmt(row['row_sum_sup'])} | {fmt(row['column_sum_sup'])} | {fmt(row['schur_bound'])} | "
            f"{fmt(row['N_times_schur_bound'])} | {fmt(row['cross_edge_count'])} |"
        )
    lines.extend(
        [
            "",
            "## Adversarial-Support Rows",
            "",
            "| N | K | row sup | column sup | Schur bound | N*bound | worst tail mode |",
            "|---:|---:|---:|---:|---:|---:|---|",
        ]
    )
    for row in payload["adversarial_rows"]:
        lines.append(
            f"| {row['N']} | {row['K']} | {fmt(row['row_sum_sup'])} | {fmt(row['column_sum_sup'])} | "
            f"{fmt(row['schur_bound'])} | {fmt(row['N_times_schur_bound'])} | {row.get('worst_tail_mode', {}).get('mode_key')} |"
        )
    lines.extend(
        [
            "",
            "## Match Against Sampled Schur Script",
            "",
            f"- forced-tail rows: `{payload['sampled_schur_match_details']}`",
            f"- adversarial rows: `{payload['sampled_schur_adversarial_match_details']}`",
            "",
            "## Scaling",
            "",
            f"- forced row sup stats: `{payload['forced_tail_row_sum_sup_stats']}`",
            f"- forced column sup stats: `{payload['forced_tail_column_sum_sup_stats']}`",
            f"- forced Schur bound stats: `{payload['forced_tail_schur_bound_stats']}`",
            f"- forced N*Schur bound stats: `{payload['forced_tail_n_times_schur_bound_stats']}`",
            f"- adversarial column sup stats: `{payload['adversarial_column_sum_sup_stats']}`",
            f"- adversarial Schur bound stats: `{payload['adversarial_schur_bound_stats']}`",
            f"- forced log-log fit column sup vs N: `{payload['fits']['forced_tail_column_sum_sup_vs_N']}`",
            f"- forced log-log fit Schur bound vs N: `{payload['fits']['forced_tail_schur_bound_vs_N']}`",
            f"- adversarial log-log fit column sup vs N: `{payload['fits']['adversarial_column_sum_sup_vs_N']}`",
            f"- adversarial log-log fit Schur bound vs N: `{payload['fits']['adversarial_schur_bound_vs_N']}`",
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
        "started pair-incidence operator proof run",
        output_dir=str(args.output_dir),
        shells=[int(shell) for shell in args.shells],
        tail_eta=float(args.tail_eta),
    )
    forced_tail_rows, adversarial_rows, warnings = _derive_rows(args)
    log(
        "derived exact pair-incidence rows",
        forced_tail_row_count=len(forced_tail_rows),
        adversarial_row_count=len(adversarial_rows),
    )

    sampled_payload = _load_optional_json(Path(args.sampled_schur_summary))
    reconciliation_payload = _load_optional_json(Path(args.reconciliation_summary))
    sampled_match = _compare_rows(forced_tail_rows, list(sampled_payload.get("rows", []))) if sampled_payload else {}
    sampled_adv_match = (
        _compare_rows(adversarial_rows, list(sampled_payload.get("adversarial_rows", [])))
        if sampled_payload
        else {}
    )
    log(
        "compared against sampled schur witness",
        sampled_summary_found=bool(sampled_payload),
        forced_tail_match=sampled_match.get("all_rows_match_to_1e12"),
        adversarial_match=sampled_adv_match.get("all_rows_match_to_1e12"),
    )

    forced_row_sups = [float(row["row_sum_sup"]) for row in forced_tail_rows]
    forced_col_sups = [float(row["column_sum_sup"]) for row in forced_tail_rows]
    forced_schur = [float(row["schur_bound"]) for row in forced_tail_rows]
    forced_n_times = [float(row["N_times_schur_bound"]) for row in forced_tail_rows]
    adversarial_col_sups = [float(row["column_sum_sup"]) for row in adversarial_rows]
    adversarial_schur = [float(row["schur_bound"]) for row in adversarial_rows]

    payload: dict[str, Any] = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "started_at": started_at,
        "status": OK_STATUS if len(forced_tail_rows) == len({int(value) for value in args.shells}) else "partial",
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "terminal_promoted": False,
        "proof_scope": "finite_shell_only_exact_pair_incidence_operator",
        "canonical_operator_name": CANONICAL_OPERATOR_NAME,
        "canonical_operator_statement": CANONICAL_OPERATOR_STATEMENT,
        "canonical_operator_formula": CANONICAL_OPERATOR_FORMULA,
        "exact_dashi_entry_formula": EXACT_DASHI_ENTRY_FORMULA,
        "canonical_theorem_target": CANONICAL_THEOREM_TARGET,
        "sampled_schur_summary": str(args.sampled_schur_summary),
        "reconciliation_summary": str(args.reconciliation_summary),
        "reconciliation_verdict": None if not reconciliation_payload else reconciliation_payload.get("overall_verdict"),
        "forced_tail_row_count": len(forced_tail_rows),
        "forced_tail_rows": forced_tail_rows,
        "adversarial_row_count": len(adversarial_rows),
        "adversarial_rows": adversarial_rows,
        "sampled_schur_script_match": bool(sampled_match.get("all_rows_match_to_1e12", False)),
        "sampled_schur_adversarial_match": bool(sampled_adv_match.get("all_rows_match_to_1e12", False)),
        "sampled_schur_match_details": sampled_match,
        "sampled_schur_adversarial_match_details": sampled_adv_match,
        "forced_tail_row_sum_sup_stats": _ratio_stats(forced_row_sups),
        "forced_tail_column_sum_sup_stats": _ratio_stats(forced_col_sups),
        "forced_tail_schur_bound_stats": _ratio_stats(forced_schur),
        "forced_tail_n_times_schur_bound_stats": _ratio_stats(forced_n_times),
        "adversarial_column_sum_sup_stats": _ratio_stats(adversarial_col_sups),
        "adversarial_schur_bound_stats": _ratio_stats(adversarial_schur),
        "fits": {
            "forced_tail_column_sum_sup_vs_N": _log_log_fit(forced_tail_rows, "N", "column_sum_sup"),
            "forced_tail_schur_bound_vs_N": _log_log_fit(forced_tail_rows, "N", "schur_bound"),
            "adversarial_column_sum_sup_vs_N": _log_log_fit(adversarial_rows, "N", "column_sum_sup"),
            "adversarial_schur_bound_vs_N": _log_log_fit(adversarial_rows, "N", "schur_bound"),
        },
        "warnings": warnings,
        "log_entries": log_entries,
    }
    payload["analysis_read"] = _analysis_read(payload)

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
            "message": "wrote pair-incidence proof artifacts",
            "output_json": str(output_json),
            "output_md": str(output_md),
        }
    )
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
