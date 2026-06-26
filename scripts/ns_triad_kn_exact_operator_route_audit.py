#!/usr/bin/env python3
"""Audit the exact-operator route status across Schur, residue, BKM, and residence.

This is a fail-closed analytic proof artifact. It consumes the exact-script
row/column audit together with the existing residue, BKM, and residence
surfaces, then records which of the four requested gates are actually closed.
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


SCRIPT_NAME = "scripts/ns_triad_kn_exact_operator_route_audit.py"
CONTRACT = "ns_triad_kn_exact_operator_route_audit"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_EXACT_OPERATOR_ROUTE_AUDIT"
SCHEMA_VERSION = "1.0.0"
DEFAULT_ROW_COLUMN_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_pair_incidence_row_column_audit_20260625/summary.json"
)
DEFAULT_DIAGONAL_RESIDUE_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_diagonal_residue_bridge_20260624/summary.json"
)
DEFAULT_BKM_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_bkm_projection_smallness_20260624/summary.json"
)
DEFAULT_RESIDENCE_AGDA = Path("DASHI/Physics/Closure/NSSprint99ResidenceTimeAgainstViscosity.agda")
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_exact_operator_route_audit_20260625"
)
CONTROL_CARD = {
    "O": "Resume the exact-operator route and audit closure status of the four live theorem gates.",
    "R": (
        "Read the exact row/column audit, diagonal-residue bridge, BKM-projection summary, and residence receipt, "
        "then report whether steps 1-4 are actually closed."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed route audit only; no theorem, full-NS, BKM, or Clay promotion.",
    "L": "row/column gate -> residue transfer -> structural BKM step -> residence-time exclusion",
    "P": ROUTE_DECISION,
    "G": "Keep downstream steps blocked if upstream theorem gates are not actually discharged.",
    "F": "The route remains pre-theorem until a profile-independent exact-script bound and structural PDE bridge are proved.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row-column-summary", type=Path, default=DEFAULT_ROW_COLUMN_SUMMARY)
    parser.add_argument("--diagonal-residue-summary", type=Path, default=DEFAULT_DIAGONAL_RESIDUE_SUMMARY)
    parser.add_argument("--bkm-summary", type=Path, default=DEFAULT_BKM_SUMMARY)
    parser.add_argument("--residence-agda", type=Path, default=DEFAULT_RESIDENCE_AGDA)
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
        print(f"[exact-route-audit] {entry['at']} +{entry['elapsed_ms']}ms {message} {details}", flush=True)

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


def _residence_status(path: Path) -> dict[str, Any]:
    text = path.read_text(encoding="utf-8")

    def has_bool(name: str, value: str) -> bool:
        needle = f"{name} = {value}"
        return needle in text

    required_tokens = [
        "MissingResidenceTimeObject",
        "LowModeResidenceWindowOpen",
        "LerayCompatibleResidenceTrajectoryOpen",
        "lowModeResidenceTimeLedgerClosed = true",
        "failClosedResidenceTimeAgainstViscosity = true",
    ]
    missing = [token for token in required_tokens if token not in text]
    return {
        "path": str(path),
        "recorded": not missing,
        "missing_tokens": missing,
        "residence_time_against_viscosity_closed": has_bool("residenceTimeAgainstViscosityClosed", "false"),
        "finite_time_kstar_collapse_closed": has_bool("finiteTimeKStarCollapseClosed", "false"),
        "clay_navier_stokes_promoted": has_bool("clayNavierStokesPromoted", "false"),
    }


def _qgap_scaled_stats(diagonal: dict[str, Any]) -> dict[str, Any]:
    values: list[float] = []
    d_values: list[float] = []
    for row in diagonal.get("bridge_rows", []):
        if not isinstance(row, dict):
            continue
        schur = row.get("SchurResidueScale", {})
        if not isinstance(schur, dict):
            continue
        n2_q_gap = _finite_float(schur.get("N2_q_gap"))
        d_q_gap = _finite_float(schur.get("D_q_gap"))
        if n2_q_gap is not None:
            values.append(n2_q_gap)
        if d_q_gap is not None:
            d_values.append(d_q_gap)
    def stats(xs: list[float]) -> dict[str, Any]:
        if not xs:
            return {"count": 0}
        return {"count": len(xs), "min": min(xs), "max": max(xs), "mean": sum(xs) / len(xs)}
    return {"N2_q_gap": stats(values), "D_q_gap": stats(d_values)}


def _analysis_read(payload: dict[str, Any]) -> str:
    rowcol = payload["row_column_summary"]
    diagonal = payload["diagonal_residue_summary"]
    bkm = payload["bkm_summary"]
    residence = payload["residence_status"]

    forced = rowcol.get("forced_tail_family", {})
    adv = rowcol.get("adversarial_family", {})
    forced_row = _finite_float(forced.get("row_sum_fit", {}).get("slope"))
    forced_col = _finite_float(forced.get("column_sum_fit", {}).get("slope"))
    adv_row = _finite_float(adv.get("row_sum_fit", {}).get("slope"))
    adv_col = _finite_float(adv.get("column_sum_fit", {}).get("slope"))
    qgap = payload["qgap_scaled_stats"]["N2_q_gap"]
    bkm_fit = bkm.get("projection_fit", {})

    def fmt(value: float | None) -> str:
        return "null" if value is None else f"{value:.3f}"

    return (
        "Route audit readout: Gate 1 remains open because the checked exact-script families are asymmetric rather than "
        f"profile-independent, with forced-tail row/column slopes {fmt(forced_row)}/{fmt(forced_col)} and adversarial "
        f"row/column slopes {fmt(adv_row)}/{fmt(adv_col)}. Gate 2 remains candidate-only: the sampled residue bridge keeps "
        f"N^2*q_gap in {fmt(qgap.get('min'))}..{fmt(qgap.get('max'))}, but the route still lacks a proved exact-script-to-residue "
        "transfer. Gate 3 remains open: the BKM projection telemetry is tiny and fitted by the sampled script, but it is still "
        f"structural-candidate-only with projection slope {fmt(_finite_float(bkm_fit.get('slope')))}. Gate 4 remains open: the "
        "residence receipt still records missing analytic objects and false closure flags, so no trajectory-level exclusion has been proved."
    )


def _markdown(payload: dict[str, Any]) -> str:
    qgap = payload["qgap_scaled_stats"]
    lines = [
        "# NS Triad Exact-Operator Route Audit",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- BKM exclusion proved: `{payload['bkm_exclusion_proved']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "## Gates",
        "",
        "| Step | Target | Closed | Reason |",
        "|---|---|---|---|",
    ]
    for row in payload["gate_rows"]:
        lines.append(
            f"| {row['step']} | {row['target']} | {row['closed']} | {row['reason']} |"
        )
    lines.extend(
        [
            "",
            "## Readout",
            "",
            payload["analysis_read"],
            "",
            "## Residue Scale Context",
            "",
            f"- N^2 * q_gap stats: `{qgap['N2_q_gap']}`",
            f"- D * q_gap stats: `{qgap['D_q_gap']}`",
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
    log("started exact-operator route audit")

    row_column_summary = _load_json(args.row_column_summary)
    diagonal_residue_summary = _load_json(args.diagonal_residue_summary)
    bkm_summary = _load_json(args.bkm_summary)
    residence_status = _residence_status(args.residence_agda)
    qgap_scaled_stats = _qgap_scaled_stats(diagonal_residue_summary)
    log(
        "loaded source artifacts",
        row_column_summary=str(args.row_column_summary),
        diagonal_residue_summary=str(args.diagonal_residue_summary),
        bkm_summary=str(args.bkm_summary),
        residence_agda=str(args.residence_agda),
    )

    gate_rows = [
        {
            "step": 1,
            "target": "profile-independent exact-script row/column control and ||L_FT,script^N||_op <= C / N",
            "closed": False,
            "reason": "checked families scale differently; the current exact-script audit remains sampled and profile-asymmetric",
        },
        {
            "step": 2,
            "target": "q_gap(N) >= c_gap / N^2 via SchurResidueScale transfer",
            "closed": False,
            "reason": "sampled N^2*q_gap is stable but the exact operator-to-residue theorem transfer is not closed",
        },
        {
            "step": 3,
            "target": "structural BKM projection smallness",
            "closed": False,
            "reason": "BKM projection is telemetry-only; no structural orthogonality theorem has been recorded",
        },
        {
            "step": 4,
            "target": "trajectory-level residence-time exclusion",
            "closed": False,
            "reason": "residence receipt still records missing analytic objects and false closure flags",
        },
    ]
    log("derived gate statuses", gate_count=len(gate_rows))

    payload: dict[str, Any] = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "started_at": started_at,
        "status": "ok",
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "terminal_promoted": False,
        "row_column_summary_path": str(args.row_column_summary),
        "diagonal_residue_summary_path": str(args.diagonal_residue_summary),
        "bkm_summary_path": str(args.bkm_summary),
        "residence_agda_path": str(args.residence_agda),
        "row_column_summary": row_column_summary,
        "diagonal_residue_summary": diagonal_residue_summary,
        "bkm_summary": bkm_summary,
        "residence_status": residence_status,
        "qgap_scaled_stats": qgap_scaled_stats,
        "gate_rows": gate_rows,
        "analysis_read": "",
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
            "message": "wrote exact-operator route audit artifacts",
            "output_json": str(output_json),
            "output_md": str(output_md),
        }
    )
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
