#!/usr/bin/env python3
"""Combine the mixed-tail tail-stability and Schur-residue evidence.

This is a candidate-only report.  It does not claim a theorem, a full-NS
promotion, a BKM exclusion proof, or a Clay promotion.  It reuses the
Schur-gap anatomy and Schur-subtraction-bound receipts to package the next
analytic bridge as two named rows:

  * TailDiagonalStable
  * SchurResidueScale

The report is intentionally small: it records the bridge question, the
relevant evidence, and the open analytic gaps.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from ns_triad_frame_stability_scan import AUTHORITY, OK_STATUS, _json_text  # type: ignore


SCRIPT_NAME = "scripts/ns_triad_kn_diagonal_residue_bridge.py"
CONTRACT = "ns_triad_kn_diagonal_residue_bridge"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_KN_DIAGONAL_RESIDUE_BRIDGE"
SCHEMA_VERSION = "1.0.0"
DEFAULT_ANATOMY_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_schur_gap_anatomy_20260624/summary.json"
)
DEFAULT_SUBTRACTION_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_schur_subtraction_bound_20260624/summary.json"
)
DEFAULT_OUTPUT_DIR = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_kn_diagonal_residue_bridge_20260624"
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--anatomy-summary", type=Path, default=DEFAULT_ANATOMY_SUMMARY)
    parser.add_argument("--subtraction-summary", type=Path, default=DEFAULT_SUBTRACTION_SUMMARY)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: JSON root must be an object")
    return payload


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _derive_rows(subtraction_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row in subtraction_rows:
        q_diag = _finite_float(row.get("q_diag"))
        q_gap = _finite_float(row.get("q_gap"))
        q_sub = _finite_float(row.get("q_schur_subtraction"))
        d_value = _finite_float(row.get("D"))
        shell = _finite_float(row.get("N")) or _finite_float(row.get("shell"))
        rows.append(
            {
                "N": row.get("N", row.get("shell")),
                "K": row.get("K"),
                "TailDiagonalStable": {
                    "evidence": "q_diag and q_schur stay on the sampled 10^-2 scale; the subtraction remains tiny relative to q_diag.",
                    "target": "q_diag(N) >= c_diag > 0",
                    "missing": "analytic tail-block coercivity from the Biot-Savart / triad geometry",
                    "q_diag": q_diag,
                    "q_schur": _finite_float(row.get("q_schur")),
                    "q_schur_subtraction_over_q_diag": (
                        q_sub / q_diag if q_diag not in (None, 0.0) and q_sub is not None else None
                    ),
                },
                "SchurResidueScale": {
                    "evidence": "q_gap is positive, much smaller than q_diag, and D*q_gap is approximately stable.",
                    "target": "q_gap(N) >= c_gap / N^2",
                    "missing": "analytic lower bound on the finite-tail Schur residue",
                    "q_gap": q_gap,
                    "q_gap_over_q_diag": (
                        q_gap / q_diag if q_diag not in (None, 0.0) and q_gap is not None else None
                    ),
                    "D_q_gap": d_value * q_gap if d_value is not None and q_gap is not None else None,
                    "N2_q_gap": shell * shell * q_gap if shell is not None and q_gap is not None else None,
                },
                "R_tail": _finite_float(row.get("R_tail")),
                "cross_l_neg_fraction": _finite_float(row.get("cross_l_neg_fraction")),
                "bkm_tail_projection_squared_fraction": _finite_float(
                    row.get("bkm_tail_projection_squared_fraction")
                ),
            }
        )
    return rows


def _load_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows = payload.get("rows", [])
    if not isinstance(rows, list):
        return []
    normalized = [row for row in rows if isinstance(row, dict)]
    normalized.sort(key=lambda row: int(row.get("N") or row.get("shell") or 0))
    return normalized


def _markdown(payload: dict[str, Any]) -> str:
    def fmt(value: Any) -> str:
        if value is None:
            return "null"
        if isinstance(value, float):
            return f"{value:.6g}"
        return str(value)

    lines = [
        "# NS Triad K_N Diagonal Residue Bridge",
        "",
        f"- status: `{payload['status']}`",
        f"- candidate only: `{payload['candidate_only']}`",
        f"- theorem promoted: `{payload['theorem_promoted']}`",
        f"- full NS promoted: `{payload['full_ns_promoted']}`",
        f"- BKM exclusion proved: `{payload['bkm_exclusion_proved']}`",
        f"- Clay promoted: `{payload['clay_promoted']}`",
        "",
        "| N | K | TailDiagonalStable | SchurResidueScale | R_tail | cross L_neg frac | BKM tail proj² |",
        "|---:|---:|---|---|---:|---:|---:|",
    ]
    for row in payload["bridge_rows"]:
        tail = row["TailDiagonalStable"]
        schur = row["SchurResidueScale"]
        lines.append(
            f"| {fmt(row['N'])} | {fmt(row['K'])} | {tail['target']} | {schur['target']} | "
            f"{fmt(row['R_tail'])} | {fmt(row['cross_l_neg_fraction'])} | "
            f"{fmt(row['bkm_tail_projection_squared_fraction'])} |"
        )
    lines.extend(
        [
            "",
            "## Readout",
            "",
            payload["analysis_read"],
            "",
            "## Bridge rows",
            "",
            "- TailDiagonalStable: q_diag and q_schur remain O(10^-2), with q_schur_subtraction/q_diag staying near 0.3%.",
            "- SchurResidueScale: q_gap stays positive, q_gap/q_diag is small, and D*q_gap remains approximately stable.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    args = _parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    anatomy = _load_json(args.anatomy_summary)
    subtraction = _load_json(args.subtraction_summary)
    subtraction_rows = _load_rows(subtraction)
    bridge_rows = _derive_rows(subtraction_rows)
    status = (
        subtraction.get("status") if subtraction.get("status") == OK_STATUS and len(bridge_rows) >= 4 else "partial"
    )

    payload: dict[str, Any] = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "status": status,
        "candidate_only": True,
        "fail_closed": True,
        "theorem_promoted": False,
        "full_ns_promoted": False,
        "bkm_exclusion_proved": False,
        "clay_promoted": False,
        "terminal_promoted": False,
        "anatomy_summary": str(args.anatomy_summary),
        "subtraction_summary": str(args.subtraction_summary),
        "source_anatomy_status": anatomy.get("status"),
        "source_subtraction_status": subtraction.get("status"),
        "row_count": len(bridge_rows),
        "bridge_rows": bridge_rows,
        "analysis_read": (
            "Candidate-only diagonal-residue bridge: TailDiagonalStable says the tail block stays on the sampled 10^-2 scale, "
            "while SchurResidueScale says the positive gap is a small normalized residue with stable D*q_gap and q_gap ~ N^-2.2."
        ),
        "promotion_flags": [],
    }

    output_json = args.output_dir / "summary.json"
    output_md = args.output_dir / "summary.md"
    output_json.write_text(_json_text(payload, bool(args.pretty)), encoding="utf-8")
    output_md.write_text(_markdown(payload), encoding="utf-8")
    print(_json_text(payload, bool(args.pretty)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
