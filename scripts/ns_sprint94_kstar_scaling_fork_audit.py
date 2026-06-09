#!/usr/bin/env python3
"""Sprint 94 NS K-star scaling fork audit."""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint94_kstar_scaling_fork_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint94_kstar_scaling_fork_audit")
SUMMARY_NAME = "ns_sprint94_kstar_scaling_fork_audit_summary.json"
ROWS_NAME = "ns_sprint94_kstar_scaling_fork_audit_rows.json"
GATE_CSV_NAME = "ns_sprint94_kstar_scaling_fork_gate_table.csv"
SOURCE_CSV_NAME = "ns_sprint94_kstar_scaling_fork_source_table.csv"
REPORT_NAME = "ns_sprint94_kstar_scaling_fork_audit.md"


@dataclass(frozen=True)
class GateRow:
    gate: str
    formula: str
    status: str
    clay_general_data_effect: str


@dataclass(frozen=True)
class SourceRow:
    source: str
    supplies_kstar_lower_bound: bool
    supplies_general_data_route: bool
    supplies_conditional_route: bool
    note: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def gate_rows() -> list[GateRow]:
    return [
        GateRow(
            "high-high absorption",
            "K*(t) >= C/(epsilon*nu)",
            "calculated",
            "requires lower bound not supplied by Leray class",
        ),
        GateRow(
            "Leray-only control",
            "upper control only",
            "insufficient",
            "cannot prove the required lower bound for all data",
        ),
        GateRow(
            "combined inequalities",
            "||u0||_L2^2 <= C^3*nu^4/epsilon",
            "small-data reduction",
            "recovers known small-data regime rather than Clay all-data closure",
        ),
        GateRow(
            "conditional criterion",
            "assume K*(t) >= C/(epsilon*nu)",
            "ready",
            "conditional regularity only",
        ),
    ]


def source_rows() -> list[SourceRow]:
    return [
        SourceRow(
            "Sprint87 high-high factorization",
            False,
            False,
            True,
            "supplies the high-high estimate but leaves absorption conditional",
        ),
        SourceRow(
            "Sprint88-93 same-source search",
            False,
            False,
            False,
            "records zero accepted sources for general-data dominance plus pointwise tail plus coefficient",
        ),
        SourceRow(
            "KStarLowerBoundHypothesis",
            True,
            False,
            True,
            "sufficient as an explicit conditional assumption",
        ),
    ]


def build_summary() -> dict[str, Any]:
    gates = gate_rows()
    sources = source_rows()
    return {
        "contract": CONTRACT,
        "complete": True,
        "route_decision": "fail_closed",
        "final_decision": "FAIL_CLOSED_FOR_CLAY_GENERAL_DATA",
        "promotion_decision": "hold",
        "absorption_required_lower_bound": "K*(t) >= C/(epsilon*nu)",
        "small_data_restriction": "||u0||_L2^2 <= C^3*nu^4/epsilon",
        "general_data_route": "obstructed",
        "conditional_route": "conditional_criterion_ready",
        "conditional_criterion_ready": True,
        "conditional_criterion": "K* >= C/(epsilon nu)",
        "clay_navier_stokes_promoted": False,
        "gate_count": len(gates),
        "source_count": len(sources),
        "accepted_general_data_source_count": sum(
            1 for row in sources if row.supplies_general_data_route
        ),
        "conditional_source_count": sum(1 for row in sources if row.supplies_conditional_route),
        "rows": {
            "gates": [asdict(row) for row in gates],
            "sources": [asdict(row) for row in sources],
        },
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = summary["rows"]
    (out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / ROWS_NAME).write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_csv(out_dir / GATE_CSV_NAME, rows["gates"])
    write_csv(out_dir / SOURCE_CSV_NAME, rows["sources"])
    lines = [
        "# NS Sprint 94 K-star Scaling Fork Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Final decision: `{summary['final_decision']}`",
        f"- Absorption required lower bound: `{summary['absorption_required_lower_bound']}`",
        f"- Small-data restriction: `{summary['small_data_restriction']}`",
        f"- General-data route: `{summary['general_data_route']}`",
        f"- Conditional route: `{summary['conditional_route']}`",
        f"- Conditional criterion: `{summary['conditional_criterion']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
    ]
    (out_dir / REPORT_NAME).write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = build_summary()
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
