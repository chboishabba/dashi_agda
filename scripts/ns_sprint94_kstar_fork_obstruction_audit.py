#!/usr/bin/env python3
"""Sprint 94 NS K-star fork obstruction audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint94_kstar_fork_obstruction_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint94_kstar_fork_obstruction_audit")
SUMMARY_NAME = "ns_sprint94_kstar_fork_obstruction_audit_summary.json"
ROWS_NAME = "ns_sprint94_kstar_fork_obstruction_audit_rows.json"
GATE_CSV_NAME = "ns_sprint94_kstar_fork_obstruction_gate_table.csv"
SOURCE_CSV_NAME = "ns_sprint94_kstar_fork_obstruction_source_table.csv"
REPORT_NAME = "ns_sprint94_kstar_fork_obstruction_audit.md"
AGDA_PATH = Path(
    "DASHI/Physics/Closure/"
    "NSSprint94KStarForkObstructionAndConditionalRegularity.agda"
)

REQUIRED_ANCHORS = [
    "canonicalNSSprint94KStarForkObstructionAndConditionalRegularity",
    "KStarLowerBoundHypothesis",
    "GlobalRegularityUnderKStarLowerBound",
    "GeneralDataKStarLowerBoundObstruction",
    "OptionABlockedGeneralDataRegularity",
    "OptionBOpenBlowupConstruction",
    "OptionCConditionalRegularity",
    "kStarForkObstructionClosed",
    "globalRegularityUnderKStarLowerBoundClosed",
    "optionCConditionalCriterionClosed",
    "generalDataKStarLowerBoundClosed",
    "generalDataClayRegularityClosed",
    "blowupConstructionClosed",
    "clayNavierStokesPromoted",
]

EXPECTED_BOOLEANS = {
    "kStarForkObstructionClosed": True,
    "globalRegularityUnderKStarLowerBoundClosed": True,
    "optionCConditionalCriterionClosed": True,
    "generalDataKStarLowerBoundClosed": False,
    "generalDataClayRegularityClosed": False,
    "blowupConstructionClosed": False,
    "clayNavierStokesPromoted": False,
}

FORBIDDEN_PATTERNS = {
    "postulate": re.compile(r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])"),
    "todo": re.compile(r"(?<![A-Za-z0-9_])TODO(?![A-Za-z0-9_])"),
    "stub": re.compile(r"(?<![A-Za-z0-9_])stub(?![A-Za-z0-9_])", re.I),
    "placeholder": re.compile(r"(?<![A-Za-z0-9_])placeholders?(?![A-Za-z0-9_])", re.I),
    "agda_hole_start": re.compile(r"\{!"),
    "agda_hole_end": re.compile(r"!\}"),
}

@dataclass(frozen=True)
class GateRow:
    gate_id: str
    gate_name: str
    expected: str
    actual: str
    passed: bool
    status: str


@dataclass(frozen=True)
class SourceRow:
    source_id: str
    surface_name: str
    present_in_repo: bool
    required_anchors: str
    missing_anchors: str
    status: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def bool_assignment(text: str, name: str, expected: bool) -> bool:
    value = "true" if expected else "false"
    pattern = re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(name)
        + r"(?![A-Za-z0-9_])"
        + r"(?:\s*:\s*[^\n=]+)?\s*=\s*"
        + value
        + r"(?![A-Za-z0-9_])",
        re.MULTILINE,
    )
    return bool(pattern.search(text))


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def audit(repo_root: Path) -> dict[str, Any]:
    agda_abs = repo_root / AGDA_PATH
    text = agda_abs.read_text(encoding="utf-8")
    missing_anchors = [anchor for anchor in REQUIRED_ANCHORS if anchor not in text]
    bool_checks = {
        name: {
            "expected": expected,
            "passed": bool_assignment(text, name, expected),
        }
        for name, expected in EXPECTED_BOOLEANS.items()
    }
    forbidden_hits = [
        {
            "label": label,
            "line": line_for_offset(text, match.start()),
            "match": match.group(0),
        }
        for label, pattern in FORBIDDEN_PATTERNS.items()
        for match in pattern.finditer(text)
    ]
    clay_true_detected = bool_assignment(text, "clayNavierStokesPromoted", True)
    all_bool_checks_pass = all(item["passed"] for item in bool_checks.values())
    passed = (
        not missing_anchors
        and not forbidden_hits
        and not clay_true_detected
        and all_bool_checks_pass
    )
    gate_rows = [
        GateRow(
            "G1",
            "KStarForkObstruction",
            "true",
            str(bool_checks["kStarForkObstructionClosed"]["passed"]).lower(),
            bool_checks["kStarForkObstructionClosed"]["passed"],
            "PASS",
        ),
        GateRow(
            "G2",
            "ConditionalCriterionClosed",
            "true",
            str(bool_checks["globalRegularityUnderKStarLowerBoundClosed"]["passed"]).lower(),
            bool_checks["globalRegularityUnderKStarLowerBoundClosed"]["passed"],
            "PASS",
        ),
        GateRow(
            "G3",
            "GeneralDataGateClosed",
            "false",
            "false" if bool_checks["generalDataClayRegularityClosed"]["passed"] else "missing",
            bool_checks["generalDataClayRegularityClosed"]["passed"],
            "FALSE_RECORDED",
        ),
        GateRow(
            "G4",
            "BlowupConstructionClosed",
            "false",
            "false" if bool_checks["blowupConstructionClosed"]["passed"] else "missing",
            bool_checks["blowupConstructionClosed"]["passed"],
            "FALSE_RECORDED",
        ),
        GateRow(
            "G5",
            "ClayNavierStokesPromoted",
            "false",
            "false" if bool_checks["clayNavierStokesPromoted"]["passed"] else "missing",
            bool_checks["clayNavierStokesPromoted"]["passed"],
            "FALSE_RECORDED",
        ),
    ]
    source_rows = [
        SourceRow(
            "S1",
            "NSSprint94 KStar fork obstruction receipt",
            agda_abs.exists(),
            "; ".join(REQUIRED_ANCHORS),
            "none" if not missing_anchors else "; ".join(missing_anchors),
            "PASS" if not missing_anchors else "FAIL",
        )
    ]
    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "complete": False,
        "fail_closed": passed,
        "route_decision": "FAIL_CLOSED",
        "final_decision": "FAIL_CLOSED",
        "promotion_decision": "hold",
        "kstar_fork_obstruction_closed": bool_checks["kStarForkObstructionClosed"]["passed"],
        "obstruction_closed_true": bool_checks["kStarForkObstructionClosed"]["passed"],
        "conditional_criterion_closed": bool_checks[
            "globalRegularityUnderKStarLowerBoundClosed"
        ]["passed"],
        "option_c_conditional_criterion_closed": bool_checks[
            "optionCConditionalCriterionClosed"
        ]["passed"],
        "general_data_gate_closed": False
        if bool_checks["generalDataClayRegularityClosed"]["passed"]
        else None,
        "general_data_kstar_lower_bound_closed": False
        if bool_checks["generalDataKStarLowerBoundClosed"]["passed"]
        else None,
        "general_data_clay_regularity_closed": False
        if bool_checks["generalDataClayRegularityClosed"]["passed"]
        else None,
        "blowup_construction_closed": False
        if bool_checks["blowupConstructionClosed"]["passed"]
        else None,
        "clay_navier_stokes_promoted": False
        if bool_checks["clayNavierStokesPromoted"]["passed"]
        else None,
        "required_residual_gate": "general-data K*(t) lower bound or blowup construction",
        "missing_anchors": missing_anchors,
        "bool_checks": bool_checks,
        "forbidden_hits": forbidden_hits,
        "forbidden_term_count": len(forbidden_hits),
        "clay_true_detected": clay_true_detected,
        "gate_results": [asdict(row) for row in gate_rows],
        "source_results": [asdict(row) for row in source_rows],
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    rows = {
        "gates": summary["gate_results"],
        "sources": summary["source_results"],
    }
    (out_dir / ROWS_NAME).write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_csv(out_dir / GATE_CSV_NAME, rows["gates"])
    write_csv(out_dir / SOURCE_CSV_NAME, rows["sources"])
    lines = [
        "# NS Sprint 94 K-star Fork Obstruction Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Complete: `{summary['complete']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Final decision: `{summary['final_decision']}`",
        f"- NSSprint94: `{summary['agda_path']}`",
        f"- K-star obstruction closed: `{summary['kstar_fork_obstruction_closed']}`",
        f"- Conditional criterion closed: `{summary['conditional_criterion_closed']}`",
        f"- General-data gate closed: `{summary['general_data_gate_closed']}`",
        f"- Blowup construction closed: `{summary['blowup_construction_closed']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Required residual gate: `{summary['required_residual_gate']}`",
    ]
    (out_dir / REPORT_NAME).write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = audit(args.repo_root)
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["fail_closed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
