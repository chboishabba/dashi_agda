#!/usr/bin/env python3
"""Sprint 90 NS local enstrophy budget audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint90_local_enstrophy_budget_audit"
ROUTE_OPEN = "NS_SPRINT90_LOCAL_ENSTROPHY_BUDGET_ROUTE_OPEN"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint90_local_enstrophy_budget_audit")
SUMMARY_NAME = "ns_sprint90_local_enstrophy_budget_audit_summary.json"
ROWS_JSON_NAME = "ns_sprint90_local_enstrophy_budget_audit_rows.json"
GATE_TABLE = "ns_sprint90_local_enstrophy_budget_gate_table.csv"
SOURCE_TABLE = "ns_sprint90_local_enstrophy_budget_source_table.csv"
REPORT_NAME = "ns_sprint90_local_enstrophy_budget_audit.md"

RECEIPT_REL = Path(
    "DASHI/Physics/Closure/NSSprint90LocalEnstrophyDangerShellReductionReceipt.agda"
)

RECEIPT_ANCHORS = [
    "canonicalNSSprint90LocalEnstrophyDangerShellReductionReceipt",
    "NSSprint90LocalEnstrophyDangerShellReductionReceipt",
    "sprint89PointwiseH1TailGateStillOpen",
    "sprint89LocalEnstrophyMechanismStillOpen",
    "sprint89IndependentCoefficientStillOpen",
    "localEnstrophyDangerShellReductionRecorded",
    "localEnstrophyDangerShellReductionBookkeepingClosed",
    "localizedEnstrophyFluxIdentityClosed",
    "dangerShellDissipationDominatesInfluxClosed",
    "pointwiseTailFromLocalDissipationClosed",
    "actualPointwiseH1TailClosureClosed",
    "independentCoefficientBudgetClosed",
    "independentEpsilonCoefficientClosed",
    "pointwiseH1TailWithIndependentEpsilonCoefficientClosed",
    "clayNavierStokesPromoted",
    "canonicalSprint90Flags",
]

SUPPORT_SURFACES = [
    (
        "Sprint89PointwiseH1TailCandidateMechanismReceipt",
        "DASHI/Physics/Closure/NSSprint89PointwiseH1TailCandidateMechanismReceipt.agda",
        ["canonicalNSSprint89PointwiseH1TailCandidateMechanismReceipt"],
    ),
    (
        "Sprint89CircularityMatrixAudit",
        "scripts/ns_sprint89_circularity_matrix_audit.py",
        ["FORBIDDEN_DEPENDENCIES", "requires_independent_epsilon_coefficient"],
    ),
]

GATE_SPECS = [
    (
        "G1",
        "LocalEnstrophyDangerShellReductionRecorded",
        "localEnstrophyDangerShellReductionRecorded",
        True,
        "record local enstrophy danger-shell reduction as the selected route",
    ),
    (
        "G2",
        "LocalEnstrophyDangerShellReductionBookkeepingClosed",
        "localEnstrophyDangerShellReductionBookkeepingClosed",
        True,
        "close only reduction bookkeeping",
    ),
    (
        "G3",
        "LocalizedEnstrophyFluxIdentityClosed",
        "localizedEnstrophyFluxIdentityClosed",
        False,
        "keep localized enstrophy flux identity analytic gate false",
    ),
    (
        "G4",
        "DangerShellDissipationDominatesInfluxClosed",
        "dangerShellDissipationDominatesInfluxClosed",
        False,
        "keep danger-shell dissipation domination analytic gate false",
    ),
    (
        "G5",
        "PointwiseTailFromLocalDissipationClosed",
        "pointwiseTailFromLocalDissipationClosed",
        False,
        "keep pointwise extraction from local dissipation false",
    ),
    (
        "G6",
        "IndependentCoefficientBudgetClosed",
        "independentCoefficientBudgetClosed",
        False,
        "keep independent coefficient budget analytic gate false",
    ),
    (
        "G7",
        "ActualPointwiseH1TailClosureClosed",
        "actualPointwiseH1TailClosureClosed",
        False,
        "keep actual pointwise H1-tail analytic closure false",
    ),
    (
        "G8",
        "IndependentEpsilonCoefficientClosed",
        "independentEpsilonCoefficientClosed",
        False,
        "keep epsilon coefficient analytic closure false",
    ),
    (
        "G9",
        "PointwiseH1TailWithIndependentEpsilonCoefficientClosed",
        "pointwiseH1TailWithIndependentEpsilonCoefficientClosed",
        False,
        "keep Sprint 89 pointwise/epsilon combined analytic closure false",
    ),
    (
        "G10",
        "NoForbiddenDependencyReuseClosed",
        "noForbiddenDependencyReuseClosed",
        True,
        "close only the dependency-reuse governance gate",
    ),
    (
        "G11",
        "ClayNavierStokesPromoted",
        "clayNavierStokesPromoted",
        False,
        "keep Clay Navier-Stokes promotion false",
    ),
]

BOOL_DECL = re.compile(
    r"(?m)^\s*([A-Za-z][A-Za-z0-9']*)\s*:\s*Bool\s*\n"
    r"\s*\1\s*=\s*(true|false)\s*$"
)
FIELD_ASSIGN = re.compile(r"(?m)^\s*;\s*([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$")
FORBIDDEN_WORDS = re.compile(
    r"(?im)\b(postulate|todo|stub|placeholder|future\s+proof|future-proof|futureproof|hole)\b"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def bools(text: str) -> dict[str, bool]:
    values = {name: raw == "true" for name, raw in BOOL_DECL.findall(text)}
    values.update({name: raw == "true" for name, raw in FIELD_ASSIGN.findall(text)})
    return values


def forbidden_hits(text: str) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for match in FORBIDDEN_WORDS.finditer(text):
        hits.append(
            {
                "line": text.count("\n", 0, match.start()) + 1,
                "term": match.group(0),
            }
        )
    return hits


def true_assignment_detected(text: str, field: str, values: dict[str, bool]) -> bool:
    pattern = re.compile(rf"(?m)\b{re.escape(field)}\b\s*(?:=|:=[^\n]*=)\s*true\b")
    return bool(pattern.search(text)) or values.get(field) is True


def source_rows(repo_root: Path, receipt_text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    receipt_exists = (repo_root / RECEIPT_REL).exists()
    missing = [anchor for anchor in RECEIPT_ANCHORS if anchor not in receipt_text]
    rows.append(
        {
            "source_id": "S1",
            "surface_name": "Sprint90LocalEnstrophyDangerShellReductionReceipt",
            "path": RECEIPT_REL.as_posix(),
            "present_in_repo": receipt_exists,
            "required_anchors": "; ".join(RECEIPT_ANCHORS),
            "missing_anchors": "; ".join(missing) if missing else "none",
            "status": "PASS" if receipt_exists and not missing else "FAIL",
        }
    )
    for index, (name, rel, anchors) in enumerate(SUPPORT_SURFACES, start=2):
        text = read_text(repo_root / rel)
        missing_support = [anchor for anchor in anchors if anchor not in text]
        rows.append(
            {
                "source_id": f"S{index}",
                "surface_name": name,
                "path": rel,
                "present_in_repo": (repo_root / rel).exists(),
                "required_anchors": "; ".join(anchors),
                "missing_anchors": "; ".join(missing_support) if missing_support else "none",
                "status": "PASS" if (repo_root / rel).exists() and not missing_support else "FAIL",
            }
        )
    return rows


def gate_rows(
    values: dict[str, bool],
    anchors_ok: bool,
    forbidden: list[dict[str, Any]],
    true_violations: dict[str, bool],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for gate_id, gate_name, field, expected, next_input in GATE_SPECS:
        actual = values.get(field)
        passed = anchors_ok and not forbidden and actual is expected
        if true_violations.get(field):
            status = "TRUE_CLOSURE_OR_PROMOTION_VIOLATION_FAIL_CLOSED"
            passed = False
        elif not anchors_ok:
            status = "FAIL_CLOSED_MISSING_ANCHOR"
        elif forbidden:
            status = "FAIL_CLOSED_FORBIDDEN_LANGUAGE"
        elif passed and expected is True:
            status = "RECORDED"
        elif passed and expected is False and field == "clayNavierStokesPromoted":
            status = "FALSE_NO_PROMOTION"
        elif passed and expected is False:
            status = "FALSE_ANALYTIC_CLOSURE_OPEN"
        else:
            status = "VALUE_MISMATCH_FAIL_CLOSED"
        rows.append(
            {
                "gate_id": gate_id,
                "gate_name": gate_name,
                "field_name": field,
                "actual_value": actual,
                "expected_value": expected,
                "passed": passed,
                "status": status,
                "next_required_input": next_input,
            }
        )
    rows.append(
        {
            "gate_id": "G12",
            "gate_name": "NoForbiddenStubOrHoleLanguage",
            "field_name": "forbidden_terms",
            "actual_value": len(forbidden),
            "expected_value": 0,
            "passed": anchors_ok and not forbidden,
            "status": "PASS" if anchors_ok and not forbidden else "FAIL_CLOSED_FORBIDDEN_OR_MISSING",
            "next_required_input": "remove postulate/TODO/stub/placeholder/future proof/hole wording",
        }
    )
    return rows


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def build(repo_root: Path) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    text = read_text(repo_root / RECEIPT_REL)
    values = bools(text)
    sources = source_rows(repo_root, text)
    anchors_ok = sources[0]["status"] == "PASS"
    forbidden = forbidden_hits(text)
    guarded_false_fields = [
        "clayNavierStokesPromoted",
        "localizedEnstrophyFluxIdentityClosed",
        "dangerShellDissipationDominatesInfluxClosed",
        "pointwiseTailFromLocalDissipationClosed",
        "independentCoefficientBudgetClosed",
        "actualPointwiseH1TailClosureClosed",
        "independentEpsilonCoefficientClosed",
        "pointwiseH1TailWithIndependentEpsilonCoefficientClosed",
    ]
    true_violations = {
        field: true_assignment_detected(text, field, values) for field in guarded_false_fields
    }
    gates = gate_rows(values, anchors_ok, forbidden, true_violations)
    fail_closed = (
        not anchors_ok
        or bool(forbidden)
        or any(true_violations.values())
        or any(not row["passed"] for row in gates)
    )
    summary = {
        "contract": CONTRACT,
        "complete": False,
        "route_decision": "fail_closed" if fail_closed else ROUTE_OPEN,
        "receipt_path": RECEIPT_REL.as_posix(),
        "source_table": SOURCE_TABLE,
        "gate_table": GATE_TABLE,
        "rows_json": ROWS_JSON_NAME,
        "report": REPORT_NAME,
        "all_required_receipt_anchors_present": anchors_ok,
        "forbidden_terms_detected": forbidden,
        "forbidden_term_count": len(forbidden),
        "fail_closed": fail_closed,
        "true_violations": true_violations,
        "clay_navier_stokes_promoted": values.get("clayNavierStokesPromoted"),
        "actual_pointwise_h1_tail_closure_closed": values.get(
            "actualPointwiseH1TailClosureClosed"
        ),
        "independent_epsilon_coefficient_closed": values.get("independentEpsilonCoefficientClosed"),
        "pointwise_h1_tail_with_independent_epsilon_coefficient_closed": values.get(
            "pointwiseH1TailWithIndependentEpsilonCoefficientClosed"
        ),
        "analytic_closure_flags": {
            "localized_enstrophy_flux_identity_closed": values.get(
                "localizedEnstrophyFluxIdentityClosed"
            ),
            "danger_shell_dissipation_dominates_influx_closed": values.get(
                "dangerShellDissipationDominatesInfluxClosed"
            ),
            "pointwise_tail_from_local_dissipation_closed": values.get(
                "pointwiseTailFromLocalDissipationClosed"
            ),
            "independent_coefficient_budget_closed": values.get(
                "independentCoefficientBudgetClosed"
            ),
            "actual_pointwise_h1_tail_closure_closed": values.get(
                "actualPointwiseH1TailClosureClosed"
            ),
            "independent_epsilon_coefficient_closed": values.get(
                "independentEpsilonCoefficientClosed"
            ),
            "pointwise_h1_tail_with_independent_epsilon_coefficient_closed": values.get(
                "pointwiseH1TailWithIndependentEpsilonCoefficientClosed"
            ),
        },
        "local_enstrophy_danger_shell_reduction_recorded": values.get(
            "localEnstrophyDangerShellReductionRecorded"
        ),
        "local_enstrophy_danger_shell_reduction_bookkeeping_closed": values.get(
            "localEnstrophyDangerShellReductionBookkeepingClosed"
        ),
        "expected_gates": {gate_name: expected for _, gate_name, _, expected, _ in GATE_SPECS},
        "gate_results": gates,
        "source_results": sources,
        "open_obligations": [
            "materialize the Sprint 90 local enstrophy danger-shell reduction receipt if missing",
            "keep pointwise analytic closure false until a non-circular theorem exists",
            "keep epsilon analytic closure false until an independent coefficient proof exists",
            "keep Clay Navier-Stokes promotion false",
        ],
    }
    return summary, sources, gates


def markdown(summary: dict[str, Any], sources: list[dict[str, Any]], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 90 Local Enstrophy Budget Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Receipt: `{summary['receipt_path']}`",
        f"- Anchors present: `{summary['all_required_receipt_anchors_present']}`",
        f"- Forbidden term count: `{summary['forbidden_term_count']}`",
        f"- Local enstrophy reduction recorded: "
        f"`{summary['local_enstrophy_danger_shell_reduction_recorded']}`",
        f"- Local enstrophy bookkeeping closed: "
        f"`{summary['local_enstrophy_danger_shell_reduction_bookkeeping_closed']}`",
        f"- Actual pointwise H1-tail closure closed: "
        f"`{summary['actual_pointwise_h1_tail_closure_closed']}`",
        f"- Independent epsilon coefficient closed: "
        f"`{summary['independent_epsilon_coefficient_closed']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        "",
        "## Gates",
        "",
        "| Gate | Expected | Actual | Status |",
        "| --- | --- | --- | --- |",
    ]
    for row in gates:
        lines.append(
            f"| `{row['gate_name']}` | `{row['expected_value']}` | "
            f"`{row['actual_value']}` | `{row['status']}` |"
        )
    lines.extend(["", "## Source Surfaces", ""])
    for row in sources:
        lines.append(
            f"- `{row['source_id']}` `{row['path']}`: `{row['status']}`, "
            f"missing anchors `{row['missing_anchors']}`."
        )
    lines.extend(["", "## Forbidden Terms", ""])
    if summary["forbidden_terms_detected"]:
        for hit in summary["forbidden_terms_detected"]:
            lines.append(f"- line `{hit['line']}` term `{hit['term']}`")
    else:
        lines.append("- none")
    lines.extend(["", "## Open Obligations", ""])
    lines.extend(f"- {item}" for item in summary["open_obligations"])
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary, sources, gates = build(args.repo_root)
    rows_payload = {"sources": sources, "gates": gates}
    write_csv(args.out_dir / SOURCE_TABLE, sources)
    write_csv(args.out_dir / GATE_TABLE, gates)
    (args.out_dir / ROWS_JSON_NAME).write_text(
        json.dumps(rows_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / REPORT_NAME).write_text(markdown(summary, sources, gates), encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
