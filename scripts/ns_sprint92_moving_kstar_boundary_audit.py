#!/usr/bin/env python3
"""Sprint 92 NS moving K-star boundary audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint92_moving_kstar_boundary_audit"
ROUTE_OPEN = "open"
FAIL_CLOSED = "fail_closed"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint92_moving_kstar_boundary_audit")
SUMMARY_NAME = "ns_sprint92_moving_kstar_boundary_audit_summary.json"
ROWS_JSON_NAME = "ns_sprint92_moving_kstar_boundary_audit_rows.json"
SOURCE_TABLE = "ns_sprint92_moving_kstar_boundary_source_table.csv"
GATE_TABLE = "ns_sprint92_moving_kstar_boundary_gate_table.csv"
REPORT_NAME = "ns_sprint92_moving_kstar_boundary_audit.md"

RECEIPT_REL = Path(
    "DASHI/Physics/Closure/NSSprint92MovingKStarLocalizationBoundary.agda"
)

REQUIRED_ANCHORS = [
    "NSSprint92MovingKStarLocalizationBoundary",
    "canonicalNSSprint92MovingKStarLocalizationBoundary",
    "fixedDangerTimeFrozenKBookkeepingClosed",
    "fixedDangerTimeFrozenKBookkeepingClosedIsTrue",
    "movingInTimeKStarLocalizationBoundaryClosed",
    "movingInTimeKStarLocalizationBoundaryClosedIsFalse",
    "dangerShellDissipationDominatesInfluxClosed",
    "dangerShellDissipationDominatesInfluxClosedIsFalse",
    "pointwiseTailFromLocalDissipationClosed",
    "pointwiseTailFromLocalDissipationClosedIsFalse",
    "highHighDominanceClosed",
    "highHighDominanceClosedIsFalse",
    "independentCoefficientBudgetClosed",
    "independentCoefficientBudgetClosedIsFalse",
    "Sprint92FrozenKJustification",
    "Sprint92MovingBoundary",
    "canonicalSprint92OpenGates",
    "canonicalSprint92Flags",
    "clayNavierStokesPromoted",
    "clayNavierStokesPromotedIsFalse",
]

TRUE_GATES = [
    (
        "FixedDangerTimeFrozenKBookkeepingClosed",
        "fixedDangerTimeFrozenKBookkeepingClosed",
        "fixed danger-time frozen-K bookkeeping is recorded as true",
    ),
]

FALSE_GATES = [
    ("MovingKStarBoundaryTheoremClosed", "movingInTimeKStarLocalizationBoundaryClosed", "prove K*(t) moving localization boundary"),
    ("HighHighDominanceClosed", "highHighDominanceClosed", "supply explicit high-high/dominance theorem"),
    ("DominanceGateClosed", "dangerShellDissipationDominatesInfluxClosed", "supply danger-shell dissipation dominance"),
    ("PointwiseTailClosed", "pointwiseTailFromLocalDissipationClosed", "supply pointwise tail extraction"),
    ("IndependentCoefficientClosed", "independentCoefficientBudgetClosed", "supply independent coefficient budget"),
    ("ClayNavierStokesPromoted", "clayNavierStokesPromoted", "keep Clay Navier-Stokes promotion false"),
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


def exported(text: str, field: str) -> bool:
    leaf = field.split(".")[-1]
    return bool(re.search(rf"(?m)\b{re.escape(leaf)}\b\s*(?::|=)", text))


def equality_to_bool(text: str, field: str, expected: bool) -> bool:
    raw = "true" if expected else "false"
    leaf = field.split(".")[-1]
    dotted = re.escape(field)
    simple = re.escape(leaf)
    return bool(
        re.search(rf"(?m)\b(?:{dotted}|{simple})\b[^\n]*\n?\s*≡\s*\n?\s*{raw}\b", text)
        or re.search(rf"(?m)\b(?:{dotted}|{simple})\b[^\n]*≡\s*{raw}\b", text)
    )


def true_assignment_detected(text: str, field: str, values: dict[str, bool]) -> bool:
    leaf = field.split(".")[-1]
    return values.get(leaf) is True or bool(
        re.search(rf"(?m)\b{re.escape(leaf)}\b\s*=\s*true\b", text)
    )


def forbidden_hits(text: str) -> list[dict[str, Any]]:
    return [
        {"line": text.count("\n", 0, match.start()) + 1, "term": match.group(0)}
        for match in FORBIDDEN_WORDS.finditer(text)
    ]


def source_rows(repo_root: Path, text: str) -> list[dict[str, Any]]:
    missing = [anchor for anchor in REQUIRED_ANCHORS if anchor not in text]
    present = (repo_root / RECEIPT_REL).exists()
    return [
        {
            "source_id": "S1",
            "surface_name": "NSSprint92MovingKStarLocalizationBoundary",
            "path": RECEIPT_REL.as_posix(),
            "present_in_repo": present,
            "required_anchors": "; ".join(REQUIRED_ANCHORS),
            "missing_anchors": "; ".join(missing) if missing else "none",
            "status": "PASS" if present and not missing else "FAIL",
        }
    ]


def gate_rows(text: str, values: dict[str, bool], anchors_ok: bool, forbidden: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    base_ok = anchors_ok and not forbidden
    gate_id = 1
    for gate_name, field, next_input in TRUE_GATES:
        leaf = field.split(".")[-1]
        actual = values.get(leaf)
        evidence = actual is True or equality_to_bool(text, field, True)
        passed = base_ok and evidence
        rows.append(
            {
                "gate_id": f"G{gate_id}",
                "gate_name": gate_name,
                "field_name": field,
                "exported": exported(text, field),
                "actual_value": actual if actual is not None else evidence,
                "expected_value": True,
                "passed": passed,
                "status": "TRUE_BOOKKEEPING_RECORDED" if passed else "FAIL_CLOSED_VALUE_OR_ANCHOR",
                "next_required_input": next_input,
            }
        )
        gate_id += 1
    for gate_name, field, next_input in FALSE_GATES:
        leaf = field.split(".")[-1]
        actual = values.get(leaf)
        false_evidence = actual is False or equality_to_bool(text, field, False)
        is_exported = exported(text, field)
        true_violation = true_assignment_detected(text, field, values)
        passed = base_ok and ((not is_exported) or false_evidence) and not true_violation
        if true_violation:
            status = "TRUE_CLOSURE_OR_PROMOTION_VIOLATION_FAIL_CLOSED"
        elif not anchors_ok:
            status = "FAIL_CLOSED_MISSING_ANCHOR"
        elif forbidden:
            status = "FAIL_CLOSED_FORBIDDEN_LANGUAGE"
        elif not is_exported:
            status = "NOT_EXPORTED_FALSE_BY_BOUNDARY"
        elif passed and field == "clayNavierStokesPromoted":
            status = "FALSE_NO_CLAY_PROMOTION"
        elif passed:
            status = "FALSE_BOUNDARY_OPEN"
        else:
            status = "VALUE_MISMATCH_FAIL_CLOSED"
        rows.append(
            {
                "gate_id": f"G{gate_id}",
                "gate_name": gate_name,
                "field_name": field,
                "exported": is_exported,
                "actual_value": actual if actual is not None else false_evidence,
                "expected_value": False if is_exported else "not_exported_or_false",
                "passed": passed,
                "status": status,
                "next_required_input": next_input,
            }
        )
        gate_id += 1
    rows.append(
        {
            "gate_id": f"G{gate_id}",
            "gate_name": "NoForbiddenStubOrHoleLanguage",
            "field_name": "forbidden_terms",
            "exported": True,
            "actual_value": len(forbidden),
            "expected_value": 0,
            "passed": base_ok,
            "status": "PASS" if base_ok else "FAIL_CLOSED_FORBIDDEN_OR_MISSING",
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
    gates = gate_rows(text, values, anchors_ok, forbidden)
    false_gate_failures = [row for row in gates if row["expected_value"] is False and not row["passed"]]
    true_gate_failures = [row for row in gates if row["expected_value"] is True and not row["passed"]]
    fail_closed = not anchors_ok or bool(forbidden) or bool(false_gate_failures) or bool(true_gate_failures)
    value_or_false = lambda name: values.get(name, False)
    summary = {
        "contract": CONTRACT,
        "complete": False,
        "route_decision": FAIL_CLOSED if fail_closed else ROUTE_OPEN,
        "final_decision": "FAIL_CLOSED" if fail_closed else "BOUNDARY_AUDIT_PASS",
        "receipt_path": RECEIPT_REL.as_posix(),
        "source_table": SOURCE_TABLE,
        "gate_table": GATE_TABLE,
        "rows_json": ROWS_JSON_NAME,
        "report": REPORT_NAME,
        "all_required_receipt_anchors_present": anchors_ok,
        "forbidden_terms_detected": forbidden,
        "forbidden_term_count": len(forbidden),
        "fail_closed": fail_closed,
        "closed_frozen_danger_time_bookkeeping_true": values.get(
            "fixedDangerTimeFrozenKBookkeepingClosed"
        ),
        "closed_frozen_k_bookkeeping_true": values.get("fixedDangerTimeFrozenKBookkeepingClosed"),
        "moving_boundary_theorem_closed": values.get(
            "movingInTimeKStarLocalizationBoundaryClosed"
        ),
        "moving_k_boundary_closed": values.get("movingInTimeKStarLocalizationBoundaryClosed"),
        "moving_k_boundary_phrase": "moving K boundary remains open",
        "anchor_phrases": [
            "frozen danger-time",
            "moving K boundary",
            "pointwise H1 tail",
            "independent coefficient",
            "Clay",
        ],
        "non_circular_high_high_control_closed": values.get("highHighDominanceClosed"),
        "edge_influx_bound_closed": False,
        "theta_preservation_closed": False,
        "high_high_dominance_closed": value_or_false("highHighDominanceClosed"),
        "dominance_gate_closed": value_or_false("dangerShellDissipationDominatesInfluxClosed"),
        "pointwise_tail_closed": value_or_false("pointwiseTailFromLocalDissipationClosed"),
        "independent_coefficient_closed": value_or_false("independentCoefficientBudgetClosed"),
        "pointwise_independent_coefficient_closed": False,
        "clay_navier_stokes_promoted": values.get("clayNavierStokesPromoted"),
        "true_gate_failures": [row["gate_name"] for row in true_gate_failures],
        "false_gate_failures": [row["gate_name"] for row in false_gate_failures],
        "gate_results": gates,
        "source_results": sources,
        "open_obligations": [
            "prove the moving K*(t) localization boundary theorem",
            "prove non-circular high-high/dominance control",
            "prove edge influx and theta preservation at the danger shell",
            "supply pointwise tail extraction with an independent coefficient budget",
            "keep Clay Navier-Stokes promotion false until all analytic gates close",
        ],
    }
    return summary, sources, gates


def markdown(summary: dict[str, Any], sources: list[dict[str, Any]], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 92 Moving K-star Boundary Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Decision: `{summary['final_decision']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Receipt: `{summary['receipt_path']}`",
        f"- Anchors present: `{summary['all_required_receipt_anchors_present']}`",
        f"- Forbidden term count: `{summary['forbidden_term_count']}`",
        f"- Closed frozen-K bookkeeping true: `{summary['closed_frozen_k_bookkeeping_true']}`",
        f"- Moving boundary theorem closed: `{summary['moving_boundary_theorem_closed']}`",
        f"- Non-circular high-high control closed: `{summary['non_circular_high_high_control_closed']}`",
        f"- Pointwise tail closed: `{summary['pointwise_tail_closed']}`",
        f"- Independent coefficient closed: `{summary['independent_coefficient_closed']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Gates",
        "",
        "| Gate | Exported | Expected | Actual | Status |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in gates:
        lines.append(
            f"| `{row['gate_name']}` | `{row['exported']}` | `{row['expected_value']}` | "
            f"`{row['actual_value']}` | `{row['status']}` |"
        )
    lines.extend(["", "## Source Surfaces", ""])
    for row in sources:
        lines.append(
            f"- `{row['source_id']}` `{row['path']}`: `{row['status']}`, "
            f"missing anchors `{row['missing_anchors']}`."
        )
    lines.extend(["", "## Open Obligations", ""])
    lines.extend(f"- {item}" for item in summary["open_obligations"])
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary, sources, gates = build(args.repo_root)
    write_csv(args.out_dir / SOURCE_TABLE, sources)
    write_csv(args.out_dir / GATE_TABLE, gates)
    (args.out_dir / ROWS_JSON_NAME).write_text(
        json.dumps({"sources": sources, "gates": gates}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (args.out_dir / REPORT_NAME).write_text(
        markdown(summary, sources, gates),
        encoding="utf-8",
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
