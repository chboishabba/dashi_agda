#!/usr/bin/env python3
"""Sprint 93 NS dominance/pointwise/coefficient audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint93_dominance_pointwise_coefficient_audit"
ROUTE_OPEN = "open"
FAIL_CLOSED = "fail_closed"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint93_dominance_pointwise_coefficient_audit")
SUMMARY_NAME = "ns_sprint93_dominance_pointwise_coefficient_audit_summary.json"
ROWS_JSON_NAME = "ns_sprint93_dominance_pointwise_coefficient_audit_rows.json"
SOURCE_TABLE = "ns_sprint93_dominance_pointwise_coefficient_source_table.csv"
GATE_TABLE = "ns_sprint93_dominance_pointwise_coefficient_gate_table.csv"
REPORT_NAME = "ns_sprint93_dominance_pointwise_coefficient_audit.md"

RECEIPT_CANDIDATES = [
    Path("DASHI/Physics/Closure/NSSprint93DominancePointwiseCoefficientLedger.agda"),
    Path("DASHI/Physics/Closure/NSSprint93DominancePointwiseCoefficientBoundary.agda"),
    Path("DASHI/Physics/Closure/NSSprint93DominancePointwiseCoefficientReceipt.agda"),
    Path("DASHI/Physics/Closure/NSSprint93DominancePointwiseTailAndIndependentCoefficient.agda"),
    Path("DASHI/Physics/Closure/NSSprint93DominancePointwiseTailAndIndependentCoefficientBoundary.agda"),
]

REQUIRED_RESIDUAL_GATE = "DominanceWithPointwiseTailAndIndependentCoefficient"

REQUIRED_ANCHORS = [
    "NSSprint93",
    "Sprint93",
    "DominanceWithPointwiseTailAndIndependentCoefficient",
    "canonical",
    "Sprint92",
    "inherited",
    "Bookkeeping",
    "dangerShellDissipationDominatesInfluxClosed",
    "pointwiseTailFromLocalDissipationClosed",
    "highHighDominanceClosed",
    "independentCoefficientBudgetClosed",
    "clayNavierStokesPromoted",
]

INHERITED_BOOKKEEPING_TRUE_GATES = [
    "inheritedBookkeepingClosed",
    "sprint92BookkeepingInherited",
    "sprint92BookkeepingInheritedClosed",
    "sprint92FrozenKBookkeepingInherited",
    "sprint92FrozenKBookkeepingClosed",
    "fixedDangerTimeFrozenKBookkeepingClosed",
]

ANALYTIC_FALSE_GATES = [
    "dangerShellDissipationDominatesInfluxClosed",
    "pointwiseTailFromLocalDissipationClosed",
    "highHighDominanceClosed",
    "independentCoefficientBudgetClosed",
    "dominanceWithPointwiseTailAndIndependentCoefficientClosed",
    "dominancePointwiseCoefficientClosed",
    "analyticDominanceGateClosed",
    "pointwiseIndependentCoefficientClosed",
]

CLAY_FALSE_GATES = [
    "clayNavierStokesPromoted",
]

FORBIDDEN_WORDS = re.compile(
    r"(?im)\b(postulate|todo|stub|placeholder|future\s+proof|future-proof|futureproof|hole|admit|sorry)\b"
)
BOOL_DECL = re.compile(
    r"(?m)^\s*([A-Za-z][A-Za-z0-9']*)\s*:\s*Bool\s*\n"
    r"\s*\1\s*=\s*(true|false)\s*$"
)
FIELD_ASSIGN = re.compile(r"(?m)^\s*;\s*([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def select_receipt(repo_root: Path) -> Path:
    for rel in RECEIPT_CANDIDATES:
        if (repo_root / rel).exists():
            return rel
    matches = sorted(
        (repo_root / "DASHI/Physics/Closure").glob("NSSprint93*.agda")
        if (repo_root / "DASHI/Physics/Closure").exists()
        else []
    )
    return matches[0].relative_to(repo_root) if matches else RECEIPT_CANDIDATES[0]


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def bools(text: str) -> dict[str, bool]:
    values = {name: raw == "true" for name, raw in BOOL_DECL.findall(text)}
    values.update({name: raw == "true" for name, raw in FIELD_ASSIGN.findall(text)})
    return values


def equality_to_bool(text: str, field: str, expected: bool) -> bool:
    raw = "true" if expected else "false"
    return bool(re.search(rf"(?m)\b{re.escape(field)}\b[^\n]*≡\s*{raw}\b", text))


def bool_evidence(text: str, values: dict[str, bool], fields: list[str], expected: bool) -> list[str]:
    evidence: list[str] = []
    for field in fields:
        if values.get(field) is expected or equality_to_bool(text, field, expected):
            evidence.append(field)
    return evidence


def forbidden_hits(text: str) -> list[dict[str, Any]]:
    return [
        {"line": text.count("\n", 0, match.start()) + 1, "term": match.group(0)}
        for match in FORBIDDEN_WORDS.finditer(text)
    ]


def source_rows(receipt_rel: Path, text: str, present: bool) -> list[dict[str, Any]]:
    missing = [anchor for anchor in REQUIRED_ANCHORS if anchor not in text]
    return [
        {
            "source_id": "S1",
            "surface_name": "NSSprint93 dominance pointwise coefficient receipt",
            "path": receipt_rel.as_posix(),
            "present_in_repo": present,
            "required_anchors": "; ".join(REQUIRED_ANCHORS),
            "missing_anchors": "; ".join(missing) if missing else "none",
            "status": "PASS" if present and not missing else "FAIL_CLOSED",
        }
    ]


def gate_rows(
    text: str,
    values: dict[str, bool],
    anchors_ok: bool,
    forbidden: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    hygiene_ok = not forbidden
    rows: list[dict[str, Any]] = []

    inherited_hits = bool_evidence(text, values, INHERITED_BOOKKEEPING_TRUE_GATES, True)
    inherited_passed = hygiene_ok and bool(inherited_hits)
    rows.append(
        {
            "gate_id": "G1",
            "gate_name": "InheritedBookkeepingTrue",
            "field_name": "; ".join(INHERITED_BOOKKEEPING_TRUE_GATES),
            "actual_value": "; ".join(inherited_hits) if inherited_hits else "none",
            "expected_value": "at least one true inherited bookkeeping gate",
            "passed": inherited_passed,
            "status": "TRUE_BOOKKEEPING_RECORDED" if inherited_passed else "FAIL_CLOSED",
            "next_required_input": "record inherited Sprint92 bookkeeping as true",
        }
    )

    for index, field in enumerate(ANALYTIC_FALSE_GATES, start=2):
        exported = field in text
        actual = values.get(field)
        false_evidence = actual is False or equality_to_bool(text, field, False)
        true_violation = actual is True or equality_to_bool(text, field, True)
        passed = hygiene_ok and ((not exported) or false_evidence) and not true_violation
        rows.append(
            {
                "gate_id": f"G{index}",
                "gate_name": f"AnalyticGateFalse:{field}",
                "field_name": field,
                "actual_value": actual if actual is not None else ("not_exported" if not exported else false_evidence),
                "expected_value": "false_or_not_exported",
                "passed": passed,
                "status": (
                    "TRUE_ANALYTIC_GATE_VIOLATION"
                    if true_violation
                    else "FALSE_ANALYTIC_GATE_OPEN"
                    if passed
                    else "FAIL_CLOSED"
                ),
                "next_required_input": "keep analytic gates false until a non-circular proof is supplied",
            }
        )

    offset = len(rows) + 1
    for index, field in enumerate(CLAY_FALSE_GATES, start=offset):
        exported = field in text
        actual = values.get(field)
        false_evidence = actual is False or equality_to_bool(text, field, False)
        true_violation = actual is True or equality_to_bool(text, field, True)
        passed = hygiene_ok and ((not exported) or false_evidence) and not true_violation
        rows.append(
            {
                "gate_id": f"G{index}",
                "gate_name": f"ClayFalse:{field}",
                "field_name": field,
                "actual_value": actual if actual is not None else ("not_exported" if not exported else false_evidence),
                "expected_value": "false_or_not_exported",
                "passed": passed,
                "status": "FALSE_NO_CLAY_PROMOTION" if passed else "FAIL_CLOSED_CLAY",
                "next_required_input": "keep Clay promotion false",
            }
        )

    exact_count = text.count(REQUIRED_RESIDUAL_GATE)
    rows.append(
        {
            "gate_id": f"G{len(rows) + 1}",
            "gate_name": "ResidualGateExact",
            "field_name": "required_residual_gate",
            "actual_value": REQUIRED_RESIDUAL_GATE if exact_count else "missing",
            "expected_value": REQUIRED_RESIDUAL_GATE,
            "passed": anchors_ok and hygiene_ok and exact_count > 0,
            "status": "EXACT_RESIDUAL_GATE_RECORDED" if anchors_ok and hygiene_ok and exact_count > 0 else "FAIL_CLOSED_RESIDUAL_GATE",
            "next_required_input": f"record residual gate exactly {REQUIRED_RESIDUAL_GATE}",
        }
    )
    rows.append(
        {
            "gate_id": f"G{len(rows) + 1}",
            "gate_name": "NoForbiddenMarkers",
            "field_name": "forbidden_terms",
            "actual_value": len(forbidden),
            "expected_value": 0,
            "passed": not forbidden,
            "status": "PASS" if not forbidden else "FAIL_CLOSED_FORBIDDEN_MARKER",
            "next_required_input": "remove forbidden markers",
        }
    )
    return rows


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def build(repo_root: Path) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    receipt_rel = select_receipt(repo_root)
    receipt_path = repo_root / receipt_rel
    text = read_text(receipt_path)
    present = receipt_path.exists()
    values = bools(text)
    sources = source_rows(receipt_rel, text, present)
    anchors_ok = sources[0]["status"] == "PASS"
    forbidden = forbidden_hits(text)
    gates = gate_rows(text, values, anchors_ok, forbidden)
    failures = [row for row in gates if not row["passed"]]
    fail_closed = bool(failures) or not anchors_ok or bool(forbidden)
    analytic_gate_values = {
        field: values.get(field, False) if field in text else False
        for field in ANALYTIC_FALSE_GATES
    }
    clay_values = {
        field: values.get(field, False) if field in text else False
        for field in CLAY_FALSE_GATES
    }
    summary = {
        "contract": CONTRACT,
        "complete": False,
        "route_decision": FAIL_CLOSED if fail_closed else ROUTE_OPEN,
        "final_decision": "FAIL_CLOSED" if fail_closed else "BOUNDARY_AUDIT_PASS",
        "receipt_path": receipt_rel.as_posix(),
        "source_table": SOURCE_TABLE,
        "gate_table": GATE_TABLE,
        "rows_json": ROWS_JSON_NAME,
        "report": REPORT_NAME,
        "all_required_receipt_anchors_present": anchors_ok,
        "forbidden_terms_detected": forbidden,
        "forbidden_term_count": len(forbidden),
        "fail_closed": fail_closed,
        "inherited_bookkeeping_true": gates[0]["passed"],
        "all_analytic_gates_false": all(value is False for value in analytic_gate_values.values()),
        "analytic_gate_values": analytic_gate_values,
        "clay_promotion": False,
        "clay_navier_stokes_promoted": False,
        "clay_gate_values": clay_values,
        "high_high_anchor_phrase": "high-high",
        "required_residual_gate": REQUIRED_RESIDUAL_GATE,
        "residual_gate_exactly_recorded": REQUIRED_RESIDUAL_GATE,
        "residual_gate_present": REQUIRED_RESIDUAL_GATE in text,
        "gate_failures": [row["gate_name"] for row in failures],
        "gate_results": gates,
        "source_results": sources,
        "open_obligations": [
            "preserve inherited Sprint92 bookkeeping as true",
            "keep all dominance, pointwise-tail, independent-coefficient, and analytic closure gates false",
            f"record residual gate exactly {REQUIRED_RESIDUAL_GATE}",
            "keep Clay Navier-Stokes promotion false",
        ],
    }
    return summary, sources, gates


def markdown(summary: dict[str, Any], sources: list[dict[str, Any]], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 93 Dominance Pointwise Coefficient Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Decision: `{summary['final_decision']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Receipt: `{summary['receipt_path']}`",
        f"- Anchors present: `{summary['all_required_receipt_anchors_present']}`",
        f"- Forbidden term count: `{summary['forbidden_term_count']}`",
        f"- Inherited bookkeeping true: `{summary['inherited_bookkeeping_true']}`",
        f"- All analytic gates false: `{summary['all_analytic_gates_false']}`",
        f"- Clay promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Residual gate: `{summary['required_residual_gate']}`",
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
