#!/usr/bin/env python3
"""Sprint 91 NS localized flux identity and coefficient budget audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint91_localized_flux_identity_audit"
ROUTE_OPEN = "NS_SPRINT91_LOCALIZED_FLUX_IDENTITY_ROUTE_OPEN"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint91_localized_flux_identity_audit")
SUMMARY_NAME = "ns_sprint91_localized_flux_identity_audit_summary.json"
ROWS_JSON_NAME = "ns_sprint91_localized_flux_identity_audit_rows.json"
SOURCE_TABLE = "ns_sprint91_localized_flux_identity_source_table.csv"
GATE_TABLE = "ns_sprint91_localized_flux_identity_gate_table.csv"
REPORT_NAME = "ns_sprint91_localized_flux_identity_audit.md"

RECEIPT_REL = Path(
    "DASHI/Physics/Closure/NSSprint91LocalizedFluxIdentityAndCoefficientBudget.agda"
)

RECEIPT_ANCHORS = [
    "NSSprint91LocalizedFluxIdentityAndCoefficientBudget",
    "canonicalNSSprint91LocalizedFluxIdentityAndCoefficientBudget",
    "LocalizedFluxIdentityImportedFromFixedKLP",
    "canonicalLocalizedFluxIdentityImportedFromFixedKLP",
    "Sprint91ClosedBookkeeping",
    "canonicalSprint91ClosedBookkeeping",
    "fullFixedKLPIdentityImported",
    "localizedFluxIdentityBookedAtFixedK",
    "localizedEnstrophyFluxIdentityClosed",
    "localizedEnstrophyFluxIdentityClosedIsTrue",
    "dangerShellDissipationDominatesInfluxClosed",
    "dangerShellDissipationDominatesInfluxClosedIsFalse",
    "pointwiseTailFromLocalDissipationClosed",
    "pointwiseTailFromLocalDissipationClosedIsFalse",
    "independentCoefficientBudgetClosed",
    "independentCoefficientBudgetClosedIsFalse",
    "clayNavierStokesPromoted",
    "clayNavierStokesPromotedIsFalse",
    "canonicalSprint91Flags",
]

OPTIONAL_TRUE_EXPORTS = [
    (
        "LocalizedEnstrophyFluxIdentityClosed",
        "localizedEnstrophyFluxIdentityClosed",
        "localized enstrophy flux identity bookkeeping is closed",
    ),
    (
        "FullIdentityFixedK",
        "fullIdentityFixedK",
        "fixed-K identity import proof field is exported as true",
    ),
    (
        "LocalizedFluxIdentityClosedHere",
        "localizedFluxIdentityClosedHere",
        "coefficient ledger records localized flux identity closure as true",
    ),
]

FALSE_GATES = [
    (
        "ClayNavierStokesPromoted",
        "clayNavierStokesPromoted",
        "keep Clay Navier-Stokes promotion false",
    ),
    (
        "DominanceGateClosed",
        "dangerShellDissipationDominatesInfluxClosed",
        "keep dominance gate false",
    ),
    (
        "PointwiseTailFromLocalDissipationClosed",
        "pointwiseTailFromLocalDissipationClosed",
        "keep pointwise extraction gate false",
    ),
    (
        "PointwiseH1TailWithIndependentEpsilonCoefficientClosed",
        "pointwiseH1TailWithIndependentEpsilonCoefficientClosed",
        "keep pointwise/independent coefficient gate false",
    ),
    (
        "IndependentCoefficientBudgetClosed",
        "independentCoefficientBudgetClosed",
        "keep independent coefficient budget gate false",
    ),
    (
        "IndependentEpsilonCoefficientClosed",
        "independentEpsilonCoefficientClosed",
        "keep independent epsilon coefficient gate false",
    ),
    (
        "LocalizedFluxIdentityAliasClosed",
        "localizedFluxIdentityClosed",
        "keep unexported localized flux identity alias false if introduced",
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


def exported(text: str, field: str) -> bool:
    return bool(re.search(rf"(?m)\b{re.escape(field)}\b\s*(?::|=)", text))


def equal_to_bool(text: str, field: str, expected: bool) -> bool:
    raw = "true" if expected else "false"
    return bool(
        re.search(
            rf"(?m)\b{re.escape(field)}\b(?:[^\n]*\n){{0,2}}[^\n]*≡\s*{raw}\b",
            text,
        )
    )


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
    receipt_exists = (repo_root / RECEIPT_REL).exists()
    missing = [anchor for anchor in RECEIPT_ANCHORS if anchor not in receipt_text]
    return [
        {
            "source_id": "S1",
            "surface_name": "Sprint91LocalizedFluxIdentityAndCoefficientBudget",
            "path": RECEIPT_REL.as_posix(),
            "present_in_repo": receipt_exists,
            "required_anchors": "; ".join(RECEIPT_ANCHORS),
            "missing_anchors": "; ".join(missing) if missing else "none",
            "status": "PASS" if receipt_exists and not missing else "FAIL",
        }
    ]


def gate_rows(
    text: str,
    values: dict[str, bool],
    anchors_ok: bool,
    forbidden: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    base_ok = anchors_ok and not forbidden
    gate_id = 1
    for gate_name, field, next_input in OPTIONAL_TRUE_EXPORTS:
        is_exported = exported(text, field)
        actual = values.get(field)
        truth_evidence = actual is True or equal_to_bool(text, field, True)
        passed = base_ok and ((not is_exported) or truth_evidence)
        if not anchors_ok:
            status = "FAIL_CLOSED_MISSING_ANCHOR"
        elif forbidden:
            status = "FAIL_CLOSED_FORBIDDEN_LANGUAGE"
        elif not is_exported:
            status = "NOT_EXPORTED"
        elif passed:
            status = "TRUE_BOOKKEEPING_RECORDED"
        else:
            status = "VALUE_MISMATCH_FAIL_CLOSED"
        rows.append(
            {
                "gate_id": f"G{gate_id}",
                "gate_name": gate_name,
                "field_name": field,
                "exported": is_exported,
                "actual_value": actual if actual is not None else truth_evidence,
                "expected_value": True if is_exported else "not_exported_or_true",
                "passed": passed,
                "status": status,
                "next_required_input": next_input,
            }
        )
        gate_id += 1
    for gate_name, field, next_input in FALSE_GATES:
        actual = values.get(field)
        false_evidence = actual is False or equal_to_bool(text, field, False)
        true_violation = true_assignment_detected(text, field, values)
        is_exported = exported(text, field)
        passed = base_ok and ((not is_exported) or false_evidence) and not true_violation
        if true_violation:
            status = "TRUE_CLOSURE_OR_PROMOTION_VIOLATION_FAIL_CLOSED"
        elif not anchors_ok:
            status = "FAIL_CLOSED_MISSING_ANCHOR"
        elif forbidden:
            status = "FAIL_CLOSED_FORBIDDEN_LANGUAGE"
        elif not is_exported:
            status = "NOT_EXPORTED"
        elif passed and field == "clayNavierStokesPromoted":
            status = "FALSE_NO_PROMOTION"
        elif passed:
            status = "FALSE_ANALYTIC_GATE_OPEN"
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
    fail_closed = not anchors_ok or bool(forbidden) or any(not row["passed"] for row in gates)
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
        "bookkeeping_flags": {
            field: {
                "exported": exported(text, field),
                "value": values.get(field),
            }
            for _, field, _ in OPTIONAL_TRUE_EXPORTS
        },
        "guarded_false_flags": {field: values.get(field) for _, field, _ in FALSE_GATES},
        "clay_navier_stokes_promoted": values.get("clayNavierStokesPromoted"),
        "localized_enstrophy_flux_identity_closed": values.get(
            "localizedEnstrophyFluxIdentityClosed"
        ),
        "localized_flux_identity_closed": values.get("localizedFluxIdentityClosed"),
        "dominance_gate_closed": values.get("dangerShellDissipationDominatesInfluxClosed"),
        "pointwise_gate_closed": values.get("pointwiseTailFromLocalDissipationClosed"),
        "independent_coefficient_budget_closed": values.get("independentCoefficientBudgetClosed"),
        "independent_epsilon_coefficient_closed": values.get("independentEpsilonCoefficientClosed"),
        "gate_results": gates,
        "source_results": sources,
        "open_obligations": [
            "materialize the Sprint 91 receipt at the audited path if missing",
            "export fixed-k/localized flux identity bookkeeping as true when the receipt claims it",
            "keep dominance, pointwise, and independent coefficient gates false until proved",
            "keep Clay Navier-Stokes promotion false",
        ],
    }
    return summary, sources, gates


def markdown(summary: dict[str, Any], sources: list[dict[str, Any]], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 91 Localized Flux Identity Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Receipt: `{summary['receipt_path']}`",
        f"- Anchors present: `{summary['all_required_receipt_anchors_present']}`",
        f"- Forbidden term count: `{summary['forbidden_term_count']}`",
        f"- Localized enstrophy flux identity closed: "
        f"`{summary['localized_enstrophy_flux_identity_closed']}`",
        f"- Dominance gate closed: `{summary['dominance_gate_closed']}`",
        f"- Pointwise gate closed: `{summary['pointwise_gate_closed']}`",
        f"- Independent coefficient budget closed: "
        f"`{summary['independent_coefficient_budget_closed']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
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
