#!/usr/bin/env python3
"""Sprint 89 NS pointwise H1-tail mechanism audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint89_pointwise_h1_tail_mechanism_audit"
ROUTE_OPEN = "NS_SPRINT89_POINTWISE_H1_TAIL_MECHANISM_OPEN"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint89_pointwise_h1_tail_mechanism_audit")
SUMMARY_NAME = "ns_sprint89_pointwise_h1_tail_mechanism_summary.json"
SOURCE_TABLE = "ns_sprint89_pointwise_h1_tail_mechanism_source_table.csv"
GATE_TABLE = "ns_sprint89_pointwise_h1_tail_mechanism_gate_table.csv"
REPORT_NAME = "ns_sprint89_pointwise_h1_tail_mechanism_report.md"

RECEIPT_CANDIDATES = [
    Path("DASHI/Physics/Closure/NSSprint89PointwiseH1TailCandidateMechanismReceipt.agda"),
    Path("DASHI/Physics/Closure/NSSprint89PointwiseH1TailMechanismReceipt.agda"),
    Path("DASHI/Physics/Closure/NSSprint89PointwiseH1TailWithIndependentEpsilonCoefficientReceipt.agda"),
    Path("DASHI/Physics/Closure/NSSprint89DangerShellPointwiseH1TailMechanismReceipt.agda"),
]

SUPPORT_SURFACES = [
    (
        "Sprint88H1TailSmallnessDecisionReceipt",
        "DASHI/Physics/Closure/NSSprint88DangerShellH1TailSmallnessDecisionReceipt.agda",
        ["canonicalNSSprint88H1TailSmallnessDecisionReceipt"],
    ),
    (
        "Sprint88TailSourceClassifier",
        "scripts/ns_sprint88_tail_source_classifier.py",
        ["PointwiseH1TailWithIndependentEpsilonCoefficient"],
    ),
]

RECEIPT_ANCHORS = [
    "canonicalNSSprint89PointwiseH1TailCandidateMechanismReceipt",
    "canonicalNSSprint89H1TailCandidateMechanismReceipt",
    "NSSprint89PointwiseH1TailCandidateMechanismReceipt",
    "PointwiseH1TailWithIndependentEpsilonCoefficient",
    "canonicalCandidateSubMechanisms",
    "canonicalCandidateMechanismClassifications",
    "canonicalFailClosedBoundaries",
    "localEnstrophyDangerShellDissipationMechanismClassified",
    "timeIntegratedToPointwiseConversionClassified",
    "coefficientIndependenceClassified",
    "noSelfUseOfAbsorptionClassified",
    "localEnstrophyDangerShellDissipationClosed",
    "timeIntegratedToPointwiseConversionClosed",
    "independentEpsilonCoefficientClosed",
    "noSelfUseOfAbsorptionClosed",
    "pointwiseH1TailWithIndependentEpsilonCoefficientClosed",
    "sprint88DangerShellAbsorptionStillOpen",
    "clayNavierStokesPromoted",
]

AUDIT_ANCHOR_ALIASES = [
    "canonicalNSSprint89PointwiseH1TailMechanismReceipt",
    "sprint88H1TailDecisionInheritedClosed",
    "pointwiseH1TailMechanismClosed",
    "dangerShellTailSmallnessClosed",
    "dangerShellAbsorptionConditionClosed",
    "clayNavierStokesPromoted",
]

GATE_SPECS = [
    (
        "G1",
        "LocalEnstrophyDangerShellDissipationMechanismClassified",
        "localEnstrophyDangerShellDissipationMechanismClassified",
        True,
        "local enstrophy danger-shell dissipation mechanism is classified",
    ),
    (
        "G2",
        "TimeIntegratedToPointwiseConversionClassified",
        "timeIntegratedToPointwiseConversionClassified",
        True,
        "time-integrated to pointwise conversion mechanism is classified",
    ),
    (
        "G3",
        "CoefficientIndependenceClassified",
        "coefficientIndependenceClassified",
        True,
        "coefficient independence mechanism is classified",
    ),
    (
        "G4",
        "NoSelfUseOfAbsorptionClassified",
        "noSelfUseOfAbsorptionClassified",
        True,
        "no self-use of absorption is classified as a governance constraint",
    ),
    (
        "G5",
        "LocalEnstrophyDangerShellDissipationClosed",
        "localEnstrophyDangerShellDissipationClosed",
        False,
        "derive local enstrophy danger-shell dissipation before closing the mechanism",
    ),
    (
        "G6",
        "TimeIntegratedToPointwiseConversionClosed",
        "timeIntegratedToPointwiseConversionClosed",
        False,
        "derive non-circular time localization before closing the mechanism",
    ),
    (
        "G7",
        "IndependentEpsilonCoefficientClosed",
        "independentEpsilonCoefficientClosed",
        False,
        "derive an epsilon<1 coefficient independent of the target absorption inequality",
    ),
    (
        "G8",
        "NoSelfUseOfAbsorptionClosed",
        "noSelfUseOfAbsorptionClosed",
        True,
        "enforce that absorption is not used to prove its own coefficient",
    ),
    (
        "G9",
        "PointwiseH1TailWithIndependentEpsilonCoefficientClosed",
        "pointwiseH1TailWithIndependentEpsilonCoefficientClosed",
        False,
        "close both the pointwise H1 tail and independent epsilon coefficient",
    ),
    (
        "G10",
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
    r"(?im)\b(postulate|todo|stub|future\s+proof|future-proof|futureproof)\b"
)
CLAY_TRUE = re.compile(r"(?m)\bclayNavierStokesPromoted\b\s*(?:=|:=[^\n]*=)\s*true\b")
POINTWISE_CLOSED_TRUE = re.compile(
    r"(?m)\bpointwiseH1TailWithIndependentEpsilonCoefficientClosed\b\s*"
    r"(?:=|:=[^\n]*=)\s*true\b"
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


def receipt_path(repo_root: Path) -> Path:
    for rel in RECEIPT_CANDIDATES:
        if (repo_root / rel).exists():
            return rel
    closure_dir = repo_root / "DASHI/Physics/Closure"
    for path in sorted(closure_dir.glob("NSSprint89*.agda")):
        text = read_text(path)
        if any(anchor in text for anchor in RECEIPT_ANCHORS):
            return path.relative_to(repo_root)
    return RECEIPT_CANDIDATES[0]


def forbidden_hits(text: str) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for match in FORBIDDEN_WORDS.finditer(text):
        line = text.count("\n", 0, match.start()) + 1
        hits.append({"line": line, "term": match.group(0)})
    return hits


def source_rows(repo_root: Path, receipt_rel: Path, receipt_text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    receipt_exists = (repo_root / receipt_rel).exists()
    missing = [anchor for anchor in RECEIPT_ANCHORS if anchor not in receipt_text]
    rows.append(
        {
            "source_id": "S1",
            "surface_name": "Sprint89PointwiseH1TailCandidateMechanismReceipt",
            "path": receipt_rel.as_posix(),
            "present_in_repo": receipt_exists,
            "required_anchors": "; ".join(RECEIPT_ANCHORS),
            "audit_anchor_aliases": "; ".join(AUDIT_ANCHOR_ALIASES),
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
                "audit_anchor_aliases": "none",
                "missing_anchors": "; ".join(missing_support) if missing_support else "none",
                "status": "PASS" if (repo_root / rel).exists() and not missing_support else "FAIL",
            }
        )
    return rows


def gate_rows(
    values: dict[str, bool],
    anchors_ok: bool,
    forbidden: list[dict[str, Any]],
    clay_true_detected: bool,
    pointwise_closed_true_detected: bool,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for gate_id, gate_name, field, expected, next_input in GATE_SPECS:
        actual = values.get(field)
        passed = anchors_ok and not forbidden and actual is expected
        if gate_name == "ClayNavierStokesPromoted" and clay_true_detected:
            status = "PROMOTION_VIOLATION_FAIL_CLOSED"
            passed = False
        elif (
            gate_name == "PointwiseH1TailWithIndependentEpsilonCoefficientClosed"
            and pointwise_closed_true_detected
        ):
            status = "POINTWISE_H1_TAIL_CLOSURE_VIOLATION_FAIL_CLOSED"
            passed = False
        elif not anchors_ok:
            status = "FAIL_CLOSED_MISSING_ANCHOR"
        elif forbidden:
            status = "FAIL_CLOSED_FORBIDDEN_STUB_LANGUAGE"
        elif passed and expected is True:
            status = "CLOSED_RECORDED"
        elif passed and expected is False and gate_name == "ClayNavierStokesPromoted":
            status = "FALSE_NO_PROMOTION"
        elif passed and expected is False:
            status = "OPEN_FAIL_CLOSED"
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
                "clay_promotion": gate_name == "ClayNavierStokesPromoted" and actual is True,
                "next_required_input": next_input,
            }
        )
    rows.append(
        {
            "gate_id": "G11",
            "gate_name": "NoPostulateTodoStubFutureProofLanguage",
            "field_name": "forbidden_terms",
            "actual_value": len(forbidden),
            "expected_value": 0,
            "passed": anchors_ok and not forbidden,
            "status": "PASS" if anchors_ok and not forbidden else "FAIL_CLOSED_FORBIDDEN_OR_MISSING",
            "clay_promotion": False,
            "next_required_input": "remove postulate/TODO/stub/future proof language from Sprint89",
        }
    )
    return rows


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def build(repo_root: Path) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]:
    receipt_rel = receipt_path(repo_root)
    text = read_text(repo_root / receipt_rel)
    values = bools(text)
    sources = source_rows(repo_root, receipt_rel, text)
    anchors_ok = sources[0]["status"] == "PASS"
    forbidden = forbidden_hits(text)
    clay_true_detected = bool(CLAY_TRUE.search(text)) or values.get("clayNavierStokesPromoted") is True
    pointwise_closed_true_detected = (
        bool(POINTWISE_CLOSED_TRUE.search(text))
        or values.get("pointwiseH1TailWithIndependentEpsilonCoefficientClosed") is True
    )
    gates = gate_rows(
        values,
        anchors_ok,
        forbidden,
        clay_true_detected,
        pointwise_closed_true_detected,
    )
    mechanism_still_open = values.get("pointwiseH1TailWithIndependentEpsilonCoefficientClosed") is False
    fail_closed = (
        not anchors_ok
        or bool(forbidden)
        or clay_true_detected
        or pointwise_closed_true_detected
        or mechanism_still_open
        or any(not row["passed"] for row in gates)
    )
    summary = {
        "contract": CONTRACT,
        "complete": False,
        "route_decision": "fail_closed" if fail_closed else ROUTE_OPEN,
        "receipt_path": receipt_rel.as_posix(),
        "source_table": SOURCE_TABLE,
        "gate_table": GATE_TABLE,
        "report": REPORT_NAME,
        "all_required_receipt_anchors_present": anchors_ok,
        "audit_anchor_aliases": AUDIT_ANCHOR_ALIASES,
        "forbidden_terms_detected": forbidden,
        "forbidden_term_count": len(forbidden),
        "fail_closed": fail_closed,
        "clay_true_detected": clay_true_detected,
        "pointwise_h1_tail_with_independent_epsilon_true_detected": pointwise_closed_true_detected,
        "sprint88_h1_tail_decision_inherited_closed": True,
        "pointwise_h1_tail_mechanism_closed": values.get(
            "pointwiseH1TailWithIndependentEpsilonCoefficientClosed"
        ),
        "danger_shell_tail_smallness_closed": values.get(
            "pointwiseH1TailWithIndependentEpsilonCoefficientClosed"
        ),
        "danger_shell_absorption_condition_closed": values.get(
            "pointwiseH1TailWithIndependentEpsilonCoefficientClosed"
        ),
        "local_enstrophy_danger_shell_dissipation_mechanism_classified": values.get(
            "localEnstrophyDangerShellDissipationMechanismClassified"
        ),
        "time_integrated_to_pointwise_conversion_classified": values.get(
            "timeIntegratedToPointwiseConversionClassified"
        ),
        "coefficient_independence_classified": values.get("coefficientIndependenceClassified"),
        "no_self_use_of_absorption_classified": values.get("noSelfUseOfAbsorptionClassified"),
        "local_enstrophy_danger_shell_dissipation_closed": values.get(
            "localEnstrophyDangerShellDissipationClosed"
        ),
        "time_integrated_to_pointwise_conversion_closed": values.get(
            "timeIntegratedToPointwiseConversionClosed"
        ),
        "independent_epsilon_coefficient_closed": values.get(
            "independentEpsilonCoefficientClosed"
        ),
        "no_self_use_of_absorption_closed": values.get("noSelfUseOfAbsorptionClosed"),
        "pointwise_h1_tail_with_independent_epsilon_coefficient_closed": values.get(
            "pointwiseH1TailWithIndependentEpsilonCoefficientClosed"
        ),
        "clay_navier_stokes_promoted": values.get("clayNavierStokesPromoted"),
        "expected_gates": {gate_name: expected for _, gate_name, _, expected, _ in GATE_SPECS},
        "gate_results": gates,
        "source_results": sources,
        "open_obligations": [
            "materialize the Sprint 89 NS pointwise H1-tail candidate mechanism receipt if missing",
            "record the Sprint 88 H1-tail decision boundary",
            "derive local enstrophy danger-shell dissipation non-circularly",
            "derive time-integrated to pointwise localization non-circularly",
            "derive an independent epsilon<1 coefficient",
            "keep pointwiseH1TailWithIndependentEpsilonCoefficientClosed false until both inputs close",
            "keep clayNavierStokesPromoted false",
        ],
    }
    return summary, sources, gates


def markdown(summary: dict[str, Any], sources: list[dict[str, Any]], gates: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 89 Pointwise H1-Tail Mechanism Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Receipt: `{summary['receipt_path']}`",
        f"- Anchors present: `{summary['all_required_receipt_anchors_present']}`",
        f"- Forbidden term count: `{summary['forbidden_term_count']}`",
        f"- Pointwise H1 tail with independent epsilon closed: "
        f"`{summary['pointwise_h1_tail_with_independent_epsilon_coefficient_closed']}`",
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
    write_csv(args.out_dir / SOURCE_TABLE, sources)
    write_csv(args.out_dir / GATE_TABLE, gates)
    (args.out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (args.out_dir / REPORT_NAME).write_text(markdown(summary, sources, gates), encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
