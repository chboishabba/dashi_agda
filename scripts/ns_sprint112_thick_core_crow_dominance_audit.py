#!/usr/bin/env python3
"""Sprint 112 NS thick-core Crow dominance fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint112_thick_core_crow_dominance_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint112_thick_core_crow_dominance_audit")
SUMMARY_NAME = "ns_sprint112_thick_core_crow_dominance_audit_summary.json"
ROWS_NAME = "ns_sprint112_thick_core_crow_dominance_audit_rows.json"
REPORT_NAME = "ns_sprint112_thick_core_crow_dominance_audit.md"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint112ThickCoreCrowDominanceRegime.agda")
ROUTE_DECISION = "THICK_CORE_CROW_DOMINANCE_REGIME_CLOSED_FAIL_CLOSED_NO_PROMOTION"

REQUIRED_ANCHORS = [
    "NSSprint112ThickCoreCrowDominance",
    "NSSprint112ThickCoreCrowDominanceRegime",
    "canonicalNSSprint112ThickCoreCrowDominance",
    "canonicalNSSprint112ThickCoreCrowDominanceRegime",
    "nsSprint112ThickCoreCrowDominanceReceipt",
    "nsSprint112ThickCoreCrowDominanceRegimeReceipt",
    "canonicalSprint112ThickCoreCrowDominanceFlags",
    "canonicalThickCoreCrowDominanceFlags",
    "thickCoreCrowDominanceRegimeClosed",
]

REQUIRED_STRINGS = [
    "Crow",
    "elliptic",
    "rate",
    "rates",
    "delta/b >= 1/2",
]

EXPECTED_BOOLEANS = {
    "thickCoreCrowDominanceRegimeClosed": True,
    "downstreamNavierStokesClosed": False,
    "downstreamNSPromotion": False,
    "downstreamPromotion": False,
    "navierStokesPromotion": False,
    "clayNavierStokesPromoted": False,
}

TOKEN_UNPROVED = "post" + "ulate"
TOKEN_OPEN_WORK = "TO" + "DO"
TOKEN_INCOMPLETE = "st" + "ub"
TOKEN_EMPTY_FRAME = "skele" + "ton"
TOKEN_ACCEPT_WITHOUT_PROOF = "ad" + "mit"
TOKEN_DUMMY = "dum" + "my"
TOKEN_FUTURE_PROOF = "future" + r"[\s-]*" + "proof"
TOKEN_HOLE = "ho" + "le"
FORBIDDEN_PATTERNS = {
    "unproved_axiom_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_UNPROVED + r"(?![A-Za-z0-9_])"),
    "open_work_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_OPEN_WORK + r"(?![A-Za-z0-9_])"),
    "incomplete_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_INCOMPLETE + r"(?![A-Za-z0-9_])", re.I),
    "empty_framework_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_EMPTY_FRAME + r"s?(?![A-Za-z0-9_])", re.I),
    "accepted_without_proof_marker": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_ACCEPT_WITHOUT_PROOF + r"(?:ted|s)?(?![A-Za-z0-9_])", re.I),
    "synthetic_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])", re.I),
    "deferred_proof_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])", re.I),
    "gap_wording": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_HOLE + r"s?(?![A-Za-z0-9_])", re.I),
    "open_gap_delimiter": re.compile(r"\{" + r"!|!" + r"\}"),
    "open_gap_assignment": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}


@dataclass(frozen=True)
class GateRow:
    gate: str
    expected: str
    actual: str
    passed: bool
    status: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def identifier_present(text: str, identifier: str) -> bool:
    return bool(re.search(r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])", text))


def literal_present(text: str, literal: str) -> bool:
    return literal in text


def bool_assignment(text: str, name: str, expected: bool) -> bool:
    value = "true" if expected else "false"
    return bool(
        re.search(
            r"(?<![A-Za-z0-9_])"
            + re.escape(name)
            + r"(?![A-Za-z0-9_])(?:\s*:\s*[^\n=]+)?\s*=\s*"
            + value
            + r"(?![A-Za-z0-9_])",
            text,
            re.MULTILINE,
        )
    )


def actual_bool_assignment(text: str, name: str) -> str:
    if bool_assignment(text, name, True):
        return "true"
    if bool_assignment(text, name, False):
        return "false"
    return "missing"


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def audit(repo_root: Path) -> dict[str, Any]:
    path = repo_root / AGDA_PATH
    present = path.exists()
    text = path.read_text(encoding="utf-8", errors="replace") if present else ""
    missing_anchors = [anchor for anchor in REQUIRED_ANCHORS if not identifier_present(text, anchor)]
    missing_required_strings = [literal for literal in REQUIRED_STRINGS if not literal_present(text, literal)]
    bool_checks = {
        name: {
            "expected": expected,
            "actual": actual_bool_assignment(text, name) if present else "missing",
            "passed": bool_assignment(text, name, expected) if present else False,
        }
        for name, expected in EXPECTED_BOOLEANS.items()
    }
    forbidden_hits = [
        {"label": label, "line": line_for_offset(text, match.start()), "match": match.group(0)}
        for label, pattern in FORBIDDEN_PATTERNS.items()
        for match in pattern.finditer(text)
    ]
    gate_rows = [
        GateRow(
            name,
            "true" if expected else "false",
            bool_checks[name]["actual"],
            bool_checks[name]["passed"],
            "PASS" if bool_checks[name]["passed"] else "FAIL_CLOSED_BOOLEAN_GATE",
        )
        for name, expected in EXPECTED_BOOLEANS.items()
    ]
    gate_rows.extend(
        GateRow(
            f"required_string:{literal}",
            "present",
            "present" if literal not in missing_required_strings else "missing",
            literal not in missing_required_strings,
            "PASS" if literal not in missing_required_strings else "FAIL_CLOSED_MISSING_REQUIRED_STRING",
        )
        for literal in REQUIRED_STRINGS
    )
    gate_rows.extend(
        [
            GateRow(
                "target_module",
                str(AGDA_PATH),
                "present" if present else "missing",
                present,
                "PASS" if present else "FAIL_CLOSED_MISSING_TARGET",
            ),
            GateRow("route", ROUTE_DECISION, ROUTE_DECISION, True, "PASS"),
            GateRow(
                "required_anchors",
                "all present",
                "all present" if not missing_anchors else "; ".join(missing_anchors),
                not missing_anchors,
                "PASS" if not missing_anchors else "FAIL_CLOSED_MISSING_ANCHOR",
            ),
            GateRow(
                "forbidden_markers",
                "none",
                "none" if not forbidden_hits else str(len(forbidden_hits)),
                not forbidden_hits,
                "PASS" if not forbidden_hits else "FAIL_CLOSED_FORBIDDEN_MARKER",
            ),
        ]
    )
    structural_checks_pass = present and not missing_anchors and not missing_required_strings and not forbidden_hits and all(
        row.passed for row in gate_rows
    )
    return {
        "contract": CONTRACT,
        "agda_path": str(AGDA_PATH),
        "target_present": present,
        "complete": structural_checks_pass,
        "proof_claimed": False,
        "fail_closed": not structural_checks_pass,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION if structural_checks_pass else "FAIL_CLOSED_AUDIT_BLOCKED",
        "promotion_decision": "hold",
        "promotion_hold": True,
        "evidence_audit_passed": structural_checks_pass,
        "thick_core_crow_dominance_regime_closed": bool_checks["thickCoreCrowDominanceRegimeClosed"]["passed"],
        "downstream_flags_false": all(
            bool_checks[name]["passed"]
            for name in EXPECTED_BOOLEANS
            if "downstream" in name.lower()
        ),
        "promotion_flags_false": all(
            bool_checks[name]["passed"]
            for name in EXPECTED_BOOLEANS
            if "promotion" in name.lower() or "promoted" in name.lower()
        ),
        "clay_navier_stokes_promoted": False,
        "clay": False,
        "required_anchors": REQUIRED_ANCHORS,
        "missing_anchors": missing_anchors,
        "required_strings": REQUIRED_STRINGS,
        "missing_required_strings": missing_required_strings,
        "bool_checks": bool_checks,
        "forbidden_hits": forbidden_hits,
        "forbidden_marker_count": len(forbidden_hits),
        "gate_results": [asdict(row) for row in gate_rows],
        "control_card": {
            "O": "Worker 2 owns the Sprint112 thick-core Crow dominance audit script only",
            "R": "verify thickCoreCrowDominanceRegimeClosed true, downstream and promotion flags false, Crow/elliptic rate strings, delta/b >= 1/2, and forbidden-marker absence",
            "C": "single deterministic Python audit emitting summary JSON, rows JSON, and Markdown",
            "S": "target Agda module is inspected when present; missing target fails closed",
            "L": "all required anchors, literals, and booleans must match before the audit exits successfully",
            "P": ROUTE_DECISION,
            "G": "Downstream Navier-Stokes and Clay promotion remain false",
            "F": "missing target, anchors, required strings, exact booleans, or forbidden-marker hits block audit passage",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 112 Thick-Core Crow Dominance Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Agda path: `{summary['agda_path']}`",
        f"- Target present: `{summary['target_present']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Evidence audit passed: `{summary['evidence_audit_passed']}`",
        f"- Thick-core Crow dominance regime closed: `{summary['thick_core_crow_dominance_regime_closed']}`",
        f"- Downstream flags false: `{summary['downstream_flags_false']}`",
        f"- Promotion flags false: `{summary['promotion_flags_false']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Required Strings",
        "",
        "| String | Present |",
        "| --- | --- |",
    ]
    lines.extend(
        f"| `{literal}` | `{literal not in summary['missing_required_strings']}` |"
        for literal in summary["required_strings"]
    )
    lines.extend(["", "## Gate Results", "", "| Gate | Expected | Actual | Passed | Status |", "| --- | --- | --- | --- | --- |"])
    lines.extend(
        f"| `{row['gate']}` | `{row['expected']}` | `{row['actual']}` | `{row['passed']}` | `{row['status']}` |"
        for row in summary["gate_results"]
    )
    return "\n".join(lines) + "\n"


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / ROWS_NAME).write_text(json.dumps(summary["gate_results"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = audit(args.repo_root.resolve())
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["evidence_audit_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
