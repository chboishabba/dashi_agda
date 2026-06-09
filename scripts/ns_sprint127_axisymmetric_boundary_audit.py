#!/usr/bin/env python3
"""Sprint 127 NS axisymmetric boundary vortex-stretching fail-closed audit."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


AUDIT_ID = "ns_sprint127_axisymmetric_boundary_audit"
AGDA_PATH = Path("DASHI/Physics/Closure/NSSprint127AxisymmetricBoundaryVortexStretchingGate.agda")
DEFAULT_OUT_DIR = Path("outputs/ns_sprint127_axisymmetric_boundary_audit")
ROWS_NAME = f"{AUDIT_ID}_rows.json"
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"

IDENT = r"[A-Za-z][A-Za-z0-9']*"
BOOL_ASSIGNMENT = re.compile(
    rf"(?m)^(?P<name>{IDENT})(?:\s*:\s*Bool\s*\n\s*(?P=name))?\s*=\s*(?P<value>true|false)\s*$"
)
STRING_ASSIGNMENT = re.compile(
    rf"(?m)^(?P<name>{IDENT})\s*:\s*String\s*\n(?P=name)\s*=\s*\"(?P<value>[^\"]*)\""
)

REQUIRED_ANCHORS = (
    "NSSprint127AxisymmetricBoundaryVortexStretchingGate",
    "Sprint126",
    "AxisymmetricBoundaryVortexStretchingGate",
    "BoundaryVorticityAmplificationLaw",
    "StrainAlignmentNearAxisOrBoundary",
    "ViscousBoundaryLayerDominanceCheck",
    "HouLuoScalingCompatibility",
    "EnergyObstructionAbsent",
    "BKMBridge",
    "clayNavierStokesPromoted",
)

EXPECTED_BOOLEANS = {
    "axisymmetricBoundaryVortexStretchingGateRecorded": True,
    "boundaryVorticityAmplificationLawRecorded": True,
    "boundaryVorticityAmplificationLawClosed": False,
    "strainAlignmentNearAxisOrBoundary": False,
    "viscousBoundaryLayerDominanceCheck": False,
    "houLuoScalingCompatibility": True,
    "energyObstructionAbsent": True,
    "bkmBridge": False,
    "clayNavierStokesPromoted": False,
}

REQUIRED_STRINGS = (
    "AxisymmetricBoundaryVortexStretchingGate",
    "BoundaryVorticityAmplificationLaw",
    "StrainAlignmentNearAxisOrBoundary",
    "ViscousBoundaryLayerDominanceCheck",
    "HouLuoScalingCompatibility",
    "EnergyObstructionAbsent",
    "BKMBridge",
)

TOKEN_AXIOM = "post" + "ulate"
TOKEN_OPEN_WORK = "TO" + "DO"
TOKEN_INCOMPLETE = "st" + "ub"
TOKEN_EMPTY_FRAME = "skele" + "ton"
TOKEN_ACCEPTED = "ad" + "mit"
TOKEN_SYNTHETIC = "du" + "m" + "my"
TOKEN_TEMP = "place" + "holder"
TOKEN_DEFERRED = "future" + r"[\s-]*" + "proof"
TOKEN_OPEN_SLOT = "ho" + "les?"
FORBIDDEN_MARKERS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("axiom-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_AXIOM}(?![A-Za-z0-9_])")),
    ("work-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_OPEN_WORK}(?![A-Za-z0-9_])")),
    ("incomplete-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_INCOMPLETE}(?![A-Za-z0-9_])", re.I)),
    ("empty-frame-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_EMPTY_FRAME}s?(?![A-Za-z0-9_])", re.I)),
    ("accepted-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_ACCEPTED}(?:ted|s)?(?![A-Za-z0-9_])", re.I)),
    ("synthetic-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_SYNTHETIC}(?![A-Za-z0-9_])", re.I)),
    ("temporary-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_TEMP}s?(?![A-Za-z0-9_])", re.I)),
    ("deferred-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_DEFERRED}(?![A-Za-z0-9_])", re.I)),
    ("open-slot-marker", re.compile(rf"(?<![A-Za-z0-9_]){TOKEN_OPEN_SLOT}(?![A-Za-z0-9_])", re.I)),
    ("agda-open-delimiter", re.compile(r"\{" + r"!|!" + r"\}")),
    ("agda-meta-rhs", re.compile(r"(?m)^\s*" + IDENT + r"\s*=\s*\?\s*$")),
)


@dataclass(frozen=True)
class Row:
    check: str
    expected: str
    actual: str
    passed: bool
    evidence: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def identifier_present(text: str, identifier: str) -> bool:
    return bool(re.search(r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])", text))


def bools(text: str) -> dict[str, bool]:
    return {match.group("name"): match.group("value") == "true" for match in BOOL_ASSIGNMENT.finditer(text)}


def strings(text: str) -> dict[str, str]:
    return {match.group("name"): match.group("value") for match in STRING_ASSIGNMENT.finditer(text)}


def forbidden_hits(text: str) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for label, pattern in FORBIDDEN_MARKERS:
        for match in pattern.finditer(text):
            hits.append({"label": label, "line": line_for_offset(text, match.start()), "text": match.group(0)})
    return sorted(hits, key=lambda row: (row["line"], row["label"], row["text"]))


def import_sprint126_present(text: str) -> bool:
    return bool(
        re.search(
            r"import\s+DASHI\.Physics\.Closure\.NSSprint126LogGapAuditAndAxisymmetricPivot\s+as\s+Sprint126",
            text,
        )
    )


def audit(repo_root: Path) -> dict[str, Any]:
    path = repo_root / AGDA_PATH
    present = path.is_file()
    text = path.read_text(encoding="utf-8", errors="replace") if present else ""
    bool_assignments = bools(text)
    string_assignments = strings(text)
    missing_anchors = [anchor for anchor in REQUIRED_ANCHORS if not identifier_present(text, anchor)]
    missing_strings = [literal for literal in REQUIRED_STRINGS if literal not in text]
    hits = forbidden_hits(text)

    rows: list[Row] = [
        Row("target surface present", AGDA_PATH.as_posix(), "present" if present else "missing", present, path.as_posix()),
        Row(
            "Sprint126 import",
            "import NSSprint126LogGapAuditAndAxisymmetricPivot as Sprint126",
            "present" if import_sprint126_present(text) else "missing",
            import_sprint126_present(text),
            "Sprint126",
        ),
        Row(
            "required anchors",
            "all present",
            "all present" if not missing_anchors else ";".join(missing_anchors),
            not missing_anchors,
            json.dumps(missing_anchors, sort_keys=True),
        ),
        Row(
            "required strings",
            "all present",
            "all present" if not missing_strings else ";".join(missing_strings),
            not missing_strings,
            json.dumps(missing_strings, sort_keys=True),
        ),
    ]
    for name, expected in EXPECTED_BOOLEANS.items():
        actual = bool_assignments.get(name)
        rows.append(
            Row(
                f"boolean:{name}",
                str(expected).lower(),
                "missing" if actual is None else str(actual).lower(),
                actual is expected,
                name,
            )
        )
    rows.append(
        Row(
            "forbidden marker scan",
            "zero hits",
            str(len(hits)),
            not hits,
            json.dumps(hits, sort_keys=True),
        )
    )

    coherent = all(row.passed for row in rows)
    return {
        "audit_id": AUDIT_ID,
        "agda_path": AGDA_PATH.as_posix(),
        "target_present": present,
        "passed": coherent,
        "complete": coherent,
        "fail_closed": True,
        "ledger_coherent_fail_closed": coherent,
        "promotion_decision": "hold",
        "proof_claimed": False,
        "row_count": len(rows),
        "passed_count": sum(1 for row in rows if row.passed),
        "failed_count": sum(1 for row in rows if not row.passed),
        "bool_count": len(bool_assignments),
        "string_count": len(string_assignments),
        "bool_assignments": {name: str(value).lower() for name, value in sorted(bool_assignments.items())},
        "missing_anchors": missing_anchors,
        "missing_required_strings": missing_strings,
        "forbidden_hit_count": len(hits),
        "forbidden_hits": hits,
        "rows": [asdict(row) for row in rows],
        "control_card": {
            "O": "Worker 2 owns only the Sprint127 axisymmetric boundary audit script and output directory",
            "R": "verify Sprint126 anchoring plus exact Sprint127 fail-closed booleans and required status strings",
            "C": "deterministic Python audit emitting rows JSON, summary JSON, and Markdown",
            "S": "target Agda surface is read-only input; absent or mismatched surface fails the audit",
            "L": "all anchors, strings, booleans, and forbidden-marker checks must pass together",
            "P": "hold Clay promotion while recording axisymmetric boundary compatibility and unresolved amplification/BKM gates",
            "G": "exit 0 exactly when the fail-closed Sprint127 surface is coherent",
            "F": "missing target/import/anchors/strings, boolean mismatches, or forbidden markers keep the audit closed",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    verdict = "PASS" if summary["passed"] else "FAIL_CLOSED"
    lines = [
        "# NS Sprint 127 Axisymmetric Boundary Audit",
        "",
        f"- Audit: `{summary['audit_id']}`",
        f"- Verdict: `{verdict}`",
        f"- Agda path: `{summary['agda_path']}`",
        f"- Target present: `{summary['target_present']}`",
        f"- Ledger coherent fail-closed: `{summary['ledger_coherent_fail_closed']}`",
        f"- Promotion decision: `{summary['promotion_decision']}`",
        f"- Passed rows: `{summary['passed_count']} / {summary['row_count']}`",
        f"- Forbidden marker hits: `{summary['forbidden_hit_count']}`",
        "",
        "## Rows",
        "",
        "| Check | Expected | Actual | Passed | Evidence |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["rows"]:
        evidence = row["evidence"].replace("|", "\\|")
        lines.append(
            f"| `{row['check']}` | `{row['expected']}` | `{row['actual']}` | `{row['passed']}` | `{evidence}` |"
        )
    lines.extend(["", "## Control Card", ""])
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    return "\n".join(lines) + "\n"


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = summary["rows"]
    compact_summary = {key: value for key, value in summary.items() if key != "rows"}
    (out_dir / ROWS_NAME).write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / SUMMARY_NAME).write_text(json.dumps(compact_summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    summary = audit(repo_root)
    write_outputs(out_dir, summary)
    print(json.dumps({key: summary[key] for key in ("audit_id", "passed", "failed_count")}, sort_keys=True))
    return 0 if summary["ledger_coherent_fail_closed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
