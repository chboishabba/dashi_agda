#!/usr/bin/env python3
"""Fail-closed audit for the YM-A finite Hamiltonian domination candidate."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_finite_domination_candidate_audit"
DEFAULT_OUT_DIR = Path("outputs/ym_finite_domination_candidate_audit")
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"
FAIL_CLOSED = "fail-closed"
META_CHAR = chr(63)

SOURCE_PATTERNS: tuple[str, ...] = (
    "DASHI/Physics/Closure/YMBochnerWeitzenbockHamiltonianDominationBoundary.agda",
    "DASHI/Physics/Closure/YMHamiltonianDominatesFiniteHodgeDefectBoundary.agda",
    "DASHI/Physics/Closure/YMHamiltonianDominationErrorBudgetBoundary.agda",
    "DASHI/Physics/Closure/YMKillingBoundary*Boundary.agda",
    "DASHI/Physics/Closure/YMGaugeZeroModeVacuumRigidityBoundary.agda",
    "DASHI/Physics/Closure/YMLatticeMassGapAuthority.agda",
    "DASHI/Physics/Closure/YMClayUpdatedBlockerReceipt.agda",
    "DASHI/Physics/Closure/*Wilson*.agda",
    "DASHI/Physics/Closure/*Holonomy*.agda",
    "DASHI/Physics/Closure/*Balaban*.agda",
    "DASHI/Physics/Closure/*H3*.agda",
)

BOOL_PATTERN = re.compile(r"^([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$", re.MULTILINE)
STRING_PATTERN = re.compile(
    r"^([A-Za-z][A-Za-z0-9']*)\s*:\s*String\s*\n"
    r"\1\s*=\s*(?:\n\s*)?\"([^\"]*)\"",
    re.MULTILINE,
)
DATA_HEADER_PATTERN = re.compile(r"^\s*data\s+\S+.*\bwhere\s*$")
TRUE_PROMOTION_PATTERN = re.compile(
    r"(?m)^\s*(?:clayYangMillsPromoted|yangMillsPromoted|continuumMassGapPromoted|terminalClayClaimPromoted)\s*=\s*true\s*$"
)
MARKER_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("unimplemented-declaration", re.compile(r"\bpost" + r"ulate\b")),
    ("open-work-token", re.compile(r"\bTO" + r"DO\b")),
    ("placeholder-token", re.compile(r"\bst" + r"ub\b", re.IGNORECASE)),
    ("agda-incomplete-braces", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-meta-character", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*" + re.escape(META_CHAR) + r"\s*$")),
    ("type-meta-character", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*:\s*" + re.escape(META_CHAR) + r"\s*$")),
)

EVIDENCE_QUERIES: dict[str, tuple[str, ...]] = {
    "bochner_weitzenbock": ("bochner", "weitzenbock", "hamiltonian", "domination", "delta", "c1"),
    "small_field_c1": ("small-field", "small field", "gamma", "epsilon", "c1", "error", "absorption"),
    "large_field_c2": ("large-field", "large field", "wilson", "holonomy", "c2", "positive"),
    "killing_boundary": ("killing", "boundary", "self-adjoint", "selfadjoint", "domain", "green"),
    "gauge_quotient": ("gauge", "quotient", "omega", "zero-mode", "zeromode", "projection"),
    "h3a_balaban": ("h3a", "balaban", "continuum", "no-spectral-pollution", "authority"),
    "promotion_guard": ("clay", "promotion", "promoted", "terminal", "false"),
}

CONSTANT_FORMULA_METADATA: dict[str, dict[str, Any]] = {
    "small_field_c1": {
        "code": "BW-SF-c1",
        "sector": "Bochner-Weitzenbock small-field sector",
        "coefficient": "c1",
        "formula": "c1 = gamma_d / 2 - C * epsilon",
        "strict_positivity_condition": "gamma_d / 2 - C * epsilon > 0",
        "equivalent_parameter_condition": "gamma_d > 2 * C * epsilon",
        "required_parameters": ["gamma_d", "C", "epsilon"],
        "normalization": {
            "gamma_d": "finite covariant Laplacian / spectral seed lower bound",
            "C": "finite domination error-budget constant",
            "epsilon": "small-field radius or perturbative field-size parameter",
        },
        "status": "blocked",
        "closed": False,
        "fail_closed_reason": "No audited source supplies explicit uniform constants proving gamma_d > 2*C*epsilon.",
    },
    "large_field_c2": {
        "code": "BW-LF-c2",
        "sector": "large-field Wilson/holonomy sector",
        "coefficient": "c2",
        "formula": "c2 = large_field_Wilson_holonomy_positive_margin",
        "strict_positivity_condition": "c2 > 0",
        "required_parameters": [
            "Wilson large-field action lower bound",
            "holonomy/topological cost lower bound",
            "uniform leakage/error subtraction",
        ],
        "status": "blocked",
        "closed": False,
        "fail_closed_reason": "The audit records the positivity obligation only; it does not promote a Wilson/holonomy lower-bound theorem.",
    },
}

REQUIRED_BLOCKERS: tuple[dict[str, Any], ...] = (
    {
        "code": "BW-SF-c1",
        "label": "small-field Bochner-Weitzenbock coefficient",
        "required": True,
        "blocked": True,
        "description": "Prove c1 = gamma_d/2 - C*epsilon > 0 with explicit uniform gamma_d, C, and epsilon.",
    },
    {
        "code": "BW-LF-c2",
        "label": "large-field Wilson/holonomy coefficient",
        "required": True,
        "blocked": True,
        "description": "Prove c2 > 0 from Wilson large-field action and holonomy/topological cost after leakage subtraction.",
    },
    {
        "code": "KB-GQ-DOMAIN",
        "label": "Killing-boundary and gauge-quotient domain obligations",
        "required": True,
        "blocked": True,
        "description": "Discharge self-adjoint Killing-boundary domain preservation, quotient descent, and gauge-invariant projection obligations.",
    },
    {
        "code": "GQ-ZERO-MODE",
        "label": "gauge zero-mode exclusion",
        "required": True,
        "blocked": True,
        "description": "Show quotienting removes gauge zero modes without creating new zero-energy modes or boundary leakage.",
    },
    {
        "code": "H3A-BALABAN-SEPARATION",
        "label": "downstream H3a/Balaban separation",
        "required": True,
        "blocked": True,
        "description": "Keep the finite domination candidate separated from H3a, Balaban, continuum transfer, no-spectral-pollution, OS/Wightman, and Clay gates.",
    },
)

FALSE_PROMOTION_FLAGS: dict[str, bool] = {
    "candidateAFiniteHamiltonianDominationPromoted": False,
    "yangMillsPromoted": False,
    "clayYangMillsPromoted": False,
    "continuumMassGapPromoted": False,
    "h3aBalabanPromoted": False,
    "terminalClayClaimPromoted": False,
}


@dataclass(frozen=True)
class SourceSurface:
    path: Path
    rel_path: str
    text: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    parser.add_argument("--markdown", action=argparse.BooleanOptionalAction, default=True)
    return parser.parse_args()


def normalize(value: str) -> str:
    return re.sub(r"[^a-z0-9]", "", value.lower())


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def read_surfaces(repo_root: Path) -> list[SourceSurface]:
    seen: set[Path] = set()
    surfaces: list[SourceSurface] = []
    for pattern in SOURCE_PATTERNS:
        for path in sorted(repo_root.glob(pattern)):
            if path in seen or not path.is_file():
                continue
            seen.add(path)
            surfaces.append(
                SourceSurface(
                    path=path,
                    rel_path=path.relative_to(repo_root).as_posix(),
                    text=path.read_text(encoding="utf-8"),
                )
            )
    return surfaces


def bool_assignments(text: str) -> dict[str, bool]:
    return {name: value == "true" for name, value in BOOL_PATTERN.findall(text)}


def string_assignments(text: str) -> dict[str, str]:
    return dict(STRING_PATTERN.findall(text))


def marker_hits(text: str) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for marker, pattern in MARKER_PATTERNS:
        for match in pattern.finditer(text):
            hits.append({"marker": marker, "line": line_number(text, match.start())})
    return hits


def empty_data_declarations(text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    lines = text.splitlines()
    for index, line in enumerate(lines):
        if not DATA_HEADER_PATTERN.match(line):
            continue
        saw_constructor = False
        for following in lines[index + 1 :]:
            stripped = following.strip()
            if not stripped or stripped.startswith("--"):
                continue
            if not following.startswith((" ", "\t")):
                break
            saw_constructor = True
            break
        if not saw_constructor:
            rows.append({"line": index + 1, "text": line.strip()})
    return rows


def source_lines(text: str, needles: Iterable[str], limit: int = 10) -> list[dict[str, Any]]:
    normalized_needles = tuple(normalize(needle) for needle in needles)
    rows: list[dict[str, Any]] = []
    for index, line in enumerate(text.splitlines(), start=1):
        normalized_line = normalize(line)
        if any(needle and needle in normalized_line for needle in normalized_needles):
            rows.append({"line": index, "text": line.strip()})
            if len(rows) >= limit:
                break
    return rows


def selected_bools(bools: dict[str, bool], needles: Iterable[str]) -> dict[str, bool]:
    normalized_needles = tuple(normalize(needle) for needle in needles)
    return {
        name: value
        for name, value in bools.items()
        if any(needle and needle in normalize(name) for needle in normalized_needles)
    }


def selected_strings(strings: dict[str, str], needles: Iterable[str]) -> dict[str, str]:
    normalized_needles = tuple(normalize(needle) for needle in needles)
    return {
        name: value
        for name, value in strings.items()
        if any(needle and needle in normalize(f"{name} {value}") for needle in normalized_needles)
    }


def scan_surface(surface: SourceSurface) -> dict[str, Any]:
    bools = bool_assignments(surface.text)
    strings = string_assignments(surface.text)
    evidence = {
        key: {
            "line_evidence": source_lines(surface.text, needles),
            "bool_assignments": selected_bools(bools, needles),
            "string_assignments": selected_strings(strings, needles),
        }
        for key, needles in EVIDENCE_QUERIES.items()
    }
    return {
        "path": surface.rel_path,
        "bool_assignments": bools,
        "string_assignments": strings,
        "true_promotion_assignment_detected": bool(TRUE_PROMOTION_PATTERN.search(surface.text)),
        "marker_hits": marker_hits(surface.text),
        "empty_data_declarations": empty_data_declarations(surface.text),
        "evidence": evidence,
    }


def evidence_bucket(scans: list[dict[str, Any]], key: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for scan in scans:
        evidence = scan["evidence"][key]
        if evidence["line_evidence"] or evidence["bool_assignments"] or evidence["string_assignments"]:
            rows.append(
                {
                    "path": scan["path"],
                    "line_evidence": evidence["line_evidence"],
                    "bool_assignments": evidence["bool_assignments"],
                    "string_assignments": evidence["string_assignments"],
                }
            )
    return rows


def build_summary(repo_root: Path) -> dict[str, Any]:
    surfaces = read_surfaces(repo_root)
    scans = [scan_surface(surface) for surface in surfaces]

    hard_fail_reasons: list[str] = []
    if not scans:
        hard_fail_reasons.append("No YM finite-domination source surfaces were discovered.")
    for scan in scans:
        if scan["true_promotion_assignment_detected"]:
            hard_fail_reasons.append(f"{scan['path']}: forbidden true promotion assignment detected")
        if scan["marker_hits"]:
            markers = ", ".join(f"{hit['marker']}@L{hit['line']}" for hit in scan["marker_hits"][:12])
            hard_fail_reasons.append(f"{scan['path']}: incomplete marker detected ({markers})")
        if scan["empty_data_declarations"]:
            lines = ", ".join(f"L{row['line']}" for row in scan["empty_data_declarations"][:12])
            hard_fail_reasons.append(f"{scan['path']}: empty data declaration detected ({lines})")

    route_reasons = [
        blocker["description"]
        for blocker in REQUIRED_BLOCKERS
        if blocker["blocked"]
    ]
    blockers_closed = all(not blocker["blocked"] for blocker in REQUIRED_BLOCKERS)
    promotion_guard_closed = not any(FALSE_PROMOTION_FLAGS.values()) and not any(
        scan["true_promotion_assignment_detected"] for scan in scans
    )

    return {
        "audit_id": AUDIT_ID,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "route_decision": FAIL_CLOSED,
        "route_closed": False,
        "hard_fail_reasons": hard_fail_reasons,
        "route_reasons": route_reasons,
        "fail_reasons": hard_fail_reasons + route_reasons,
        "scope": {
            "candidate": "YM-A finite Hamiltonian domination candidate",
            "inequality": "H_d | Omega^perp >= c1 Delta_YM,d + c2 Hol_d - E_d",
            "source_patterns": list(SOURCE_PATTERNS),
            "scanned_surface_count": len(scans),
            "scanned_surfaces": [scan["path"] for scan in scans],
        },
        "constant_formula_metadata": CONSTANT_FORMULA_METADATA,
        "small_field_bochner_weitzenbock_condition": CONSTANT_FORMULA_METADATA["small_field_c1"],
        "large_field_wilson_holonomy_condition": CONSTANT_FORMULA_METADATA["large_field_c2"],
        "required_blockers": list(REQUIRED_BLOCKERS),
        "blockers_closed": blockers_closed,
        "killing_boundary_gauge_quotient_obligations": [
            blocker
            for blocker in REQUIRED_BLOCKERS
            if blocker["code"] in {"KB-GQ-DOMAIN", "GQ-ZERO-MODE"}
        ],
        "downstream_separation": {
            "code": "H3A-BALABAN-SEPARATION",
            "closed": False,
            "separated_from": [
                "H3a",
                "Balaban",
                "continuum transfer",
                "no-spectral-pollution",
                "OS/Wightman",
                "Clay Yang-Mills",
            ],
            "claim": "finite domination evidence is diagnostic and does not discharge downstream H3a/Balaban obligations",
        },
        "promotion_flags": FALSE_PROMOTION_FLAGS,
        "promotion_guard": {
            "closed": promotion_guard_closed,
            "never_claim_clay_or_ym_promotion": True,
            "false_flags": FALSE_PROMOTION_FLAGS,
            "true_promotion_assignments": [
                scan["path"] for scan in scans if scan["true_promotion_assignment_detected"]
            ],
        },
        "evidence": {
            key: evidence_bucket(scans, key)
            for key in EVIDENCE_QUERIES
        },
        "fail_closed_scan": scans,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# YM Finite Domination Candidate Audit",
        "",
        f"Route decision: `{summary['route_decision']}`",
        f"Route closed: `{str(summary['route_closed']).lower()}`",
        "",
        "## Constants",
        "",
    ]
    for item in summary["constant_formula_metadata"].values():
        lines.extend(
            [
                f"### {item['code']}",
                "",
                f"- Formula: `{item['formula']}`",
                f"- Positivity: `{item['strict_positivity_condition']}`",
                f"- Closed: `{str(item['closed']).lower()}`",
                f"- Reason: {item['fail_closed_reason']}",
                "",
            ]
        )
    lines.extend(["## Required Blockers", ""])
    for blocker in summary["required_blockers"]:
        lines.append(f"- `{blocker['code']}` blocked=`{str(blocker['blocked']).lower()}`: {blocker['description']}")
    lines.extend(["", "## Promotion Guard", ""])
    for name, value in summary["promotion_flags"].items():
        lines.append(f"- `{name}`: `{str(value).lower()}`")
    lines.extend(["", "## Evidence Buckets", ""])
    for key, rows in summary["evidence"].items():
        lines.append(f"- `{key}`: {len(rows)} source surface(s)")
    lines.extend(["", "## Fail-Closed Reasons", ""])
    for reason in summary["fail_reasons"]:
        lines.append(f"- {reason}")
    return "\n".join(lines)


def write_outputs(summary: dict[str, Any], out_dir: Path, markdown: bool) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if markdown:
        (out_dir / REPORT_NAME).write_text(render_markdown(summary) + "\n", encoding="utf-8")


def main() -> None:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    summary = build_summary(repo_root)
    write_outputs(summary, out_dir, args.markdown)
    print(f"wrote {out_dir / SUMMARY_NAME}")
    if args.markdown:
        print(f"wrote {out_dir / REPORT_NAME}")
    print(f"route_decision={summary['route_decision']}")
    for reason in summary["fail_reasons"]:
        print(f"{FAIL_CLOSED}: {reason}")
    if summary["hard_fail_reasons"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
