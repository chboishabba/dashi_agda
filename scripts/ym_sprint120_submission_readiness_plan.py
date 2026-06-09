#!/usr/bin/env python3
"""Generate a concrete Sprint-120 submission readiness roadmap.

The output is a purely structural artifact: it records the 18 current Clay-facing
obligations, categories (hard/medium/easy), dependency edges, and a feasible
round schedule for up to six parallel workers per round. The schedule is
computed from declared dependencies, not from unstated optimism.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_OUT_DIR = Path("outputs/ym_sprint120_submission_readiness")
SUMMARY_NAME = "ym_sprint120_submission_readiness_summary.json"
PLAN_NAME = "ym_sprint120_submission_readiness_plan.md"
CERT_SUMMARY = Path("outputs/ym_sprint120_certificate_audit/ym_sprint120_certificate_audit_summary.json")


@dataclass(frozen=True)
class Obligation:
    obligation_id: str
    name: str
    category: str
    depends_on: tuple[str, ...]
    blocked_by: tuple[str, ...]
    evidence_link: str


OBLIGATIONS: tuple[Obligation, ...] = (
    Obligation(
        "CC1",
        "ExternalCommonCarrierConstruction",
        "hard",
        (),
        (
            "externalCommonCarrierConstructionTheoremProvedHere",
            "commonCarrierConstructionTheoremProvedHere",
            "externalCommonCarrierConstructionClosedHere",
            "commonCarrierFeedThroughClosedHere",
        ),
        "YMSprint120ExternalCommonCarrierConstructionCertificate.agda",
    ),
    Obligation(
        "WC1",
        "WeakCompactnessExtraction",
        "hard",
        ("CC1",),
        ("weakCompactnessCertificateClosedHere", "weakCompactnessClosedHere"),
        "YMSprint120WeakCompactnessCertificateInterface.agda",
    ),
    Obligation(
        "MC1",
        "ClosedFormLowerSemicontinuityMoscoLiminf",
        "hard",
        ("WC1", "CC2", "CC3", "CC4"),
        ("allMoscoCompactnessObligationsClosedHere",),
        "YMSprint120MoscoAggregateClosureCertificate.agda",
    ),
    Obligation(
        "SC1",
        "LogGeneratorFunctionalCalculusClosure",
        "hard",
        ("MC1", "MC3"),
        ("transferLowerBoundTheoremProvedHere", "allTransferCalculusObligationsClosedHere"),
        "YMSprint120TransferCalculusClosureCertificate.agda",
    ),
    Obligation(
        "SC3",
        "TransferLowerBoundTheorem",
        "hard",
        ("SC1", "MC1"),
        ("transferLowerBoundTheoremProvedHere",),
        "YMSprint120TransferCalculusClosureCertificate.agda",
    ),
    Obligation("CC2", "gauge covariance of carrier maps", "medium", ("CC1",), ("externalCommonCarrierConstructionTheoremProvedHere",), "YMSprint120CommonCarrierFeedThroughClosureReducer.agda"),
    Obligation("CC3", "uniform norm window", "medium", ("CC1",), ("externalCommonCarrierConstructionTheoremProvedHere",), "YMSprint120CommonCarrierFeedThroughClosureReducer.agda"),
    Obligation(
        "CC4",
        "approximate inverse residuals vanish",
        "medium",
        ("CC1",),
        ("externalCommonCarrierConstructionTheoremProvedHere",),
        "YMSprint120CommonCarrierFeedThroughClosureReducer.agda",
    ),
    Obligation("WC2", "null sector escape exclusion", "medium", ("CC1", "WC1"), ("weakCompactnessClosedHere",), "YMSprint120WeakCompactnessCertificateInterface.agda"),
    Obligation("WC3p", "projection sector stability", "medium", ("CC1", "WC1"), ("weakCompactnessClosedHere",), "YMSprint120WeakCompactnessCertificateInterface.agda"),
    Obligation("MC2", "Mosco recovery limsup", "medium", ("MC1",), ("allMoscoCompactnessObligationsClosedHere",), "YMSprint120MoscoAggregateClosureCertificate.agda"),
    Obligation("MC3", "uniform form lower bound", "medium", ("WC1",), ("allMoscoCompactnessObligationsClosedHere",), "YMSprint120MoscoAggregateClosureCertificate.agda"),
    Obligation("MC4", "no bottom spectrum pollution", "medium", ("MC1",), ("allMoscoCompactnessObligationsClosedHere",), "YMSprint120MoscoAggregateClosureCertificate.agda"),
    Obligation("SC2", "spectral gap transport under Mosco", "medium", ("SC1",), ("transferLowerBoundTheoremProvedHere", "allTransferCalculusObligationsClosedHere"), "YMSprint120TransferCalculusClosureCertificate.agda"),
    Obligation("OS1", "full OS→Wightman", "medium", ("SC3",), ("allTransferCalculusObligationsClosedHere", "transferLowerBoundTheoremProvedHere"), "YMSprint120TransferCalculusClosureCertificate.agda"),
    Obligation("SY1", "SymmetryRestorationInContinuumLimit", "easy", ("SC3",), ("allTransferCalculusObligationsClosedHere",), "DASHI/Physics/Closure/YMSprint105SymmetryRestorationContinuumLimit.agda"),
    Obligation("GG1", "CompactSimpleGroupParameterTable", "easy", ("SC3",), (), "YMSprint104ClayCandidateDossierBuilder.agda"),
    Obligation("FIN", "Final Clay assembly", "easy", ("SY1", "GG1", "OS1"), (), "DASHI/Physics/Closure/YMSprint120ExternalCommonCarrierConstructionCertificate.agda"),
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def parse_bool_assignments(text: str) -> dict[str, bool]:
    return {
        name: value == "true"
        for name, value in re.findall(r"^([A-Za-z][A-Za-z0-9']*)\s*=\s*(true|false)\s*$", text, re.MULTILINE)
    }


def read_certificate_summary(repo_root: Path) -> dict[str, Any]:
    summary_path = repo_root / CERT_SUMMARY
    if summary_path.exists():
        try:
            return json.loads(summary_path.read_text())
        except Exception:
            pass

    theorem_flags = []
    for module in sorted((repo_root / "DASHI" / "Physics" / "Closure").glob("YMSprint120*.agda")):
        assignments = parse_bool_assignments(module.read_text())
        theorem_flags.extend({"name": name, "value": value} for name, value in assignments.items())
    flag_values = {row["name"]: row["value"] for row in theorem_flags}
    return {
        "route_decision": (
            "sprint120 certificate route proved"
            if all(
                flag_values.get(all_flag, False)
                for all_flag in (
                    "externalCommonCarrierConstructionTheoremProvedHere",
                    "weakCompactnessClosedHere",
                    "allMoscoCompactnessObligationsClosedHere",
                    "allTransferCalculusObligationsClosedHere",
                )
            )
            else "fail-closed"
        ),
        "theorem_proved_flags": theorem_flags,
    }


def make_lookup(flags: list[dict[str, Any]]) -> dict[str, bool]:
    return {entry["name"]: bool(entry.get("value", False)) for entry in flags}


def mark_status(
    flag_map: dict[str, bool], all_flags_satisfied: bool
) -> tuple[str, list[str]]:
    if all_flags_satisfied:
        return "closed", []
    open_reasons = [name for name, value in flag_map.items() if not value]
    if not open_reasons:
        open_reasons = ["not supplied as repo theorem witness"]
    return "blocked", open_reasons


def build_plan(
    obligation_records: tuple[Obligation, ...],
    closure_flags: dict[str, bool],
    route_closed: bool,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for obligation in obligation_records:
        mapped_flags = {f: closure_flags.get(f, False) for f in obligation.blocked_by}
        status, reasons = mark_status(mapped_flags, all(mapped_flags.values()) if mapped_flags else False)
        if not route_closed:
            status = "blocked"
        rows.append(
            {
                "obligation_id": obligation.obligation_id,
                "name": obligation.name,
                "category": obligation.category,
                "depends_on": list(obligation.depends_on),
                "blocked_by_flags": obligation.blocked_by,
                "blocked_by_reasons": reasons,
                "evidence_link": obligation.evidence_link,
                "status": status,
            }
        )

    dependency_graph = {row["obligation_id"]: row["depends_on"] for row in rows}
    unresolved = {row["obligation_id"] for row in rows}
    completed: set[str] = set()
    rounds: list[list[str]] = []

    while unresolved:
        eligible = [
            row["obligation_id"]
            for row in rows
            if row["obligation_id"] in unresolved and all(dep in completed for dep in dependency_graph[row["obligation_id"]])
        ]
        if not eligible:
            # Guard against mis-declared dependency cycles.
            rounds.append(sorted(unresolved))
            break
        selected = eligible[:6]
        rounds.append(selected)
        for item in selected:
            unresolved.discard(item)
            completed.add(item)

    return {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "route_decision": (
            "ready" if route_closed and all(row["status"] == "closed" for row in rows) else "fail-closed"
        ),
        "obligations": rows,
        "rounds_of_six": [
            {
                "round": idx + 1,
                "lanes": round_rows,
                "count": len(round_rows),
                "status": "full" if len(round_rows) == 6 else "partial" if round_rows else "blocked",
            }
            for idx, round_rows in enumerate(rounds)
        ],
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = ["# Sprint 120 Submission Readiness Plan", "", f"Route decision: `{summary['route_decision']}`", ""]
    lines.extend(["## Obligations (total: " + str(len(summary["obligations"])) + ")", ""])
    for row in summary["obligations"]:
        lines.append(
            f"- `{row['obligation_id']}` ({row['category']}): `{row['name']}` — `{row['status']}`"
        )
        lines.append(f"  - depends on: {', '.join(row['depends_on']) or '[]'}")
        lines.append(f"  - blocked_by: {', '.join(row['blocked_by_flags']) or '[]'}")
        if row['blocked_by_reasons']:
            lines.append(f"  - open_reasons: {', '.join(row['blocked_by_reasons'])}")
        lines.append("")

    lines.append("## Dispatch plan (up to six lanes per round)")
    for round_row in summary["rounds_of_six"]:
        lines.append(f"- round {round_row['round']} ({round_row['count']}): {', '.join(round_row['lanes'])}")
    return "\n".join(lines) + "\n"


def build_summary(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    _ = out_dir
    certificate = read_certificate_summary(repo_root)
    closure_flags = make_lookup(certificate.get("theorem_proved_flags", []))
    route_closed = certificate.get("route_decision") == "sprint120 certificate route proved"
    return build_plan(OBLIGATIONS, closure_flags, route_closed)


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    (out_dir / PLAN_NAME).write_text(render_markdown(summary))


def main() -> None:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    summary = build_summary(repo_root, out_dir)
    write_outputs(summary, out_dir)
    print(f"wrote {out_dir / SUMMARY_NAME}")
    print(f"wrote {out_dir / PLAN_NAME}")
    print(f"rounds={len(summary['rounds_of_six'])}")


if __name__ == "__main__":
    main()
