#!/usr/bin/env python3
"""Sprint 93 NS candidate-source matrix audit.

Deterministic fail-closed matrix over Sprint87-92 source surfaces.  A source is
accepted only if the same allowed source supplies dominance, pointwise H1 tail,
and an independent coefficient while avoiding the forbidden dependency classes.
"""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint93_candidate_source_matrix_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint93_candidate_source_matrix_audit")
SUMMARY_NAME = "ns_sprint93_candidate_source_matrix_audit_summary.json"
ROWS_JSON_NAME = "ns_sprint93_candidate_source_matrix_audit_rows.json"
ROWS_CSV_NAME = "ns_sprint93_candidate_source_matrix_audit.csv"
REPORT_NAME = "ns_sprint93_candidate_source_matrix_audit.md"

FAIL_CLOSED = "fail-closed"
ROUTE_OPEN = "NS_SPRINT93_CANDIDATE_SOURCE_MATRIX_ROUTE_OPEN"

FORBIDDEN_DEPENDENCIES = [
    "target_absorption",
    "bkm",
    "serrin",
    "h1_continuation",
    "theta_preservation",
    "desired_conclusion",
    "epsilon_from_absorption",
]

SUMMARY_INPUTS = {
    "sprint87_absorption_scaling": Path(
        "outputs/ns_sprint87_absorption_scaling_audit/"
        "ns_sprint87_absorption_scaling_summary.json"
    ),
    "sprint87_factorization": Path(
        "outputs/ns_sprint87_danger_shell_factorization_audit/"
        "ns_sprint87_danger_shell_factorization_summary.json"
    ),
    "sprint88_h1_tail_decision": Path(
        "outputs/ns_sprint88_h1_tail_smallness_decision_audit/"
        "ns_sprint88_h1_tail_smallness_decision_summary.json"
    ),
    "sprint88_tail_classifier": Path(
        "outputs/ns_sprint88_tail_source_classifier/"
        "ns_sprint88_tail_source_classifier_summary.json"
    ),
    "sprint89_circularity": Path(
        "outputs/ns_sprint89_circularity_matrix_audit/"
        "ns_sprint89_circularity_matrix_audit_summary.json"
    ),
    "sprint89_pointwise_mechanism": Path(
        "outputs/ns_sprint89_pointwise_h1_tail_mechanism_audit/"
        "ns_sprint89_pointwise_h1_tail_mechanism_summary.json"
    ),
    "sprint90_epsilon_solver": Path(
        "outputs/ns_sprint90_epsilon_budget_solver/"
        "ns_sprint90_epsilon_budget_solver_summary.json"
    ),
    "sprint90_local_enstrophy": Path(
        "outputs/ns_sprint90_local_enstrophy_budget_audit/"
        "ns_sprint90_local_enstrophy_budget_audit_summary.json"
    ),
    "sprint91_coefficient_independence": Path(
        "outputs/ns_sprint91_coefficient_independence_audit/"
        "ns_sprint91_coefficient_independence_audit_summary.json"
    ),
    "sprint91_localized_flux": Path(
        "outputs/ns_sprint91_localized_flux_identity_audit/"
        "ns_sprint91_localized_flux_identity_audit_summary.json"
    ),
    "sprint92_high_high_dominance": Path(
        "outputs/ns_sprint92_high_high_dominance_budget_audit/"
        "ns_sprint92_high_high_dominance_budget_audit_summary.json"
    ),
    "sprint92_moving_kstar": Path(
        "outputs/ns_sprint92_moving_kstar_boundary_audit/"
        "ns_sprint92_moving_kstar_boundary_audit_summary.json"
    ),
}


@dataclass(frozen=True)
class CandidateSource:
    source_id: str
    candidate_source: str
    source_kind: str
    source_surface: str
    evidence_summary_key: str
    supplies_dominance: bool
    supplies_pointwise_h1_tail: bool
    supplies_independent_coefficient: bool
    target_absorption: bool
    bkm: bool
    serrin: bool
    h1_continuation: bool
    theta_preservation: bool
    desired_conclusion: bool
    epsilon_from_absorption: bool
    classification: str
    evidence_note: str
    next_required_input: str
    allowed_source: bool = True

    @property
    def forbidden_hits(self) -> list[str]:
        return [name for name in FORBIDDEN_DEPENDENCIES if bool(getattr(self, name))]

    @property
    def avoids_forbidden_dependencies(self) -> bool:
        return not self.forbidden_hits

    @property
    def same_source_completeness(self) -> bool:
        return (
            self.supplies_dominance
            and self.supplies_pointwise_h1_tail
            and self.supplies_independent_coefficient
        )

    @property
    def accepted(self) -> bool:
        return (
            self.allowed_source
            and self.avoids_forbidden_dependencies
            and self.same_source_completeness
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def candidate_sources() -> list[CandidateSource]:
    clear = dict(
        target_absorption=False,
        bkm=False,
        serrin=False,
        h1_continuation=False,
        theta_preservation=False,
        desired_conclusion=False,
        epsilon_from_absorption=False,
    )
    return [
        CandidateSource(
            "S87A",
            "Sprint87 absorption scaling",
            "scalar absorption condition",
            "scripts/ns_sprint87_absorption_scaling_audit.py; outputs/ns_sprint87_absorption_scaling_audit",
            "sprint87_absorption_scaling",
            False,
            False,
            False,
            **clear,
            classification="SCALAR_CONDITION_ONLY",
            evidence_note="Records required scalar law, but does not supply the pointwise tail or independent coefficient.",
            next_required_input="non-circular tail law and coefficient fixed before absorption",
        ),
        CandidateSource(
            "S87B",
            "Sprint87 danger-shell factorization",
            "high-high factorization receipt",
            "scripts/ns_sprint87_danger_shell_factorization_audit.py; DASHI/Physics/Closure/NSSprint87DangerShellSupFactorizationReceipt.agda",
            "sprint87_factorization",
            False,
            False,
            False,
            **clear,
            classification="FACTORIZATION_SUPPORT_ONLY",
            evidence_note="Factorization support is closed, while danger-shell absorption remains the next gate.",
            next_required_input="pre-absorption dominance with pointwise tail and coefficient",
        ),
        CandidateSource(
            "S88A",
            "Sprint88 H1 tail decision",
            "tail-smallness decision receipt",
            "scripts/ns_sprint88_h1_tail_smallness_decision_audit.py; DASHI/Physics/Closure/NSSprint88DangerShellH1TailSmallnessDecisionReceipt.agda",
            "sprint88_h1_tail_decision",
            False,
            False,
            False,
            **clear,
            classification="TAIL_GATE_RECORDED_OPEN",
            evidence_note="Records that non-circular danger-shell H1-tail smallness is still open.",
            next_required_input="prove non-circular pointwise H1-tail smallness",
        ),
        CandidateSource(
            "S88B",
            "Sprint88 tail source classifier",
            "tail candidate classifier",
            "scripts/ns_sprint88_tail_source_classifier.py; outputs/ns_sprint88_tail_source_classifier",
            "sprint88_tail_classifier",
            False,
            False,
            False,
            **clear,
            classification="ALL_TAIL_CANDIDATES_FAIL_CLOSED",
            evidence_note="Classifier records zero sufficient sources for pointwise absorption.",
            next_required_input="one source with pointwise H1 tail and independent coefficient",
        ),
        CandidateSource(
            "S89A",
            "Sprint89 circularity matrix",
            "forbidden dependency matrix",
            "scripts/ns_sprint89_circularity_matrix_audit.py; outputs/ns_sprint89_circularity_matrix_audit",
            "sprint89_circularity",
            False,
            False,
            False,
            **clear,
            classification="NO_ALLOWED_ROUTE",
            evidence_note="Matrix rejects current candidates and records no allowed route with both inputs.",
            next_required_input="allowed same-source route avoiding forbidden dependencies",
        ),
        CandidateSource(
            "S89B",
            "Sprint89 pointwise H1 mechanism",
            "pointwise extraction mechanism audit",
            "scripts/ns_sprint89_pointwise_h1_tail_mechanism_audit.py; outputs/ns_sprint89_pointwise_h1_tail_mechanism_audit",
            "sprint89_pointwise_mechanism",
            False,
            False,
            False,
            **clear,
            classification="MECHANISM_OPEN",
            evidence_note="Pointwise mechanism surface remains an audit of missing analytic extraction.",
            next_required_input="actual pointwise extraction theorem",
        ),
        CandidateSource(
            "S90A",
            "Sprint90 epsilon budget solver",
            "scalar/numeric budget solver",
            "scripts/ns_sprint90_epsilon_budget_solver.py; outputs/ns_sprint90_epsilon_budget_solver",
            "sprint90_epsilon_solver",
            False,
            False,
            False,
            **clear,
            classification="SOLVER_NEEDS_SUPPLIED_EVIDENCE",
            evidence_note="Solver can validate a supplied law but does not itself supply dominance, tail, or coefficient evidence.",
            next_required_input="feed supplied pointwise tail and independent coefficient",
        ),
        CandidateSource(
            "S90B",
            "Sprint90 local enstrophy",
            "local enstrophy/dissipation reduction receipt",
            "scripts/ns_sprint90_local_enstrophy_budget_audit.py; DASHI/Physics/Closure/NSSprint90LocalEnstrophyDangerShellReductionReceipt.agda",
            "sprint90_local_enstrophy",
            False,
            False,
            False,
            **clear,
            classification="LOCAL_ENSTROPHY_REDUCTION_ONLY",
            evidence_note="Relevant local-enstrophy receipt records reduction bookkeeping, with dominance, pointwise tail, and coefficient flags false.",
            next_required_input="close local dissipation dominance and pointwise extraction non-circularly",
        ),
        CandidateSource(
            "S91A",
            "Sprint91 coefficient independence",
            "coefficient classifier",
            "scripts/ns_sprint91_coefficient_independence_audit.py; outputs/ns_sprint91_coefficient_independence_audit",
            "sprint91_coefficient_independence",
            False,
            False,
            False,
            **clear,
            classification="NO_INDEPENDENT_COEFFICIENT_SOURCE",
            evidence_note="Finds no allowed source with both pointwise H1 tail and independent coefficient.",
            next_required_input="coefficient fixed independently on same source as tail and dominance",
        ),
        CandidateSource(
            "S91B",
            "Sprint91 localized flux identity",
            "localized flux identity bookkeeping",
            "scripts/ns_sprint91_localized_flux_identity_audit.py; DASHI/Physics/Closure/NSSprint91LocalizedFluxIdentityAndCoefficientBudget.agda",
            "sprint91_localized_flux",
            False,
            False,
            False,
            **clear,
            classification="IDENTITY_BOOKKEEPING_ONLY",
            evidence_note="Localized identity bookkeeping is closed; dominance, tail, and coefficient gates remain false.",
            next_required_input="analytic domination theorem with pointwise extraction and coefficient",
        ),
        CandidateSource(
            "S92A",
            "Sprint92 high-high dominance budget",
            "target dominance budget audit",
            "scripts/ns_sprint92_high_high_dominance_budget_audit.py; outputs/ns_sprint92_high_high_dominance_budget_audit",
            "sprint92_high_high_dominance",
            False,
            False,
            False,
            **clear,
            classification="DOMINANCE_BUDGET_FAIL_CLOSED",
            evidence_note="Direct dominance audit records no allowed source closing target dominance with both required inputs.",
            next_required_input="one allowed non-circular dominance source",
        ),
        CandidateSource(
            "S92B",
            "Sprint92 moving K* boundary",
            "moving K localization boundary audit",
            "scripts/ns_sprint92_moving_kstar_boundary_audit.py; DASHI/Physics/Closure/NSSprint92MovingKStarLocalizationBoundary.agda",
            "sprint92_moving_kstar",
            False,
            False,
            False,
            **clear,
            classification="MOVING_BOUNDARY_OPEN",
            evidence_note="Frozen-K bookkeeping is recorded, but moving boundary, dominance, tail, and coefficient gates remain false.",
            next_required_input="moving K* boundary plus dominance/tail/coefficient source",
        ),
        CandidateSource(
            "X1",
            "Split-source dominance tail coefficient attempt",
            "rejected multi-source assembly",
            "outputs/ns_sprint90_local_enstrophy_budget_audit; outputs/ns_sprint91_coefficient_independence_audit; outputs/ns_sprint92_high_high_dominance_budget_audit",
            "sprint92_high_high_dominance",
            False,
            False,
            False,
            **clear,
            classification="REJECT_SPLIT_SOURCE_ASSEMBLY",
            evidence_note="Separate surfaces discuss parts of the desired package, but no same source supplies dominance, pointwise H1 tail, and independent coefficient.",
            next_required_input="one same-source proof surface carrying all three inputs",
            allowed_source=False,
        ),
        CandidateSource(
            "F1",
            "Adjacent leakage / target absorption reuse",
            "forbidden absorption-derived coefficient",
            "DASHI/Physics/Closure/NSAdjacentShellLeakageBoundReceipt.agda",
            "sprint87_absorption_scaling",
            False,
            False,
            False,
            target_absorption=True,
            bkm=False,
            serrin=False,
            h1_continuation=False,
            theta_preservation=False,
            desired_conclusion=False,
            epsilon_from_absorption=True,
            classification="REJECT_TARGET_ABSORPTION_EPSILON_REUSE",
            evidence_note="Leakage estimates tied to the target absorption epsilon are circular for coefficient supply.",
            next_required_input="coefficient fixed before and outside target absorption",
            allowed_source=False,
        ),
        CandidateSource(
            "F2",
            "Target conclusion / continuation shortcuts",
            "forbidden downstream regularity route",
            "BKM/Serrin/H1 continuation/theta preservation/desired conclusion shortcuts",
            "sprint89_circularity",
            True,
            True,
            True,
            target_absorption=True,
            bkm=True,
            serrin=True,
            h1_continuation=True,
            theta_preservation=True,
            desired_conclusion=True,
            epsilon_from_absorption=True,
            classification="REJECT_FORBIDDEN_DEPENDENCIES_EVEN_IF_COMPLETE",
            evidence_note="This synthetic rejection row proves the matrix rejects forbidden complete-looking routes.",
            next_required_input="same facts from an allowed pre-continuation source",
            allowed_source=False,
        ),
    ]


def evidence_summaries(repo_root: Path) -> dict[str, dict[str, Any]]:
    return {key: read_json(repo_root / path) for key, path in SUMMARY_INPUTS.items()}


def surface_present(repo_root: Path, surface: str) -> bool:
    concrete = [part.strip() for part in surface.split(";") if part.strip()]
    existing = []
    for part in concrete:
        if part.startswith("BKM/") or part.startswith("DASHI/") or part.startswith("outputs/") or part.startswith("scripts/"):
            existing.append((repo_root / part).exists())
    return bool(existing) and all(existing)


def source_rows(repo_root: Path) -> list[dict[str, Any]]:
    summaries = evidence_summaries(repo_root)
    rows: list[dict[str, Any]] = []
    for source in candidate_sources():
        summary = summaries.get(source.evidence_summary_key, {})
        row = asdict(source)
        row.update(
            {
                "summary_path": SUMMARY_INPUTS[source.evidence_summary_key].as_posix(),
                "summary_present": bool(summary),
                "summary_contract": summary.get("contract", "missing"),
                "summary_complete": summary.get("complete", "missing"),
                "summary_route_decision": summary.get("route_decision", "missing"),
                "forbidden_hits": "; ".join(source.forbidden_hits) if source.forbidden_hits else "none",
                "forbidden_hit_count": len(source.forbidden_hits),
                "avoids_forbidden_dependencies": source.avoids_forbidden_dependencies,
                "same_source_completeness": source.same_source_completeness,
                "accepted": source.accepted,
                "route_decision": ROUTE_OPEN if source.accepted else FAIL_CLOSED,
                "source_surface_present": surface_present(repo_root, source.source_surface),
            }
        )
        rows.append(row)
    return rows


def summary_payload(rows: list[dict[str, Any]]) -> dict[str, Any]:
    accepted = [row for row in rows if row["accepted"]]
    return {
        "contract": CONTRACT,
        "complete": bool(accepted),
        "route_decision": ROUTE_OPEN if accepted else FAIL_CLOSED,
        "final_decision": "ACCEPTED" if accepted else "FAIL_CLOSED",
        "fail_closed": not accepted,
        "candidate_source_count": len(rows),
        "accepted_source_count": len(accepted),
        "accepted_sources": [row["candidate_source"] for row in accepted],
        "required_residual_gate": "DominanceWithPointwiseTailAndIndependentCoefficient",
        "residual_gate": "DominanceWithPointwiseTailAndIndependentCoefficient",
        "clay_navier_stokes_promoted": False,
        "clay_promotion": False,
        "forbidden_dependencies": FORBIDDEN_DEPENDENCIES,
        "rejects_target_absorption": True,
        "rejects_bkm": True,
        "rejects_serrin": True,
        "rejects_h1_continuation": True,
        "rejects_theta_preservation": True,
        "rejects_desired_conclusion": True,
        "rejects_epsilon_from_absorption": True,
        "requires_same_source_completeness": True,
        "requires_dominance": True,
        "requires_pointwise_h1_tail": True,
        "requires_independent_coefficient": True,
        "any_allowed_dominance": any(
            row["allowed_source"] and row["avoids_forbidden_dependencies"] and row["supplies_dominance"]
            for row in rows
        ),
        "any_allowed_pointwise_h1_tail": any(
            row["allowed_source"] and row["avoids_forbidden_dependencies"] and row["supplies_pointwise_h1_tail"]
            for row in rows
        ),
        "any_allowed_independent_coefficient": any(
            row["allowed_source"] and row["avoids_forbidden_dependencies"] and row["supplies_independent_coefficient"]
            for row in rows
        ),
        "same_source_complete_count": sum(
            1
            for row in rows
            if row["allowed_source"]
            and row["avoids_forbidden_dependencies"]
            and row["same_source_completeness"]
        ),
        "rejected_for_forbidden_dependencies": [
            {"candidate_source": row["candidate_source"], "forbidden_hits": row["forbidden_hits"]}
            for row in rows
            if row["forbidden_hit_count"]
        ],
        "all_referenced_summaries_present": all(row["summary_present"] for row in rows),
        "all_declared_surfaces_present": all(row["source_surface_present"] for row in rows if row["source_id"] != "F2"),
        "fail_closed_reason": (
            "No allowed same-source Sprint87-92/local-enstrophy/dissipation source supplies dominance, "
            "pointwise H1 tail, and independent coefficient while avoiding forbidden dependencies."
        ),
        "rows_json": ROWS_JSON_NAME,
        "rows_csv": ROWS_CSV_NAME,
        "report": REPORT_NAME,
        "open_obligations": [
            "supply dominance before using target absorption",
            "supply pointwise H1 tail without BKM/Serrin/H1 continuation/theta preservation",
            "supply an independent coefficient not derived from absorption",
            "record dominance, tail, and coefficient on the same allowed source",
        ],
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 93 Candidate-Source Matrix Audit",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Decision: `{summary['final_decision']}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Candidate sources: `{summary['candidate_source_count']}`",
        f"- Accepted sources: `{summary['accepted_source_count']}`",
        "",
        "## Fail-Closed Rule",
        "",
        (
            "A candidate is accepted only when one allowed source supplies dominance, "
            "pointwise H1 tail, and an independent coefficient, and avoids target "
            "absorption, BKM, Serrin, H1 continuation, theta preservation, desired "
            "conclusion, and epsilon-from-absorption dependencies."
        ),
        "",
        "## Matrix",
        "",
        "| Source | Dominance | H1 tail | Independent coefficient | Avoids forbidden | Same-source complete | Classification | Decision |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(
            f"| {row['candidate_source']} | `{row['supplies_dominance']}` | "
            f"`{row['supplies_pointwise_h1_tail']}` | "
            f"`{row['supplies_independent_coefficient']}` | "
            f"`{row['avoids_forbidden_dependencies']}` | "
            f"`{row['same_source_completeness']}` | "
            f"`{row['classification']}` | `{row['route_decision']}` |"
        )
    lines.extend(["", "## Rejections", ""])
    for row in rows:
        if row["forbidden_hit_count"]:
            lines.append(f"- `{row['candidate_source']}` rejected for `{row['forbidden_hits']}`.")
    lines.extend(["", "## Open Obligations", ""])
    for obligation in summary["open_obligations"]:
        lines.append(f"- {obligation}")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = source_rows(repo_root)
    summary = summary_payload(rows)

    (out_dir / SUMMARY_NAME).write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (out_dir / ROWS_JSON_NAME).write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    (out_dir / REPORT_NAME).write_text(markdown(summary, rows), encoding="utf-8")

    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
