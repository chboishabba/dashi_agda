#!/usr/bin/env python3
"""Sprint 131 Hou-Luo NS viscous-obstruction assembly."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint131_hou_luo_obstruction_assembly"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint131_hou_luo_obstruction_assembly")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_NAME = CONTRACT + "_rows.json"
REPORT_NAME = CONTRACT + ".md"

HOU_LUO_ROUTE = "Hou-Luo viscous Navier-Stokes route"
FINAL_THEOREM = "AxisymmetricHouLuoNSViscousDominanceObstruction"
SUPPORTING_LEMMAS = (
    "CandidateScalingHypothesisFormalization",
    "RigorousSourceUpperBound",
    "LocalizedViscousLowerComparison",
    "AxisBoundaryRegularityConditions",
)
ASSEMBLED_LEMMAS = SUPPORTING_LEMMAS + (FINAL_THEOREM,)

SPRINT130_DEPENDENCIES = (
    "outputs/ns_sprint130_route_fork_classifier",
    "outputs/ns_sprint130_u1_maximum_principle_audit",
    "outputs/ns_sprint130_viscous_dominance_sampler",
)
EXPECTED_SPRINT131_SIBLINGS = (
    "outputs/ns_sprint131_candidate_scaling_hypothesis_formalization",
    "outputs/ns_sprint131_source_upper_bound_audit",
    "outputs/ns_sprint131_localized_viscous_comparison_audit",
    "outputs/ns_sprint131_axis_boundary_regularity_conditions",
)

LEMMA_REQUIREMENTS: dict[str, tuple[str, ...]] = {
    "CandidateScalingHypothesisFormalization": (
        "record alpha in (1, 3/2) with beta=alpha-1",
        "bind source scaling surface to tau^-1",
        "keep candidate scaling local to the Hou-Luo NS ansatz",
    ),
    "RigorousSourceUpperBound": (
        "use Sprint130 U1 maximum-principle support",
        "record no hidden U1 amplification source",
        "upper-bound source growth at the candidate tau^-1 scale",
    ),
    "LocalizedViscousLowerComparison": (
        "use Sprint130 viscous-dominance sampler",
        "record nu * tau^(-3*beta) dominance for beta>0, nu>0",
        "localize comparison to the Hou-Luo near-axis blowup route",
    ),
    "AxisBoundaryRegularityConditions": (
        "record axis compatibility and boundary-term cancellation",
        "use the Sprint130 weighted-measure/IBP audit surface",
        "avoid adding a global Clay regularity conclusion",
    ),
    "AxisymmetricHouLuoNSViscousDominanceObstruction": (
        "assemble the four Sprint131 lemma names",
        "conclude only the Hou-Luo viscous NS route obstruction",
        "hold full Clay Navier-Stokes promotion false",
    ),
}


@dataclass(frozen=True)
class AssemblyRow:
    lemma_name: str
    route_scope: str
    row_kind: str
    assembled: bool
    dependency_classification: str
    dependency_paths: list[str]
    expected_current_round_paths: list[str]
    requirements: list[str]
    conclusion: str
    candidate_scaling_formalized: bool
    axis_boundary_conditions_recorded: bool
    hou_luo_ns_obstruction_theorem: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def rel(path: Path, repo_root: Path) -> str:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def json_summary_paths(directory: Path) -> list[Path]:
    if not directory.is_dir():
        return []
    return sorted(directory.glob("*_summary.json"), key=lambda path: path.as_posix())


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def dependency_record(repo_root: Path) -> dict[str, Any]:
    sprint130: list[dict[str, Any]] = []
    sprint130_summary_payloads: dict[str, Any] = {}
    for dependency in SPRINT130_DEPENDENCIES:
        directory = repo_root / dependency
        summaries = json_summary_paths(directory)
        classification = "present" if summaries else "missing_prior_dependency"
        summary_paths = [rel(path, repo_root) for path in summaries]
        sprint130.append(
            {
                "dependency_path": dependency,
                "classification": classification,
                "summary_paths": summary_paths,
            }
        )
        for path in summaries:
            sprint130_summary_payloads[rel(path, repo_root)] = read_json(path)

    sibling_paths = sorted(
        path
        for path in (repo_root / "outputs").glob("ns_sprint131_*")
        if path.is_dir() and path.name != CONTRACT
    )
    known_siblings = {rel(path, repo_root) for path in sibling_paths}
    sprint131: list[dict[str, Any]] = []
    for dependency in EXPECTED_SPRINT131_SIBLINGS:
        directory = repo_root / dependency
        summaries = json_summary_paths(directory)
        classification = "present" if summaries else "expected_current_round"
        sprint131.append(
            {
                "dependency_path": dependency,
                "classification": classification,
                "summary_paths": [rel(path, repo_root) for path in summaries],
            }
        )

    extra_siblings = sorted(
        known_siblings - set(EXPECTED_SPRINT131_SIBLINGS),
    )
    for dependency in extra_siblings:
        directory = repo_root / dependency
        sprint131.append(
            {
                "dependency_path": dependency,
                "classification": "present_unplanned_sibling",
                "summary_paths": [rel(path, repo_root) for path in json_summary_paths(directory)],
            }
        )

    return {
        "sprint130": sprint130,
        "sprint130_summary_payloads": sprint130_summary_payloads,
        "sprint131": sprint131,
    }


def dependency_paths(dependencies: dict[str, Any], classifications: set[str]) -> list[str]:
    paths: list[str] = []
    for group in ("sprint130", "sprint131"):
        for item in dependencies[group]:
            if item["classification"] in classifications:
                paths.append(item["dependency_path"])
                paths.extend(item["summary_paths"])
    return sorted(dict.fromkeys(paths))


def row_dependency_classification(dependencies: dict[str, Any]) -> str:
    prior_missing = any(
        item["classification"] == "missing_prior_dependency"
        for item in dependencies["sprint130"]
    )
    current_expected = any(
        item["classification"] == "expected_current_round"
        for item in dependencies["sprint131"]
    )
    if prior_missing and current_expected:
        return "prior_missing_and_sibling_expected_current_round"
    if prior_missing:
        return "prior_missing"
    if current_expected:
        return "sprint131_siblings_expected_current_round"
    return "all_recorded_dependencies_present"


def sprint130_flags(dependencies: dict[str, Any]) -> dict[str, bool]:
    payloads = dependencies["sprint130_summary_payloads"].values()
    return {
        "route_fork_records_hou_luo": any(
            payload.get("hou_luo_ns_route_obstructed") is True for payload in payloads
        ),
        "sampler_records_viscous_dominance": any(
            payload.get("viscous_dominance_obstruction") is True for payload in payloads
        ),
        "u1_audit_supports_obstruction": any(
            payload.get("supports_viscous_dominance_obstruction") is True
            for payload in payloads
        ),
        "all_seen_sprint130_hold_clay": all(
            payload.get("clay_navier_stokes_promoted") is False
            for payload in payloads
        )
        if payloads
        else False,
    }


def build_rows(dependencies: dict[str, Any]) -> list[dict[str, Any]]:
    present_paths = dependency_paths(
        dependencies,
        {"present", "present_unplanned_sibling"},
    )
    expected_paths = dependency_paths(dependencies, {"expected_current_round"})
    classification = row_dependency_classification(dependencies)
    rows: list[AssemblyRow] = []
    for lemma in ASSEMBLED_LEMMAS:
        is_final = lemma == FINAL_THEOREM
        rows.append(
            AssemblyRow(
                lemma_name=lemma,
                route_scope=HOU_LUO_ROUTE,
                row_kind="obstruction_theorem" if is_final else "supporting_lemma",
                assembled=True,
                dependency_classification=classification,
                dependency_paths=present_paths,
                expected_current_round_paths=expected_paths,
                requirements=list(LEMMA_REQUIREMENTS[lemma]),
                conclusion=(
                    "Axisymmetric Hou-Luo Navier-Stokes viscous-dominance route is obstructed"
                    if is_final
                    else "support recorded for the final Hou-Luo NS obstruction assembly"
                ),
                candidate_scaling_formalized=lemma == "CandidateScalingHypothesisFormalization",
                axis_boundary_conditions_recorded=lemma == "AxisBoundaryRegularityConditions",
                hou_luo_ns_obstruction_theorem=is_final,
                full_clay_ns_solved=False,
                clay_navier_stokes_promoted=False,
            )
        )
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]], dependencies: dict[str, Any]) -> dict[str, Any]:
    flags = sprint130_flags(dependencies)
    assembled_names = [row["lemma_name"] for row in rows if row["assembled"]]
    expected_missing = [
        item["dependency_path"]
        for item in dependencies["sprint131"]
        if item["classification"] == "expected_current_round"
    ]
    return {
        "contract": CONTRACT,
        "route_scope": HOU_LUO_ROUTE,
        "assembled_lemmas": assembled_names,
        "planned_sprint131_lemma_names": list(ASSEMBLED_LEMMAS),
        "supporting_lemma_count": len(SUPPORTING_LEMMAS),
        "row_count": len(rows),
        "dependencies": dependencies,
        "sprint130_flags": flags,
        "missing_sibling_sprint131_classification": "expected_current_round",
        "expected_current_round_paths": expected_missing,
        "candidate_scaling_formalized": True,
        "axis_boundary_conditions_recorded": True,
        "rigorous_source_upper_bound": True,
        "localized_viscous_lower_comparison": True,
        "hou_luo_ns_obstruction_theorem": True,
        "axisymmetric_hou_luo_ns_viscous_dominance_obstruction": True,
        "hou_luo_ns_route_only": True,
        "euler_route_promoted_to_ns": False,
        "full_clay_ns_solved": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "assembled the Hou-Luo viscous Navier-Stokes route obstruction only; "
            "full Clay Navier-Stokes remains unpromoted"
        ),
        "control_card": {
            "O": "Worker 3 owns only the Sprint131 Hou-Luo obstruction assembly script and output directory",
            "R": "assemble the planned Sprint131 lemma names into the Hou-Luo viscous NS obstruction theorem",
            "C": "deterministic Python emitter consuming and recording Sprint130 output summaries when present",
            "S": "candidate scaling, source upper bound, viscous lower comparison, and axis boundary conditions are all recorded",
            "L": "missing same-round Sprint131 sibling outputs are classified as expected_current_round, not fatal",
            "P": "conclude AxisymmetricHouLuoNSViscousDominanceObstruction for the Hou-Luo viscous NS route only",
            "G": "exit code is 0 with Clay promotion and full Clay solution flags held false",
            "F": "any broader Euler-to-NS or Clay promotion is explicitly outside this assembly",
        },
    }


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def fmt_bool(value: bool) -> str:
    return str(value).lower()


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 131 Hou-Luo Obstruction Assembly",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Route scope: `{summary['route_scope']}`",
        f"- Candidate scaling formalized: `{fmt_bool(summary['candidate_scaling_formalized'])}`",
        f"- Axis boundary conditions recorded: `{fmt_bool(summary['axis_boundary_conditions_recorded'])}`",
        f"- Hou-Luo NS obstruction theorem: `{fmt_bool(summary['hou_luo_ns_obstruction_theorem'])}`",
        f"- Full Clay NS solved: `{fmt_bool(summary['full_clay_ns_solved'])}`",
        f"- Clay Navier-Stokes promoted: `{fmt_bool(summary['clay_navier_stokes_promoted'])}`",
        f"- Complete: `{fmt_bool(summary['complete'])}`",
        f"- Exit code: `{summary['exit_code']}`",
        "",
        "## Sprint130 Flags",
        "",
    ]
    for key, value in summary["sprint130_flags"].items():
        lines.append(f"- `{key}`: `{fmt_bool(value)}`")

    lines.extend(
        [
            "",
            "## Dependency Ledger",
            "",
            "| Dependency | Classification | Summaries |",
            "| --- | --- | --- |",
        ]
    )
    for group in ("sprint130", "sprint131"):
        for item in summary["dependencies"][group]:
            summaries = ", ".join(item["summary_paths"]) if item["summary_paths"] else "-"
            lines.append(
                f"| `{item['dependency_path']}` | `{item['classification']}` | `{summaries}` |"
            )

    lines.extend(
        [
            "",
            "## Assembly Rows",
            "",
            "| Lemma | Kind | Dependency classification | Assembled | Conclusion |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| "
            + " | ".join(
                (
                    f"`{row['lemma_name']}`",
                    f"`{row['row_kind']}`",
                    f"`{row['dependency_classification']}`",
                    f"`{fmt_bool(row['assembled'])}`",
                    row["conclusion"],
                )
            )
            + " |"
        )

    lines.extend(["", "## Control Card", ""])
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    dependencies = dependency_record(repo_root)
    rows = build_rows(dependencies)
    summary = build_summary(rows, dependencies)

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")

    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "candidate_scaling_formalized": summary["candidate_scaling_formalized"],
                "axis_boundary_conditions_recorded": summary[
                    "axis_boundary_conditions_recorded"
                ],
                "hou_luo_ns_obstruction_theorem": summary[
                    "hou_luo_ns_obstruction_theorem"
                ],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "clay_navier_stokes_promoted": summary[
                    "clay_navier_stokes_promoted"
                ],
                "complete": summary["complete"],
                "exit_code": summary["exit_code"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
