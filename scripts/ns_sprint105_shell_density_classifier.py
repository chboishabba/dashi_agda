#!/usr/bin/env python3
"""Sprint 105 NS shell-density source classifier."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint105_shell_density_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint105_shell_density_classifier")
SUMMARY_NAME = "ns_sprint105_shell_density_classifier_summary.json"
ROWS_NAME = "ns_sprint105_shell_density_classifier_rows.json"
REPORT_NAME = "ns_sprint105_shell_density_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_SHELL_DENSITY_SOURCE"

REQUIRED_GATES = (
    "lp_projector",
    "local_density_definition",
    "leray_integrability",
    "localization_bound",
    "non_circular_construction",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "external_forcing",
    "imposed_density_locus",
    "imposed_shell_energy",
    "target_kstar_collapse",
)


@dataclass(frozen=True)
class ShellDensityCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    lp_projector: bool
    local_density_definition: bool
    leray_integrability: bool
    localization_bound: bool
    non_circular_construction: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "lp_projector": self.lp_projector,
            "local_density_definition": self.local_density_definition,
            "leray_integrability": self.leray_integrability,
            "localization_bound": self.localization_bound,
            "non_circular_construction": self.non_circular_construction,
            "no_forbidden_dependency": self.no_forbidden_dependency,
        }

    @property
    def accepted(self) -> bool:
        return all(self.gate_results.values())

    def row(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["forbidden_dependencies"] = (
            "none" if not self.forbidden_dependencies else ";".join(self.forbidden_dependencies)
        )
        payload["no_forbidden_dependency"] = self.no_forbidden_dependency
        payload["gate_results"] = self.gate_results
        payload["failed_gates"] = [
            gate for gate, passed in self.gate_results.items() if not passed
        ]
        payload["accepted"] = self.accepted
        return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def candidate_families() -> list[ShellDensityCandidate]:
    return [
        ShellDensityCandidate(
            family_id="LP1",
            family="lp_projector_density",
            ansatz="define shell density from Littlewood-Paley projected velocity energy",
            classification="projector identity without independent density source",
            lp_projector=True,
            local_density_definition=True,
            leray_integrability=True,
            localization_bound=False,
            non_circular_construction=False,
            forbidden_dependencies=("desired_conclusion",),
            verdict="reject",
            note=(
                "The Littlewood-Paley projector supplies a formal shell energy density, "
                "but the needed localized lower-bound mechanism is not derived independently."
            ),
        ),
        ShellDensityCandidate(
            family_id="M1",
            family="mollified_local_energy_density",
            ansatz="mollify the local energy inequality to obtain a scale-local density",
            classification="local energy density without shell localization closure",
            lp_projector=False,
            local_density_definition=True,
            leray_integrability=True,
            localization_bound=False,
            non_circular_construction=False,
            forbidden_dependencies=(),
            verdict="reject",
            note=(
                "Mollification is Leray-compatible and defines a local density, but it "
                "does not isolate a dyadic shell source or close the localization bound."
            ),
        ),
        ShellDensityCandidate(
            family_id="D1",
            family="dyadic_square_function_density",
            ansatz="use a dyadic square function as a shell-density candidate",
            classification="square-function control without pointwise shell source",
            lp_projector=True,
            local_density_definition=True,
            leray_integrability=True,
            localization_bound=False,
            non_circular_construction=False,
            forbidden_dependencies=("target_kstar_collapse",),
            verdict="reject",
            note=(
                "Square functions organize dyadic energy, but converting that ledger "
                "into the target localized shell source relies on the collapse endpoint."
            ),
        ),
        ShellDensityCandidate(
            family_id="W1",
            family="weak_leray_density_extraction",
            ansatz="extract shell density from weak compactness of Leray approximants",
            classification="compactness extraction without constructive localization",
            lp_projector=True,
            local_density_definition=False,
            leray_integrability=True,
            localization_bound=False,
            non_circular_construction=False,
            forbidden_dependencies=("assumed_singularity",),
            verdict="reject",
            note=(
                "Weak compactness can pass to subsequential energy distributions, but "
                "it does not construct a local shell density source without assuming a singular endpoint."
            ),
        ),
        ShellDensityCandidate(
            family_id="I1",
            family="imposed_shell_density",
            ansatz="select the shell-density locus and shell energy directly",
            classification="forbidden imposed shell-density source",
            lp_projector=True,
            local_density_definition=True,
            leray_integrability=False,
            localization_bound=True,
            non_circular_construction=False,
            forbidden_dependencies=("imposed_density_locus", "imposed_shell_energy", "desired_conclusion"),
            verdict="reject",
            note=(
                "The candidate builds the needed density locus and shell energy into "
                "the construction, so any apparent bound is circular."
            ),
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [candidate.row() for candidate in candidate_families()]
    accepted = [row for row in rows if row["accepted"]]
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic classifier for Navier-Stokes shell-density source candidates",
        "fail_closed": True,
        "route_decision": ROUTE_DECISION,
        "final_decision": ROUTE_DECISION,
        "accepted_source_count": len(accepted),
        "candidate_family_count": len(rows),
        "required_gates": list(REQUIRED_GATES),
        "forbidden_dependencies": list(FORBIDDEN_DEPENDENCIES),
        "accepted_families": [row["family"] for row in accepted],
        "rejected_families": [row["family"] for row in rows if not row["accepted"]],
        "option_b_closed": False,
        "clay_navier_stokes_promoted": False,
        "sprint105_shell_density_source_closed": False,
        "fail_closed_reason": (
            "No candidate derives a shell-local density, Leray integrability, localization "
            "bound, and non-circular construction while avoiding forbidden dependencies."
        ),
        "control_card": {
            "O": "classify candidate shell-density source families",
            "R": "all six gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting JSON and Markdown",
            "S": "five requested candidates evaluated in fixed order",
            "L": "acceptance is conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false",
            "F": "accepted_source_count is zero because every candidate fails non_circular_construction or a prerequisite gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 105 Shell-Density Source Classifier",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Fail closed: `{str(summary['fail_closed']).lower()}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Accepted source count: `{summary['accepted_source_count']}`",
        f"- Candidate family count: `{summary['candidate_family_count']}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        "- Required gates: " + ", ".join(f"`{gate}`" for gate in summary["required_gates"]),
        "- Forbidden dependencies: "
        + ", ".join(f"`{item}`" for item in summary["forbidden_dependencies"]),
        "",
        "| Family | Accepted | Failed gates | Forbidden dependencies | Note |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["rows"]:
        failed = "none" if not row["failed_gates"] else ", ".join(f"`{gate}`" for gate in row["failed_gates"])
        lines.append(
            f"| `{row['family']}` | `{str(row['accepted']).lower()}` | {failed} | `{row['forbidden_dependencies']}` | {row['note']} |"
        )
    lines.extend(["", summary["fail_closed_reason"]])
    return "\n".join(lines) + "\n"


def write_outputs(out_dir: Path, summary: dict[str, Any]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / SUMMARY_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / ROWS_NAME).write_text(json.dumps(summary["rows"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / REPORT_NAME).write_text(render_markdown(summary), encoding="utf-8")


def main() -> int:
    args = parse_args()
    summary = build_summary()
    write_outputs(args.out_dir, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
