#!/usr/bin/env python3
"""Sprint 104 NS concentration-measure source classifier."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint104_concentration_measure_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint104_concentration_measure_classifier")
SUMMARY_NAME = "ns_sprint104_concentration_measure_classifier_summary.json"
ROWS_NAME = "ns_sprint104_concentration_measure_classifier_rows.json"
REPORT_NAME = "ns_sprint104_concentration_measure_classifier.md"
ROUTE_DECISION = "FAIL_CLOSED_CONCENTRATION_MEASURE_SOURCE"

REQUIRED_GATES = (
    "dyadic_energy_density",
    "threshold_selection",
    "locus_measurability",
    "scale_local_tightness",
    "leray_compatible",
    "non_circular_source",
    "no_forbidden_dependency",
)

FORBIDDEN_DEPENDENCIES = (
    "assumed_bkm_failure",
    "assumed_serrin_failure",
    "assumed_singularity",
    "target_blowup",
    "desired_conclusion",
    "external_forcing",
    "imposed_concentration_locus",
    "imposed_concentration_measure",
    "imposed_defect_measure",
    "imposed_high_frequency_threshold",
    "imposed_intermittency_profile",
    "maximal_locus_as_source",
    "target_kstar_collapse",
)


@dataclass(frozen=True)
class ConcentrationMeasureCandidate:
    family_id: str
    family: str
    ansatz: str
    classification: str
    dyadic_energy_density: bool
    threshold_selection: bool
    locus_measurability: bool
    scale_local_tightness: bool
    leray_compatible: bool
    non_circular_source: bool
    forbidden_dependencies: tuple[str, ...]
    verdict: str
    note: str

    @property
    def no_forbidden_dependency(self) -> bool:
        return len(self.forbidden_dependencies) == 0

    @property
    def gate_results(self) -> dict[str, bool]:
        return {
            "dyadic_energy_density": self.dyadic_energy_density,
            "threshold_selection": self.threshold_selection,
            "locus_measurability": self.locus_measurability,
            "scale_local_tightness": self.scale_local_tightness,
            "leray_compatible": self.leray_compatible,
            "non_circular_source": self.non_circular_source,
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


def candidate_families() -> list[ConcentrationMeasureCandidate]:
    return [
        ConcentrationMeasureCandidate(
            family_id="D1",
            family="shell_energy_density_threshold",
            ansatz="threshold dyadic shell energy density to define high-frequency concentration",
            classification="density threshold without closed scale-local tightness",
            dyadic_energy_density=True,
            threshold_selection=False,
            locus_measurability=True,
            scale_local_tightness=False,
            leray_compatible=True,
            non_circular_source=False,
            forbidden_dependencies=("imposed_high_frequency_threshold",),
            verdict="reject",
            note="The dyadic density is available, but the threshold needed to isolate concentration is not selected from a non-circular Leray budget.",
        ),
        ConcentrationMeasureCandidate(
            family_id="M1",
            family="maximal_function_locus",
            ansatz="use a Hardy-Littlewood or dyadic maximal function to choose the concentration locus",
            classification="measurable locus without source mechanism",
            dyadic_energy_density=True,
            threshold_selection=True,
            locus_measurability=True,
            scale_local_tightness=False,
            leray_compatible=True,
            non_circular_source=False,
            forbidden_dependencies=("maximal_locus_as_source",),
            verdict="reject",
            note="A maximal-function superlevel set is measurable, but it repackages concentration instead of deriving a scale-local source for it.",
        ),
        ConcentrationMeasureCandidate(
            family_id="E1",
            family="defect_measure_extraction",
            ansatz="extract a defect measure from weak limits of high-frequency energy densities",
            classification="compactness defect without constructive concentration source",
            dyadic_energy_density=True,
            threshold_selection=False,
            locus_measurability=True,
            scale_local_tightness=False,
            leray_compatible=True,
            non_circular_source=False,
            forbidden_dependencies=("imposed_defect_measure",),
            verdict="reject",
            note="Weak compactness can name a defect, but it does not provide a non-circular threshold or tight scale-local production mechanism.",
        ),
        ConcentrationMeasureCandidate(
            family_id="I1",
            family="intermittency_profile_measure",
            ansatz="assume an intermittency profile that concentrates high-frequency energy on sparse sets",
            classification="profile ansatz with imposed intermittency",
            dyadic_energy_density=True,
            threshold_selection=True,
            locus_measurability=True,
            scale_local_tightness=False,
            leray_compatible=False,
            non_circular_source=False,
            forbidden_dependencies=("imposed_intermittency_profile", "desired_conclusion"),
            verdict="reject",
            note="The intermittency profile supplies the desired concentration geometry as an ansatz rather than deriving it inside the unforced Leray class.",
        ),
        ConcentrationMeasureCandidate(
            family_id="C1",
            family="imposed_concentration_locus",
            ansatz="select the concentration locus directly and measure high-frequency energy there",
            classification="forbidden imposed concentration",
            dyadic_energy_density=True,
            threshold_selection=True,
            locus_measurability=True,
            scale_local_tightness=True,
            leray_compatible=False,
            non_circular_source=False,
            forbidden_dependencies=("imposed_concentration_locus", "imposed_concentration_measure", "desired_conclusion"),
            verdict="reject",
            note="This candidate passes formal measurement checks only by building the concentration locus into the input data.",
        ),
    ]


def build_summary() -> dict[str, Any]:
    rows = [candidate.row() for candidate in candidate_families()]
    accepted = [row for row in rows if row["accepted"]]
    return {
        "contract": CONTRACT,
        "complete": False,
        "proof_claimed": False,
        "scope": "deterministic classifier for high-frequency concentration measure sources",
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
        "sprint104_concentration_measure_source_closed": False,
        "fail_closed_reason": (
            "No candidate derives dyadic density, threshold selection, measurable locus, "
            "and scale-local tightness from a non-circular Leray-compatible source."
        ),
        "control_card": {
            "O": "classify candidate high-frequency concentration measure sources",
            "R": "all seven gates must pass and forbidden dependencies must be absent",
            "C": "single deterministic Python ledger emitting JSON and Markdown",
            "S": "five requested candidates evaluated in fixed order",
            "L": "acceptance is conjunction of gate_results",
            "P": ROUTE_DECISION,
            "G": "Clay Navier-Stokes promotion remains false",
            "F": "accepted_source_count is zero because every candidate fails non_circular_source or a prerequisite gate",
        },
        "rows": rows,
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Sprint 104 Concentration-Measure Source Classifier",
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
