#!/usr/bin/env python3
"""Sprint 133 axisymmetric-with-swirl target emitter.

This deterministic emitter records the finite, Clay-adjacent target
AxisymmetricNSWithSwirlGlobalRegularity.  The target is deliberately narrower
than full 3D Navier-Stokes regularity: it asks for global regularity inside the
axisymmetric-with-swirl symmetry class, where the Sprint 130-132 obstruction
surfaces give concrete support but do not yet close the large-Re, marginal, or
class-exhaustion gates.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint133_axisymmetric_swirl_target"
TARGET = "AxisymmetricNSWithSwirlGlobalRegularity"
TARGET_ID = "axisymmetric_ns_with_swirl_global_regularity"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint133_axisymmetric_swirl_target")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_NAME = CONTRACT + "_rows.json"
CSV_NAME = CONTRACT + "_rows.csv"
GATES_JSON_NAME = CONTRACT + "_gates.json"
GATES_CSV_NAME = CONTRACT + "_gates.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT_DEPENDENCIES = {
    "sprint130": (
        "PureDiffusionU1MaximumPrinciple",
        "ViscousDominanceNearBlowup",
        "RouteForkClassifier",
    ),
    "sprint131": (
        "RigorousSourceUpperBound",
        "LocalizedViscousLowerComparison",
        "HouLuoObstructionAssembly",
    ),
    "sprint132": (
        "NSPartialRegularityFromObstructionTower",
        "MechanismExhaustionAudit",
        "GapInventoryClassifier",
    ),
}

FINITE_GATES = (
    "large_re_axisymmetric_transient_control",
    "marginal_beta_zero_analysis",
    "axisymmetric_symmetry_class_exhaustion",
    "axisymmetric_swirl_global_assembly",
)


@dataclass(frozen=True)
class TargetGate:
    gate_id: str
    target: str
    gate_name: str
    finite_gate: bool
    status: str
    proof_objective: str
    key_estimate_or_claim: str
    dependencies: tuple[str, ...]
    existing_support: tuple[str, ...]
    missing_lemmas: tuple[str, ...]
    closure_condition: str
    clay_relevance: str
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in ("dependencies", "existing_support", "missing_lemmas"):
            row[key] = list(row[key])
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        TargetGate(
            gate_id="large_re_axisymmetric_transient_control",
            target=TARGET,
            gate_name="large_re_axisymmetric_transient_control",
            finite_gate=True,
            status="open",
            proof_objective=(
                "Upgrade the moderate-Re Hou-Luo viscous obstruction to a full "
                "PDE estimate that prevents a large-Re transient from reaching "
                "BKM divergence before viscosity dominates."
            ),
            key_estimate_or_claim=(
                "For beta>0 and nu>0, axisymmetric swirl source growth cannot "
                "outrun localized diffusion uniformly over large Reynolds data."
            ),
            dependencies=(
                "Sprint130:PureDiffusionU1MaximumPrinciple",
                "Sprint130:ViscousDominanceNearBlowup",
                "Sprint131:RigorousSourceUpperBound",
                "Sprint131:LocalizedViscousLowerComparison",
                "Sprint131:HouLuoObstructionAssembly",
                "Sprint132:GapInventoryClassifier",
            ),
            existing_support=(
                "u1 has an exact maximum principle and no autonomous source",
                "localized beta>0 comparison gives viscous/source divergence",
                "Sprint132 isolates large-Re axisymmetric data as an open gate",
            ),
            missing_lemmas=(
                "NoLogAxisymmetricBiotSavartUniform",
                "LargeReAxisymmetricTransientControl",
            ),
            closure_condition=(
                "A uniform PDE comparison rules out finite-time BKM blowup for "
                "all beta>0 axisymmetric-with-swirl data, including large Re."
            ),
            clay_relevance=(
                "Closes the concentrated Hou-Luo branch inside the axisymmetric "
                "symmetry class, not the full Clay problem."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        TargetGate(
            gate_id="marginal_beta_zero_analysis",
            target=TARGET,
            gate_name="marginal_beta_zero_analysis",
            finite_gate=True,
            status="open",
            proof_objective=(
                "Analyze the no-concentration boundary regime where beta=0 and "
                "the Sprint130/131 viscous dominance ratio no longer diverges."
            ),
            key_estimate_or_claim=(
                "Large-scale shear without shrinking delta cannot sustain BKM "
                "growth unless a new nonlocal axisymmetric amplification "
                "estimate is available."
            ),
            dependencies=(
                "Sprint130:RouteForkClassifier",
                "Sprint131:RigorousSourceUpperBound",
                "Sprint132:GapInventoryClassifier",
            ),
            existing_support=(
                "the source remains exactly partial_z(u1^2)=2 u1 partial_z u1",
                "u1 remains bounded by its initial Linf norm for nu>0",
                "Sprint132 names beta=0 as a separate open marginal gate",
            ),
            missing_lemmas=(
                "MarginalScalingCaseAnalysis",
                "LargeScaleShearCannotForceBKM",
            ),
            closure_condition=(
                "A beta=0 continuation estimate shows the marginal source term "
                "cannot force BKM divergence from finite-energy smooth data."
            ),
            clay_relevance=(
                "Closes the non-concentrating axisymmetric boundary case only."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        TargetGate(
            gate_id="axisymmetric_symmetry_class_exhaustion",
            target=TARGET,
            gate_name="axisymmetric_symmetry_class_exhaustion",
            finite_gate=True,
            status="open",
            proof_objective=(
                "Replace full 3D mechanism enumeration with an axisymmetric "
                "structure theorem showing every axisymmetric BKM-divergent "
                "scenario enters either beta>0 concentration or beta=0 marginal "
                "scaling after suitable localization."
            ),
            key_estimate_or_claim=(
                "Within the axisymmetric-with-swirl class, potential singular "
                "sequences admit a finite scaling dichotomy: concentrated "
                "beta>0 or marginal beta=0."
            ),
            dependencies=(
                "Sprint132:NSPartialRegularityFromObstructionTower",
                "Sprint132:MechanismExhaustionAudit",
                "Sprint132:GapInventoryClassifier",
            ),
            existing_support=(
                "Sprint132 shows full 3D mechanism exhaustion is structurally blocked",
                "axisymmetric symmetry removes non-axisymmetric WBF and triad lanes",
                "the target has finite gates rather than open-ended route enumeration",
            ),
            missing_lemmas=(
                "AxisymmetricScalingDichotomy",
                "AxisymmetricClassExhaustionTheorem",
            ),
            closure_condition=(
                "Every axisymmetric-with-swirl blowup candidate is forced into "
                "one of the already closed gates G1 or G2."
            ),
            clay_relevance=(
                "Provides a genuine subcase theorem for Clay without claiming "
                "universal 3D exhaustion."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        TargetGate(
            gate_id="axisymmetric_swirl_global_assembly",
            target=TARGET,
            gate_name="axisymmetric_swirl_global_assembly",
            finite_gate=True,
            status="blocked_on_prior_gates",
            proof_objective=(
                "Assemble gates G1-G3 with standard local existence and BKM "
                "continuation into global regularity for axisymmetric NS with "
                "swirl."
            ),
            key_estimate_or_claim=(
                "No axisymmetric-with-swirl solution can realize finite-time "
                "BKM divergence once the large-Re, marginal, and exhaustion "
                "gates are closed."
            ),
            dependencies=(
                "Sprint130:PureDiffusionU1MaximumPrinciple",
                "Sprint131:HouLuoObstructionAssembly",
                "Sprint132:NSPartialRegularityFromObstructionTower",
                "G1:beta_gt_0_large_re_pde_control",
                "G2:beta_eq_0_marginal_case",
                "G3:axisymmetric_class_exhaustion",
            ),
            existing_support=(
                "local smooth continuation is governed by BKM-type criteria",
                "the axisymmetric swirl PDE has exact u1 and omega1 equations",
                "Sprint130-132 surfaces provide named support for the assembly map",
            ),
            missing_lemmas=(
                "AxisymmetricContinuationAssembly",
            ),
            closure_condition=(
                "G1, G2, and G3 are closed with compatible hypotheses and no "
                "remaining large-data axisymmetric exception."
            ),
            clay_relevance=(
                "Would be a major Clay-adjacent subcase, still strictly weaker "
                "than full 3D Navier-Stokes regularity."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "gate_id",
        "target",
        "gate_name",
        "finite_gate",
        "status",
        "proof_objective",
        "key_estimate_or_claim",
        "dependencies",
        "existing_support",
        "missing_lemmas",
        "closure_condition",
        "clay_relevance",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = dict(row)
            for key in ("dependencies", "existing_support", "missing_lemmas"):
                serializable[key] = "; ".join(serializable[key])
            writer.writerow(serializable)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    statuses: dict[str, int] = {}
    for row in rows:
        statuses[row["status"]] = statuses.get(row["status"], 0) + 1
    missing = sorted({lemma for row in rows for lemma in row["missing_lemmas"]})
    return {
        "contract": CONTRACT,
        "target": TARGET_ID,
        "target_name": TARGET,
        "target_defined": True,
        "axisymmetric_swirl_target_defined": True,
        "finite_gate_count": len(rows),
        "finite_gates": [row["gate_id"] for row in rows],
        "finite_gap_list": [row["gate_id"] for row in rows],
        "axisymmetric_gap_list": [row["gate_id"] for row in rows],
        "finite_gap_list_defined": True,
        "status_counts": statuses,
        "sprint_dependencies": SPRINT_DEPENDENCIES,
        "load_bearing_missing_lemmas": missing,
        "highest_alpha_next_lanes": [
            "NoLogAxisymmetricBiotSavartUniform",
            "LargeReAxisymmetricTransientControl",
            "MarginalScalingCaseAnalysis",
            "LargeScaleShearCannotForceBKM",
            "AxisymmetricScalingDichotomy",
            "AxisymmetricContinuationAssembly",
        ],
        "target_scope": "axisymmetric_NS_with_swirl_only",
        "axisymmetric_class_only": True,
        "mechanism_enumeration_claim": False,
        "full_3d_mechanism_exhaustion_claim": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
    }


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 133 Axisymmetric-With-Swirl Target",
        "",
        f"Contract: `{CONTRACT}`",
        f"Target: `{TARGET}`",
        "",
        "This artifact records a finite Clay-adjacent target, not full 3D "
        "Navier-Stokes regularity.  Full Clay promotion remains false.",
        "",
        "| Gate | Status | Missing lemmas | Prior support |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        missing = "; ".join(row["missing_lemmas"])
        support = "; ".join(row["dependencies"])
        lines.append(
            f"| `{row['gate_id']}` | `{row['status']}` | {missing} | {support} |"
        )
    lines.extend(
        [
            "",
            f"`finite_gate_count={summary['finite_gate_count']}`",
            f"`full_clay_ns_solved={str(summary['full_clay_ns_solved']).lower()}`",
            f"`clay_navier_stokes_promoted={str(summary['clay_navier_stokes_promoted']).lower()}`",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    out_dir = args.repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)

    write_json(out_dir / SUMMARY_NAME, summary)
    write_json(out_dir / ROWS_NAME, rows)
    write_csv(out_dir / CSV_NAME, rows)
    write_json(out_dir / GATES_JSON_NAME, rows)
    write_csv(out_dir / GATES_CSV_NAME, rows)
    (out_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")

    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
