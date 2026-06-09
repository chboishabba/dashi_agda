#!/usr/bin/env python3
"""Sprint 143 off-center crossing scenario classifier.

This deterministic toy-profile classifier records that the centered monotone
branch still has local support, while small off-center shoulders, boundary
layer crossings, annular crossings, and delayed crossings remain admissible
unless a separate theorem excludes them.

The artifact is a scenario ledger only.  It supplies no theorem, no proof, no
Agda promotion, no global barrier closure, and no Clay Navier-Stokes promotion.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint143_offcenter_crossing_scenarios"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint143_offcenter_crossing_scenarios")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 143
LANE = 3
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
PARENT_SAMPLERS = (
    "ns_sprint139_localized_kernel_sign_sampler",
    "ns_sprint142_kernel_sign_stress_sampler",
    "ns_sprint142_boundary_annulus_concavity_ledger",
)
BLOCKER = "OffCenterFirstCrossingExclusion"
TARGET_VARIABLE = "v=partial_z u1"
ROUTE_DECISION = "fail_closed_offcenter_crossings_admissible_no_promotion"
THEOREM_REQUIRED = "OffCenterBoundaryAnnularDelayedCrossingExclusion"

REQUIRED_ROW_IDS = {
    "centered_monotone_branch",
    "small_offcenter_shoulder",
    "boundary_layer_crossing",
    "annular_crossing",
    "delayed_crossing",
}
ADVERSE_ROW_IDS = REQUIRED_ROW_IDS - {"centered_monotone_branch"}


@dataclass(frozen=True)
class ToyScenario:
    row_id: str
    scenario_class: str
    crossing_geometry: str
    crossing_r: float
    crossing_z: float
    center_offset: float
    shoulder_amplitude: float
    annular_radius: float
    boundary_distance: float
    crossing_delay: float
    source_sign_model: str
    interpretation: str


@dataclass(frozen=True)
class ScenarioRow:
    row_id: str
    sprint: int
    lane: int
    contract: str
    program: str
    blocker_id: str
    target_variable: str
    scenario_class: str
    crossing_geometry: str
    v_crossing_geometry: str
    crossing_r: float
    crossing_z: float
    center_offset: float
    shoulder_amplitude: float
    annular_radius: float
    boundary_distance: float
    crossing_delay: float
    toy_profile_score: float
    crossing_order_score: float
    source_sign_model: str
    source_sign_hazard: str
    theorem_requirement: str
    centered_monotone_branch_supported: bool
    adverse_scenario: bool
    scenario_admissible_without_new_theorem: bool
    secondary_peak_exclusion_proved: bool
    global_barrier_closed: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool
    proof_status: str
    interpretation: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["no_proof_promotion"] = True
        row["promotion_decision"] = "hold_no_clay_promotion"
        row["missing_input"] = self.theorem_requirement
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def display_path(path: Path, repo_root: Path) -> str:
    try:
        return str(path.relative_to(repo_root))
    except ValueError:
        return str(path)


def clean(value: float) -> float:
    if abs(value) < 1.0e-14:
        return 0.0
    return float(f"{value:.12g}")


def scenarios() -> tuple[ToyScenario, ...]:
    return (
        ToyScenario(
            row_id="centered_monotone_branch",
            scenario_class="centered_support",
            crossing_geometry="centered_axis_monotone_first_crossing",
            crossing_r=1.0,
            crossing_z=0.0,
            center_offset=0.0,
            shoulder_amplitude=0.0,
            annular_radius=0.0,
            boundary_distance=1.0,
            crossing_delay=0.0,
            source_sign_model="locally_favorable_same_z_source",
            interpretation=(
                "The centered monotone branch is compatible with the local "
                "same-z support already sampled in Sprint 139/142."
            ),
        ),
        ToyScenario(
            row_id="small_offcenter_shoulder",
            scenario_class="offcenter_shoulder_admissible",
            crossing_geometry="small_offcenter_secondary_shoulder_first_crossing",
            crossing_r=1.08,
            crossing_z=0.06,
            center_offset=0.08,
            shoulder_amplitude=0.18,
            annular_radius=0.0,
            boundary_distance=0.74,
            crossing_delay=0.12,
            source_sign_model="mixed_local_and_shoulder_source",
            interpretation=(
                "A small shoulder can move the first v crossing away from the "
                "centered monotone branch unless secondary peaks are excluded."
            ),
        ),
        ToyScenario(
            row_id="boundary_layer_crossing",
            scenario_class="boundary_layer_admissible",
            crossing_geometry="near_boundary_layer_first_crossing",
            crossing_r=1.35,
            crossing_z=0.42,
            center_offset=0.35,
            shoulder_amplitude=0.09,
            annular_radius=0.0,
            boundary_distance=0.05,
            crossing_delay=0.2,
            source_sign_model="boundary_image_sensitive_source",
            interpretation=(
                "A boundary-layer crossing remains compatible with the toy "
                "ledger because boundary image/correction signs are unproved."
            ),
        ),
        ToyScenario(
            row_id="annular_crossing",
            scenario_class="annular_admissible",
            crossing_geometry="off_axis_annular_first_crossing",
            crossing_r=2.2,
            crossing_z=0.35,
            center_offset=1.2,
            shoulder_amplitude=0.24,
            annular_radius=2.2,
            boundary_distance=0.42,
            crossing_delay=0.18,
            source_sign_model="annular_source_sign_indefinite",
            interpretation=(
                "An annular crossing is not ruled out by centered monotonicity "
                "support without an annular shoulder exclusion theorem."
            ),
        ),
        ToyScenario(
            row_id="delayed_crossing",
            scenario_class="delayed_admissible",
            crossing_geometry="time_delayed_offcenter_first_crossing",
            crossing_r=1.18,
            crossing_z=0.28,
            center_offset=0.18,
            shoulder_amplitude=0.12,
            annular_radius=1.18,
            boundary_distance=0.5,
            crossing_delay=0.65,
            source_sign_model="delayed_transport_source_sign_uncertified",
            interpretation=(
                "A crossing delayed by transport can occur after the local "
                "centered window, so it needs a persistence/exclusion theorem."
            ),
        ),
    )


def toy_profile_score(case: ToyScenario) -> float:
    support = 1.0 - 0.55 * case.center_offset - 0.35 * case.crossing_delay
    support += 0.25 * (1.0 - min(case.boundary_distance, 1.0))
    support += 0.2 * case.shoulder_amplitude
    return clean(support)


def crossing_order_score(case: ToyScenario) -> float:
    order = case.center_offset + case.shoulder_amplitude + case.crossing_delay
    if case.annular_radius > 1.5:
        order += 0.35
    if case.boundary_distance < 0.1:
        order += 0.4
    return clean(order)


def classify_source_sign_hazard(case: ToyScenario) -> str:
    if case.row_id == "centered_monotone_branch":
        return "none_local_centered_support_only"
    hazards: list[str] = []
    if case.center_offset > 0.0 or case.shoulder_amplitude > 0.0:
        hazards.append("offcenter_secondary_peak")
    if case.boundary_distance < 0.1:
        hazards.append("boundary_image_sign")
    if case.annular_radius > 1.5:
        hazards.append("annular_kernel_sign")
    if case.crossing_delay > 0.4:
        hazards.append("delayed_transport_sign")
    return "+".join(hazards) if hazards else "uncertified_source_sign"


def theorem_requirement(case: ToyScenario) -> str:
    if case.row_id == "centered_monotone_branch":
        return "local_centered_monotone_support_not_global_theorem"
    if case.row_id == "small_offcenter_shoulder":
        return "SecondaryPeakExclusionForVCrossings"
    if case.row_id == "boundary_layer_crossing":
        return "BoundaryLayerCrossingExclusionOrSignedBoundaryKernelTheorem"
    if case.row_id == "annular_crossing":
        return "AnnularShoulderCrossingExclusionOrDominanceTheorem"
    if case.row_id == "delayed_crossing":
        return "DelayedCrossingPersistenceExclusionTheorem"
    return THEOREM_REQUIRED


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in scenarios():
        centered = case.row_id == "centered_monotone_branch"
        adverse = case.row_id in ADVERSE_ROW_IDS
        row = ScenarioRow(
            row_id=case.row_id,
            sprint=SPRINT,
            lane=LANE,
            contract=CONTRACT,
            program=PROGRAM,
            blocker_id=BLOCKER,
            target_variable=TARGET_VARIABLE,
            scenario_class=case.scenario_class,
            crossing_geometry=case.crossing_geometry,
            v_crossing_geometry=case.crossing_geometry,
            crossing_r=case.crossing_r,
            crossing_z=case.crossing_z,
            center_offset=case.center_offset,
            shoulder_amplitude=case.shoulder_amplitude,
            annular_radius=case.annular_radius,
            boundary_distance=case.boundary_distance,
            crossing_delay=case.crossing_delay,
            toy_profile_score=toy_profile_score(case),
            crossing_order_score=crossing_order_score(case),
            source_sign_model=case.source_sign_model,
            source_sign_hazard=classify_source_sign_hazard(case),
            theorem_requirement=theorem_requirement(case),
            centered_monotone_branch_supported=centered,
            adverse_scenario=adverse,
            scenario_admissible_without_new_theorem=True,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
            proof_status="no proof/promotion",
            interpretation=case.interpretation,
        ).as_row()
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = {row["row_id"] for row in rows}
    missing_rows = sorted(REQUIRED_ROW_IDS - row_ids)
    centered_rows = [row for row in rows if row["centered_monotone_branch_supported"]]
    adverse_rows = [row for row in rows if row["adverse_scenario"]]

    invariant_failures: list[str] = []
    if missing_rows:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_rows))
    if not centered_rows:
        invariant_failures.append("centered_support_missing")
    if {row["row_id"] for row in adverse_rows} != ADVERSE_ROW_IDS:
        invariant_failures.append("adverse_scenarios_missing")
    if any(not row["scenario_admissible_without_new_theorem"] for row in adverse_rows):
        invariant_failures.append("adverse_scenario_marked_inadmissible")
    if any(row["secondary_peak_exclusion_proved"] for row in rows):
        invariant_failures.append("secondary_peak_exclusion_proved")
    if any(row["global_barrier_closed"] for row in rows):
        invariant_failures.append("global_barrier_closed")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_navier_stokes_promoted")
    if any(row["claim_closed"] or row["claim_proved"] or row["claim_proven"] for row in rows):
        invariant_failures.append("claim_closure_or_proof_marked")

    invariants_passed = not invariant_failures
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "parent_samplers": list(PARENT_SAMPLERS),
        "blocker_id": BLOCKER,
        "target_variable": TARGET_VARIABLE,
        "route_decision": ROUTE_DECISION,
        "decision": ROUTE_DECISION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "centered_row_ids": [row["row_id"] for row in centered_rows],
        "adverse_row_ids": [row["row_id"] for row in adverse_rows],
        "theorem_required": THEOREM_REQUIRED,
        "theorem_supplied": False,
        "constants_required": True,
        "constants_available": False,
        "missing_constants": True,
        "has_centered_support": True,
        "has_adverse_scenarios": True,
        "secondary_peak_exclusion_proved": False,
        "global_barrier_closed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "artifact_complete": invariants_passed,
        "invariants_passed": invariants_passed,
        "invariant_failures": invariant_failures,
        "promotion_allowed": False,
        "promotion_decision": "hold_no_clay_promotion",
        "proof_status": "no proof/promotion",
        "conclusion": (
            "centered_monotone_branch_supported_but_offcenter_boundary_annular_"
            "delayed_crossings_remain_admissible_without_new_theorem"
        ),
        "control_card": {
            "O": (
                "Sprint 143 lane 3 emits only the off-center crossing scenario "
                "classifier script and its generated output artifacts."
            ),
            "R": (
                "Classify toy v=partial_z u1 crossing geometries: centered "
                "monotone support plus off-center, boundary-layer, annular, "
                "and delayed admissible scenarios."
            ),
            "C": (
                "Pure Python stdlib; deterministic fixed toy rows; JSON, CSV, "
                "Markdown; no docs, tests, or Agda edits."
            ),
            "S": (
                "Centered monotone branch is supported locally, but all adverse "
                "scenario classes remain admissible unless a theorem is supplied."
            ),
            "L": (
                "toy profile parameters -> v crossing geometry -> source sign "
                "hazard -> theorem requirement -> fail-closed summary flags."
            ),
            "P": (
                "Do not promote: no secondary-peak exclusion, no global barrier "
                "closure, and no Clay Navier-Stokes solution."
            ),
            "G": (
                "Require has_centered_support=true, has_adverse_scenarios=true, "
                "all proof/promotion flags false, artifact_complete=true, and "
                "invariants_passed=true."
            ),
            "F": (
                "Missing required rows, absent centered/adverse classes, any "
                "proof claim, missing constants closure, barrier closure, or "
                "Clay promotion fails closed."
            ),
        },
    }
    return summary


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    required_false = (
        "secondary_peak_exclusion_proved",
        "global_barrier_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    )
    if not summary["has_centered_support"]:
        raise ValueError("has_centered_support must be true")
    if not summary["has_adverse_scenarios"]:
        raise ValueError("has_adverse_scenarios must be true")
    for key in required_false:
        if summary[key]:
            raise ValueError(f"{key} must be false")
    if not summary["artifact_complete"] or not summary["invariants_passed"]:
        raise ValueError("artifact_complete and invariants_passed must be true")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))
    for row in rows:
        if row["claim_closed"] or row["claim_proved"] or row["claim_proven"]:
            raise ValueError(f"{row['row_id']} claims proof/closure")
        if row["global_barrier_closed"] or row["clay_navier_stokes_promoted"]:
            raise ValueError(f"{row['row_id']} claims barrier closure or promotion")


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty CSV")
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def format_value(value: Any) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, float):
        return f"{value:.12g}"
    return str(value)


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "geometry",
        "source sign hazard",
        "theorem requirement",
        "centered support",
        "adverse",
        "admissible",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append(
            "| "
            + " | ".join(
                (
                    f"`{row['row_id']}`",
                    f"`{row['v_crossing_geometry']}`",
                    f"`{row['source_sign_hazard']}`",
                    f"`{row['theorem_requirement']}`",
                    format_value(row["centered_monotone_branch_supported"]),
                    format_value(row["adverse_scenario"]),
                    format_value(row["scenario_admissible_without_new_theorem"]),
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 143 Off-Center Crossing Scenarios",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Blocker: `{BLOCKER}`",
        f"- Target variable: `{TARGET_VARIABLE}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Has centered support: `{str(summary['has_centered_support']).lower()}`",
        f"- Has adverse scenarios: `{str(summary['has_adverse_scenarios']).lower()}`",
        f"- Secondary peak exclusion proved: `{str(summary['secondary_peak_exclusion_proved']).lower()}`",
        f"- Global barrier closed: `{str(summary['global_barrier_closed']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        "",
        "## Rows",
        "",
        markdown_table(rows),
        "",
        "## Conclusion",
        "",
        (
            "The centered monotone branch is supported by this toy-profile "
            "classifier, but small off-center shoulder, boundary layer crossing, "
            "annular crossing, and delayed crossing rows remain admissible unless "
            "the listed theorem requirements are supplied."
        ),
        "",
        "## Row Notes",
        "",
    ]
    for row in rows:
        lines.append(f"- `{row['row_id']}`: {row['interpretation']}")
    lines.extend(["", "## Control Card", ""])
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    return "\n".join(lines) + "\n"


def emit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    resolved_out_dir = out_dir if out_dir.is_absolute() else repo_root / out_dir
    resolved_out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate(summary, rows)

    rows_json_path = resolved_out_dir / ROWS_JSON_NAME
    rows_csv_path = resolved_out_dir / ROWS_CSV_NAME
    report_path = resolved_out_dir / REPORT_NAME
    summary_path = resolved_out_dir / SUMMARY_NAME

    write_json(rows_json_path, rows)
    write_csv(rows_csv_path, rows)
    report_path.write_text(build_report(summary, rows), encoding="utf-8")

    summary["artifacts"] = {
        "summary_json": display_path(summary_path, repo_root),
        "rows_json": display_path(rows_json_path, repo_root),
        "rows_csv": display_path(rows_csv_path, repo_root),
        "markdown": display_path(report_path, repo_root),
    }
    write_json(summary_path, summary)

    summary["artifact_hashes"] = {
        "summary_json": file_sha256(summary_path),
        "rows_json": file_sha256(rows_json_path),
        "rows_csv": file_sha256(rows_csv_path),
        "markdown": file_sha256(report_path),
    }
    write_json(summary_path, summary)
    return summary


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    summary = emit(repo_root=repo_root, out_dir=args.out_dir)
    print(
        json.dumps(
            {
                "artifact_complete": summary["artifact_complete"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "contract": summary["contract"],
                "global_barrier_closed": summary["global_barrier_closed"],
                "has_adverse_scenarios": summary["has_adverse_scenarios"],
                "has_centered_support": summary["has_centered_support"],
                "invariants_passed": summary["invariants_passed"],
                "out_dir": summary["artifacts"]["summary_json"].rsplit("/", 1)[0],
                "secondary_peak_exclusion_proved": summary[
                    "secondary_peak_exclusion_proved"
                ],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
