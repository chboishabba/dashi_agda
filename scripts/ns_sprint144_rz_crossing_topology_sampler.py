#!/usr/bin/env python3
"""Sprint 144 r-z crossing topology sampler.

This deterministic toy sampler records that a scalar zero count on one fixed
z-line can have local support while still failing to control the first positive
crossing in the full coupled r-z barrier geometry.

The artifact is intentionally fail-closed. It proves no coupled zero-number
theorem, no secondary peak exclusion theorem, no global barrier closure, and no
Clay Navier-Stokes promotion.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import shutil
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint144_rz_crossing_topology_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint144_rz_crossing_topology_sampler")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 144
LANE = 3
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_VARIABLE = "v = partial_z u1"
BLOCKER = "RZFirstPositiveCrossingTopology"
DECISION = "fail_closed_fixed_z_line_zero_count_insufficient"
MISSING_THEOREM = "CoupledRZZeroNumberFirstPositiveCrossingTheorem"

REQUIRED_SCENARIOS = {
    "fixed_line_decrease_support",
    "radial_bypass_crossing",
    "annular_loop_crossing",
    "saddle_node_pair_creation",
    "boundary_interval_reentry",
}
ADVERSE_SCENARIOS = REQUIRED_SCENARIOS - {"fixed_line_decrease_support"}


@dataclass(frozen=True)
class TopologyCase:
    row_id: str
    topology_class: str
    fixed_z_line: float
    fixed_line_initial_zero_count: int
    fixed_line_final_zero_count: int
    first_positive_r: float
    first_positive_z: float
    radial_excursion: float
    annular_winding: int
    boundary_touch_count: int
    created_zero_pairs: int
    scalar_support: bool
    rz_adverse_topology: bool
    mechanism: str
    missing_input: str
    interpretation: str


@dataclass(frozen=True)
class TopologyRow:
    row_id: str
    sprint: int
    lane: int
    contract: str
    program: str
    blocker_id: str
    target_variable: str
    topology_class: str
    fixed_z_line: float
    fixed_line_initial_zero_count: int
    fixed_line_final_zero_count: int
    fixed_line_zero_count_delta: int
    fixed_line_zero_count_decreased: bool
    first_positive_r: float
    first_positive_z: float
    radial_excursion: float
    annular_winding: int
    boundary_touch_count: int
    created_zero_pairs: int
    rz_complexity_score: float
    scalar_support: bool
    rz_adverse_topology: bool
    fixed_line_controls_full_rz_first_crossing: bool
    fixed_line_zero_count_sufficient: bool
    coupled_zero_number_theorem_proved: bool
    secondary_peak_exclusion_proved: bool
    global_barrier_closed: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool
    mechanism: str
    missing_input: str
    proof_status: str
    interpretation: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["no_proof_promotion"] = True
        row["promotion_decision"] = "hold_no_clay_promotion"
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


def cases() -> tuple[TopologyCase, ...]:
    return (
        TopologyCase(
            row_id="fixed_line_decrease_support",
            topology_class="scalar_fixed_line_support",
            fixed_z_line=0.0,
            fixed_line_initial_zero_count=4,
            fixed_line_final_zero_count=2,
            first_positive_r=1.0,
            first_positive_z=0.0,
            radial_excursion=0.0,
            annular_winding=0,
            boundary_touch_count=0,
            created_zero_pairs=0,
            scalar_support=True,
            rz_adverse_topology=False,
            mechanism="fixed_z_line_zero_count_decreases_in_scalar_slice",
            missing_input="full_rz_crossing_control_not_needed_for_support_row",
            interpretation=(
                "The fixed z-line scalar slice can show a decreasing zero count; "
                "this records local scalar support only."
            ),
        ),
        TopologyCase(
            row_id="radial_bypass_crossing",
            topology_class="radial_bypass",
            fixed_z_line=0.0,
            fixed_line_initial_zero_count=4,
            fixed_line_final_zero_count=2,
            first_positive_r=1.42,
            first_positive_z=0.18,
            radial_excursion=0.42,
            annular_winding=0,
            boundary_touch_count=0,
            created_zero_pairs=0,
            scalar_support=True,
            rz_adverse_topology=True,
            mechanism="positive_crossing_reaches_rz_domain_by_radial_bypass",
            missing_input="RadialBypassFirstCrossingExclusion",
            interpretation=(
                "The monitored fixed line improves, while the first positive "
                "crossing enters through a radial path outside that line."
            ),
        ),
        TopologyCase(
            row_id="annular_loop_crossing",
            topology_class="annular_loop",
            fixed_z_line=0.0,
            fixed_line_initial_zero_count=4,
            fixed_line_final_zero_count=2,
            first_positive_r=2.15,
            first_positive_z=0.31,
            radial_excursion=1.15,
            annular_winding=1,
            boundary_touch_count=0,
            created_zero_pairs=0,
            scalar_support=True,
            rz_adverse_topology=True,
            mechanism="off_axis_annular_loop_avoids_fixed_slice_count",
            missing_input="AnnularLoopCrossingExclusion",
            interpretation=(
                "An annular loop can carry the first positive crossing around "
                "the controlled fixed z-line."
            ),
        ),
        TopologyCase(
            row_id="saddle_node_pair_creation",
            topology_class="saddle_node_zero_pair",
            fixed_z_line=0.0,
            fixed_line_initial_zero_count=4,
            fixed_line_final_zero_count=2,
            first_positive_r=1.26,
            first_positive_z=-0.22,
            radial_excursion=0.26,
            annular_winding=0,
            boundary_touch_count=0,
            created_zero_pairs=1,
            scalar_support=True,
            rz_adverse_topology=True,
            mechanism="rz_saddle_node_pair_creates_off_line_positive_region",
            missing_input="CoupledRZSaddleNodePairExclusion",
            interpretation=(
                "A coupled r-z saddle-node pair can create an off-line positive "
                "region without increasing the chosen scalar slice count."
            ),
        ),
        TopologyCase(
            row_id="boundary_interval_reentry",
            topology_class="boundary_reentry",
            fixed_z_line=0.0,
            fixed_line_initial_zero_count=4,
            fixed_line_final_zero_count=2,
            first_positive_r=1.66,
            first_positive_z=0.47,
            radial_excursion=0.66,
            annular_winding=0,
            boundary_touch_count=2,
            created_zero_pairs=0,
            scalar_support=True,
            rz_adverse_topology=True,
            mechanism="crossing_exits_and_reenters_through_boundary_interval",
            missing_input="BoundaryIntervalReentryExclusion",
            interpretation=(
                "Boundary interval reentry leaves the fixed-line zero count "
                "compatible with an uncontrolled full-domain first crossing."
            ),
        ),
    )


def rz_complexity_score(case: TopologyCase) -> float:
    score = case.radial_excursion
    score += 0.6 * case.annular_winding
    score += 0.45 * case.created_zero_pairs
    score += 0.3 * case.boundary_touch_count
    score += abs(case.first_positive_z - case.fixed_z_line)
    return clean(score)


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in cases():
        delta = case.fixed_line_final_zero_count - case.fixed_line_initial_zero_count
        row = TopologyRow(
            row_id=case.row_id,
            sprint=SPRINT,
            lane=LANE,
            contract=CONTRACT,
            program=PROGRAM,
            blocker_id=BLOCKER,
            target_variable=TARGET_VARIABLE,
            topology_class=case.topology_class,
            fixed_z_line=case.fixed_z_line,
            fixed_line_initial_zero_count=case.fixed_line_initial_zero_count,
            fixed_line_final_zero_count=case.fixed_line_final_zero_count,
            fixed_line_zero_count_delta=delta,
            fixed_line_zero_count_decreased=delta < 0,
            first_positive_r=case.first_positive_r,
            first_positive_z=case.first_positive_z,
            radial_excursion=case.radial_excursion,
            annular_winding=case.annular_winding,
            boundary_touch_count=case.boundary_touch_count,
            created_zero_pairs=case.created_zero_pairs,
            rz_complexity_score=rz_complexity_score(case),
            scalar_support=case.scalar_support,
            rz_adverse_topology=case.rz_adverse_topology,
            fixed_line_controls_full_rz_first_crossing=False,
            fixed_line_zero_count_sufficient=False,
            coupled_zero_number_theorem_proved=False,
            secondary_peak_exclusion_proved=False,
            global_barrier_closed=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
            mechanism=case.mechanism,
            missing_input=case.missing_input,
            proof_status="no proof/promotion",
            interpretation=case.interpretation,
        ).as_row()
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = {row["row_id"] for row in rows}
    missing = sorted(REQUIRED_SCENARIOS - row_ids)
    extra = sorted(row_ids - REQUIRED_SCENARIOS)
    scalar_support_rows = [row for row in rows if row["scalar_support"]]
    adverse_rows = [row for row in rows if row["rz_adverse_topology"]]

    failures: list[str] = []
    if missing:
        failures.append("missing_required_scenarios:" + ",".join(missing))
    if extra:
        failures.append("unexpected_scenarios:" + ",".join(extra))
    if not scalar_support_rows:
        failures.append("scalar_support_missing")
    if {row["row_id"] for row in adverse_rows} != ADVERSE_SCENARIOS:
        failures.append("rz_adverse_topologies_missing")
    if any(not row["fixed_line_zero_count_decreased"] for row in rows):
        failures.append("fixed_line_decrease_not_recorded")
    if any(row["fixed_line_zero_count_sufficient"] for row in rows):
        failures.append("fixed_line_zero_count_marked_sufficient")
    if any(row["coupled_zero_number_theorem_proved"] for row in rows):
        failures.append("coupled_zero_number_theorem_marked_proved")
    if any(row["secondary_peak_exclusion_proved"] for row in rows):
        failures.append("secondary_peak_exclusion_marked_proved")
    if any(row["global_barrier_closed"] for row in rows):
        failures.append("global_barrier_marked_closed")
    if any(row["full_clay_ns_solved"] for row in rows):
        failures.append("full_clay_ns_marked_solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        failures.append("clay_promotion_detected")
    if any(row["claim_closed"] or row["claim_proved"] or row["claim_proven"] for row in rows):
        failures.append("claim_closure_or_proof_detected")

    invariants_passed = not failures
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "blocker_id": BLOCKER,
        "target_variable": TARGET_VARIABLE,
        "missing_theorem": MISSING_THEOREM,
        "row_count": len(rows),
        "required_scenarios": sorted(REQUIRED_SCENARIOS),
        "observed_scenarios": [row["row_id"] for row in rows],
        "scalar_support_row_ids": [row["row_id"] for row in scalar_support_rows],
        "rz_adverse_topology_row_ids": [row["row_id"] for row in adverse_rows],
        "has_scalar_support": True,
        "has_rz_adverse_topologies": True,
        "fixed_line_zero_count_sufficient": False,
        "coupled_zero_number_theorem_proved": False,
        "secondary_peak_exclusion_proved": False,
        "global_barrier_closed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "artifact_complete": invariants_passed,
        "invariants_passed": invariants_passed,
        "invariant_failures": failures,
        "promotion_allowed": False,
        "promotion_decision": "hold_no_clay_promotion",
        "proof_status": "no proof/promotion",
        "conclusion": (
            "fixed_z_line_scalar_zero_count_can_decrease_while_full_rz_first_"
            "positive_crossing_remains_uncontrolled"
        ),
        "control_card": {
            "O": (
                "Sprint 144 lane 3 owns only the r-z crossing topology sampler "
                "script and its generated output artifacts."
            ),
            "R": (
                "Show by deterministic toy scenarios that fixed z-line scalar "
                "zero counts do not control full r-z first positive crossings."
            ),
            "C": (
                "Pure Python stdlib; fixed rows; JSON, CSV, Markdown; robust "
                "temporary output directory replacement; no docs/tests/Agda edits."
            ),
            "S": (
                "Scalar fixed-line decrease is recorded, while radial bypass, "
                "annular loop, saddle-node pair, and boundary reentry topologies "
                "remain adverse."
            ),
            "L": (
                "Toy topology parameters -> fixed-line zero-count delta -> full "
                "r-z first crossing geometry -> missing theorem -> fail-closed flags."
            ),
            "P": (
                "Do not promote: no coupled zero-number theorem, no secondary "
                "peak exclusion, no global barrier closure, and no Clay solution."
            ),
            "G": (
                "Require has_scalar_support=true, has_rz_adverse_topologies=true, "
                "all proof/promotion flags false, artifact_complete=true, and "
                "invariants_passed=true."
            ),
            "F": (
                "Any missing scenario, any sufficient fixed-line claim, any theorem "
                "proof, barrier closure, or Clay promotion fails the artifact."
            ),
        },
    }
    summary["summary_hash"] = stable_hash(
        {key: value for key, value in summary.items() if key != "summary_hash"}
    )
    return summary


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    errors: list[str] = []
    required_false = (
        "fixed_line_zero_count_sufficient",
        "coupled_zero_number_theorem_proved",
        "secondary_peak_exclusion_proved",
        "global_barrier_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    )
    if not summary["has_scalar_support"]:
        errors.append("has_scalar_support must be true")
    if not summary["has_rz_adverse_topologies"]:
        errors.append("has_rz_adverse_topologies must be true")
    for key in required_false:
        if summary[key]:
            errors.append(f"{key} must be false")
    if not summary["artifact_complete"] or not summary["invariants_passed"]:
        errors.append("artifact_complete and invariants_passed must be true")
    if summary["invariant_failures"]:
        errors.extend(summary["invariant_failures"])
    for row in rows:
        if row["fixed_line_zero_count_sufficient"]:
            errors.append(f"{row['row_id']} marked fixed-line count sufficient")
        if row["claim_closed"] or row["claim_proved"] or row["claim_proven"]:
            errors.append(f"{row['row_id']} claims proof/closure")
        if row["global_barrier_closed"] or row["clay_navier_stokes_promoted"]:
            errors.append(f"{row['row_id']} claims barrier closure or promotion")
    if errors:
        raise ValueError("; ".join(errors))


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


def format_bool(value: bool) -> str:
    return str(value).lower()


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "topology",
        "fixed delta",
        "first r",
        "first z",
        "scalar support",
        "r-z adverse",
        "sufficient",
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
                    f"`{row['topology_class']}`",
                    str(row["fixed_line_zero_count_delta"]),
                    f"{row['first_positive_r']:.12g}",
                    f"{row['first_positive_z']:.12g}",
                    format_bool(row["scalar_support"]),
                    format_bool(row["rz_adverse_topology"]),
                    format_bool(row["fixed_line_zero_count_sufficient"]),
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 144 R-Z Crossing Topology Sampler",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Decision: `{summary['decision']}`",
        f"- Target variable: `{TARGET_VARIABLE}`",
        f"- Missing theorem: `{MISSING_THEOREM}`",
        f"- Has scalar support: `{format_bool(summary['has_scalar_support'])}`",
        (
            "- Has r-z adverse topologies: "
            f"`{format_bool(summary['has_rz_adverse_topologies'])}`"
        ),
        (
            "- Fixed-line zero count sufficient: "
            f"`{format_bool(summary['fixed_line_zero_count_sufficient'])}`"
        ),
        (
            "- Coupled zero-number theorem proved: "
            f"`{format_bool(summary['coupled_zero_number_theorem_proved'])}`"
        ),
        (
            "- Secondary peak exclusion proved: "
            f"`{format_bool(summary['secondary_peak_exclusion_proved'])}`"
        ),
        f"- Global barrier closed: `{format_bool(summary['global_barrier_closed'])}`",
        f"- Full Clay NS solved: `{format_bool(summary['full_clay_ns_solved'])}`",
        (
            "- Clay Navier-Stokes promoted: "
            f"`{format_bool(summary['clay_navier_stokes_promoted'])}`"
        ),
        f"- Artifact complete: `{format_bool(summary['artifact_complete'])}`",
        f"- Invariants passed: `{format_bool(summary['invariants_passed'])}`",
        "",
        "## Rows",
        "",
        markdown_table(rows),
        "",
        "## Conclusion",
        "",
        (
            "The fixed z-line scalar zero count can decrease in every toy row, "
            "but this does not control the full r-z first positive crossing. "
            "Radial bypass, annular loop, saddle-node pair creation, and "
            "boundary interval reentry remain adverse topologies without the "
            "missing coupled theorem."
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


def replace_output_dir(tmp_dir: Path, out_dir: Path) -> None:
    parent = out_dir.parent
    parent.mkdir(parents=True, exist_ok=True)
    backup_dir = parent / f".{out_dir.name}.bak"
    if backup_dir.exists():
        shutil.rmtree(backup_dir)
    if out_dir.exists():
        out_dir.replace(backup_dir)
    try:
        tmp_dir.replace(out_dir)
    except Exception:
        if out_dir.exists():
            shutil.rmtree(out_dir)
        if backup_dir.exists():
            backup_dir.replace(out_dir)
        raise
    if backup_dir.exists():
        shutil.rmtree(backup_dir)


def emit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    resolved_out_dir = out_dir if out_dir.is_absolute() else repo_root / out_dir
    parent = resolved_out_dir.parent
    parent.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate(summary, rows)

    with tempfile.TemporaryDirectory(
        prefix=f".{CONTRACT}.", dir=str(parent)
    ) as tmp_name:
        tmp_dir = Path(tmp_name)
        summary_path = tmp_dir / SUMMARY_NAME
        rows_json_path = tmp_dir / ROWS_JSON_NAME
        rows_csv_path = tmp_dir / ROWS_CSV_NAME
        report_path = tmp_dir / REPORT_NAME

        write_json(rows_json_path, rows)
        write_csv(rows_csv_path, rows)
        report_path.write_text(build_report(summary, rows), encoding="utf-8")

        final_summary_path = resolved_out_dir / SUMMARY_NAME
        final_rows_json_path = resolved_out_dir / ROWS_JSON_NAME
        final_rows_csv_path = resolved_out_dir / ROWS_CSV_NAME
        final_report_path = resolved_out_dir / REPORT_NAME
        summary["artifacts"] = {
            "summary_json": display_path(final_summary_path, repo_root),
            "rows_json": display_path(final_rows_json_path, repo_root),
            "rows_csv": display_path(final_rows_csv_path, repo_root),
            "markdown": display_path(final_report_path, repo_root),
        }
        write_json(summary_path, summary)
        summary["artifact_hashes"] = {
            "summary_json": file_sha256(summary_path),
            "rows_json": file_sha256(rows_json_path),
            "rows_csv": file_sha256(rows_csv_path),
            "markdown": file_sha256(report_path),
        }
        write_json(summary_path, summary)

        replace_output_dir(tmp_dir, resolved_out_dir)

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
                "coupled_zero_number_theorem_proved": summary[
                    "coupled_zero_number_theorem_proved"
                ],
                "fixed_line_zero_count_sufficient": summary[
                    "fixed_line_zero_count_sufficient"
                ],
                "global_barrier_closed": summary["global_barrier_closed"],
                "has_rz_adverse_topologies": summary["has_rz_adverse_topologies"],
                "has_scalar_support": summary["has_scalar_support"],
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
