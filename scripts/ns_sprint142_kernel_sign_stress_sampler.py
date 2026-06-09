#!/usr/bin/env python3
"""Sprint 142 kernel-sign stress sampler for partial_z^2 psi1.

This deterministic sampler sharpens the Sprint 139 localized-kernel ledger.
It samples favorable local same-z rows alongside adverse or nonlocal rows:
axial offset, annular source, boundary image, and far-tail geometries.  The
output is a fail-closed diagnostic artifact only.  It does not prove a uniform
global negative sign theorem for partial_z^2 psi1, does not solve Clay
Navier-Stokes, and does not emit a promotion.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint142_kernel_sign_stress_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint142_kernel_sign_stress_sampler")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 142
LANE = 3
BLOCKER = "GlobalNegativeKernelSignForPartialZ2Psi1"
PARENT_LEDGER = "ns_sprint139_localized_kernel_sign_sampler"
ROUTE_DECISION = "fail_closed_no_uniform_global_negative_sign_theorem"
KERNEL_MODEL = "5d_radial_green_partial_z2_axisymmetric_S3_average"

VARIABLES = {
    "psi1": "psi^theta / r",
    "omega1": "omega^theta / r",
    "Ltilde": "partial_r^2 + (3/r) partial_r + partial_z^2",
    "elliptic_relation": "-Ltilde psi1 = omega1",
    "sampled_kernel": "partial_z^2 |(y,z)-(y_prime,z_prime)|^-3 averaged over S^3 angle",
}

ANGLE_STEPS = 721
EPSILON2 = 1.0e-8
SIGN_TOLERANCE = 1.0e-9


@dataclass(frozen=True)
class SampleCase:
    row_id: str
    geometry_class: str
    evaluation_r: float
    evaluation_z: float
    source_r: float
    source_z: float
    source_weight: float
    expected_role: str
    source_description: str
    interpretation: str


@dataclass(frozen=True)
class StressRow:
    row_id: str
    sprint: int
    lane: int
    contract: str
    blocker_id: str
    parent_ledger: str
    geometry_class: str
    evaluation_r: float
    evaluation_z: float
    source_r: float
    source_z: float
    source_weight: float
    angular_steps: int
    kernel_average: float
    radial_measure_weight: float
    weighted_contribution: float
    min_point_kernel: float
    max_point_kernel: float
    sign_classification: str
    favorable_local_same_z_row: bool
    adverse_or_nonlocal_row: bool
    supports_local_negative_sign: bool
    obstructs_uniform_global_negative_sign: bool
    expected_role: str
    source_description: str
    interpretation: str
    uniform_global_negative_sign_theorem_proved: bool
    global_concavity_proved: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["blocked_claim"] = "uniform_global_negative_sign_for_partial_z2_psi1"
        row["blocker_status"] = "open"
        row["missing_input"] = (
            "global signed kernel dominance theorem covering axial offsets, "
            "annuli, boundary images, and far-tail sources"
        )
        row["constants_absent"] = True
        row["simultaneous_theorem_absent"] = True
        row["global_barrier_closed"] = False
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["row_hash"] = stable_hash(row)
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def clean(value: float) -> float:
    if abs(value) < 1.0e-14:
        return 0.0
    return float(f"{value:.15g}")


def sample_cases() -> tuple[SampleCase, ...]:
    return (
        SampleCase(
            row_id="favorable_local_same_z_inner_radial_patch",
            geometry_class="favorable_local_same_z",
            evaluation_r=1.0,
            evaluation_z=0.0,
            source_r=0.84,
            source_z=0.0,
            source_weight=1.0,
            expected_role="favorable_local_same_z_row",
            source_description="nearby same-z positive omega1 radial patch",
            interpretation=(
                "Same-z local radial separation gives a negative partial_z^2 "
                "kernel sample, preserving the Sprint 139 localized support."
            ),
        ),
        SampleCase(
            row_id="favorable_local_same_z_outer_radial_patch",
            geometry_class="favorable_local_same_z",
            evaluation_r=1.0,
            evaluation_z=0.0,
            source_r=1.22,
            source_z=0.0,
            source_weight=1.0,
            expected_role="favorable_local_same_z_row",
            source_description="nearby same-z outer radial shell",
            interpretation=(
                "A second same-z local row remains favorable, so the sampler "
                "does not erase useful localized-kernel evidence."
            ),
        ),
        SampleCase(
            row_id="adverse_axial_offset_same_radius",
            geometry_class="adverse_axial_offset",
            evaluation_r=1.0,
            evaluation_z=0.0,
            source_r=1.0,
            source_z=0.34,
            source_weight=1.0,
            expected_role="adverse_row",
            source_description="same-radius source displaced in z",
            interpretation=(
                "Axial offset can flip the sampled sign, blocking a theorem "
                "based only on local radial intuition."
            ),
        ),
        SampleCase(
            row_id="adverse_annular_source_axial_offset",
            geometry_class="adverse_annular_source",
            evaluation_r=1.0,
            evaluation_z=0.0,
            source_r=2.1,
            source_z=1.55,
            source_weight=1.0,
            expected_role="adverse_nonlocal_row",
            source_description="off-axis annular source with axial separation",
            interpretation=(
                "An annular source away from the local patch has the wrong "
                "sign, so same-z favorable samples cannot globalize."
            ),
        ),
        SampleCase(
            row_id="adverse_boundary_image_reflection",
            geometry_class="adverse_boundary_image",
            evaluation_r=1.0,
            evaluation_z=0.18,
            source_r=1.35,
            source_z=-0.82,
            source_weight=-0.65,
            expected_role="adverse_boundary_image_row",
            source_description="method-of-images style reflected source with opposite image weight",
            interpretation=(
                "A boundary-image contribution changes the signed balance; "
                "the sampler records it as a boundary-sensitive obstruction."
            ),
        ),
        SampleCase(
            row_id="adverse_far_tail_axial_column",
            geometry_class="adverse_far_tail",
            evaluation_r=1.0,
            evaluation_z=0.0,
            source_r=0.52,
            source_z=2.35,
            source_weight=1.0,
            expected_role="adverse_far_tail_row",
            source_description="far axial tail near the axis",
            interpretation=(
                "A far-tail axial column remains sign-adverse at the interior "
                "evaluation point, keeping the global kernel theorem open."
            ),
        ),
    )


REQUIRED_ROW_IDS = {case.row_id for case in sample_cases()}
REQUIRED_ADVERSE_CLASSES = {
    "adverse_axial_offset",
    "adverse_annular_source",
    "adverse_boundary_image",
    "adverse_far_tail",
}


def second_z_kernel(dy2: float, dz: float) -> float:
    rho2 = dy2 + dz * dz + EPSILON2
    return 3.0 * (4.0 * dz * dz - dy2) / (rho2 ** 3.5)


def angular_average_kernel(
    evaluation_r: float,
    evaluation_z: float,
    source_r: float,
    source_z: float,
) -> tuple[float, float, float]:
    if ANGLE_STEPS < 3 or ANGLE_STEPS % 2 == 0:
        raise ValueError("ANGLE_STEPS must be odd and at least 3")

    dz = evaluation_z - source_z
    h = math.pi / (ANGLE_STEPS - 1)
    weighted_total = 0.0
    weight_total = 0.0
    min_kernel = math.inf
    max_kernel = -math.inf

    for index in range(ANGLE_STEPS):
        theta = index * h
        angular_weight = math.sin(theta) ** 2
        simpson_weight = 1 if index in (0, ANGLE_STEPS - 1) else (4 if index % 2 else 2)
        dy2 = (
            evaluation_r * evaluation_r
            + source_r * source_r
            - 2.0 * evaluation_r * source_r * math.cos(theta)
        )
        kernel = second_z_kernel(dy2=dy2, dz=dz)
        weighted_total += simpson_weight * angular_weight * kernel
        weight_total += simpson_weight * angular_weight
        min_kernel = min(min_kernel, kernel)
        max_kernel = max(max_kernel, kernel)

    if weight_total <= 0.0:
        raise ValueError("angular quadrature produced zero weight")
    return weighted_total / weight_total, min_kernel, max_kernel


def classify_sign(value: float) -> str:
    if value < -SIGN_TOLERANCE:
        return "negative_favorable_for_local_concavity"
    if value > SIGN_TOLERANCE:
        return "positive_adverse_to_negative_sign_theorem"
    return "near_zero_inconclusive"


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case in sample_cases():
        kernel_average, min_kernel, max_kernel = angular_average_kernel(
            evaluation_r=case.evaluation_r,
            evaluation_z=case.evaluation_z,
            source_r=case.source_r,
            source_z=case.source_z,
        )
        radial_measure_weight = case.source_r ** 3
        weighted_contribution = kernel_average * case.source_weight * radial_measure_weight
        sign_classification = classify_sign(weighted_contribution)
        favorable = (
            case.geometry_class == "favorable_local_same_z"
            and sign_classification == "negative_favorable_for_local_concavity"
        )
        adverse_or_nonlocal = case.geometry_class in REQUIRED_ADVERSE_CLASSES
        obstructs = adverse_or_nonlocal or sign_classification != "negative_favorable_for_local_concavity"
        row = StressRow(
            row_id=case.row_id,
            sprint=SPRINT,
            lane=LANE,
            contract=CONTRACT,
            blocker_id=BLOCKER,
            parent_ledger=PARENT_LEDGER,
            geometry_class=case.geometry_class,
            evaluation_r=case.evaluation_r,
            evaluation_z=case.evaluation_z,
            source_r=case.source_r,
            source_z=case.source_z,
            source_weight=case.source_weight,
            angular_steps=ANGLE_STEPS,
            kernel_average=clean(kernel_average),
            radial_measure_weight=clean(radial_measure_weight),
            weighted_contribution=clean(weighted_contribution),
            min_point_kernel=clean(min_kernel),
            max_point_kernel=clean(max_kernel),
            sign_classification=sign_classification,
            favorable_local_same_z_row=favorable,
            adverse_or_nonlocal_row=adverse_or_nonlocal,
            supports_local_negative_sign=favorable,
            obstructs_uniform_global_negative_sign=obstructs,
            expected_role=case.expected_role,
            source_description=case.source_description,
            interpretation=case.interpretation,
            uniform_global_negative_sign_theorem_proved=False,
            global_concavity_proved=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ).as_row()
        rows.append(row)
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = {str(row["row_id"]) for row in rows}
    missing_rows = sorted(REQUIRED_ROW_IDS.difference(row_ids))
    favorable_rows = [row for row in rows if row["favorable_local_same_z_row"]]
    adverse_rows = [row for row in rows if row["adverse_or_nonlocal_row"]]
    adverse_classes = {str(row["geometry_class"]) for row in adverse_rows}
    positive_adverse_rows = [
        row
        for row in adverse_rows
        if row["sign_classification"] == "positive_adverse_to_negative_sign_theorem"
    ]
    negative_adverse_rows = [
        row
        for row in adverse_rows
        if row["sign_classification"] == "negative_favorable_for_local_concavity"
    ]
    obstruction_rows = [
        row for row in rows if row["obstructs_uniform_global_negative_sign"]
    ]

    invariant_failures: list[str] = []
    if missing_rows:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_rows))
    if not favorable_rows:
        invariant_failures.append("has_favorable_rows_false")
    if not adverse_rows:
        invariant_failures.append("has_adverse_rows_false")
    missing_adverse_classes = sorted(REQUIRED_ADVERSE_CLASSES.difference(adverse_classes))
    if missing_adverse_classes:
        invariant_failures.append(
            "missing_adverse_classes:" + ",".join(missing_adverse_classes)
        )
    if not positive_adverse_rows:
        invariant_failures.append("positive_adverse_rows_missing")
    if not negative_adverse_rows:
        invariant_failures.append("adverse_same_sign_counterbalance_missing")
    if any(row["global_concavity_proved"] for row in rows):
        invariant_failures.append("global_concavity_proof_claimed")
    if any(row["uniform_global_negative_sign_theorem_proved"] for row in rows):
        invariant_failures.append("uniform_global_negative_sign_theorem_claimed")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_claimed")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_claimed")

    invariants_passed = not invariant_failures
    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "blocker_id": BLOCKER,
        "parent_ledger": PARENT_LEDGER,
        "kernel_model": KERNEL_MODEL,
        "variables": VARIABLES,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "required_adverse_classes": sorted(REQUIRED_ADVERSE_CLASSES),
        "angular_steps": ANGLE_STEPS,
        "epsilon2": EPSILON2,
        "sign_tolerance": SIGN_TOLERANCE,
        "route_decision": ROUTE_DECISION,
        "decision": ROUTE_DECISION,
        "fail_closed": True,
        "has_favorable_rows": bool(favorable_rows),
        "has_adverse_rows": bool(adverse_rows),
        "favorable_row_ids": [row["row_id"] for row in favorable_rows],
        "adverse_row_ids": [row["row_id"] for row in adverse_rows],
        "positive_adverse_row_ids": [row["row_id"] for row in positive_adverse_rows],
        "negative_adverse_row_ids": [row["row_id"] for row in negative_adverse_rows],
        "obstruction_row_ids": [row["row_id"] for row in obstruction_rows],
        "uniform_global_negative_sign_theorem_proved": False,
        "global_concavity_proved": False,
        "global_concavity_proven": False,
        "global_concavity_closed": False,
        "global_barrier_closed": False,
        "constants_absent": True,
        "simultaneous_theorem_absent": True,
        "required_theorem": (
            "GlobalSignedKernelDominanceWithSprint140CompatibleConstants"
        ),
        "required_constants_available": False,
        "global_concavity_proof_scope": "not_proved_sampling_only",
        "conclusion": "no_uniform_global_negative_sign_theorem",
        "blocker_open": True,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "promotion_decision": "hold_no_clay_promotion",
        "artifact_complete": invariants_passed,
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Sprint 142 lane 3 writes only "
                "scripts/ns_sprint142_kernel_sign_stress_sampler.py and "
                "outputs/ns_sprint142_kernel_sign_stress_sampler/."
            ),
            "R": (
                "Stress sample partial_z^2 psi1 kernel signs with favorable "
                "same-z rows plus axial, annular, boundary-image, and far-tail "
                "adverse rows."
            ),
            "C": (
                "Pure Python stdlib, deterministic S^3 Simpson quadrature, "
                "JSON summary, JSON rows, CSV, Markdown, fail-closed validation."
            ),
            "S": (
                "Local same-z radial rows are favorable, but adverse/nonlocal "
                "geometries keep the global sign theorem open."
            ),
            "L": (
                "5d radial Green kernel -> partial_z^2 derivative -> angular "
                "average -> radial measure weighting -> sign stress ledger."
            ),
            "P": (
                "Conclude no uniform global negative sign theorem; retain only "
                "localized support evidence."
            ),
            "G": (
                "Validation requires has_favorable_rows=true, "
                "has_adverse_rows=true, global_concavity_proved=false, "
                "uniform theorem false, and no Clay promotion."
            ),
            "F": (
                "Missing required rows/classes, absent favorable/adverse rows, "
                "any global proof claim, or any promotion fails closed."
            ),
        },
    }


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    if summary["route_decision"] != ROUTE_DECISION or not summary["fail_closed"]:
        raise ValueError("route decision must remain fail-closed")
    if not summary["has_favorable_rows"]:
        raise ValueError("validation requires has_favorable_rows=true")
    if not summary["has_adverse_rows"]:
        raise ValueError("validation requires has_adverse_rows=true")
    if summary["global_concavity_proved"]:
        raise ValueError("global_concavity_proved must be false")
    if summary["uniform_global_negative_sign_theorem_proved"]:
        raise ValueError("uniform global negative sign theorem must not be proved")
    if not summary["blocker_open"]:
        raise ValueError("blocker must remain open")
    if summary["full_clay_ns_solved"] or summary["clay_navier_stokes_promoted"]:
        raise ValueError("Clay promotion is forbidden")
    if any(row["global_concavity_proved"] for row in rows):
        raise ValueError("row claims global concavity proof")
    if any(row["uniform_global_negative_sign_theorem_proved"] for row in rows):
        raise ValueError("row claims uniform global negative sign theorem")
    if any(row["full_clay_ns_solved"] for row in rows):
        raise ValueError("row claims full Clay NS solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        raise ValueError("row promotes Clay Navier-Stokes")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty CSV")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
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
        "source",
        "weight",
        "contribution",
        "sign",
        "favorable",
        "adverse",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        source = f"r'={row['source_r']:.3g}, z'={row['source_z']:.3g}"
        lines.append(
            "| "
            + " | ".join(
                (
                    f"`{row['row_id']}`",
                    f"`{row['geometry_class']}`",
                    source,
                    format_value(row["source_weight"]),
                    format_value(row["weighted_contribution"]),
                    f"`{row['sign_classification']}`",
                    format_value(row["favorable_local_same_z_row"]),
                    format_value(row["adverse_or_nonlocal_row"]),
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 142 Kernel Sign Stress Sampler",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Parent ledger: `{PARENT_LEDGER}`",
        f"- Blocker: `{BLOCKER}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Has favorable rows: `{str(summary['has_favorable_rows']).lower()}`",
        f"- Has adverse rows: `{str(summary['has_adverse_rows']).lower()}`",
        f"- Global concavity proved: `{str(summary['global_concavity_proved']).lower()}`",
        f"- Uniform global negative sign theorem proved: `{str(summary['uniform_global_negative_sign_theorem_proved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        "",
        "## Rows",
        "",
        markdown_table(rows),
        "",
        "## Conclusion",
        "",
        (
            "The stress sampler preserves localized same-z negative-sign support, "
            "but axial-offset, annular, boundary-image, and far-tail rows keep "
            "the sign ledger mixed.  Therefore it concludes no uniform global "
            "negative sign theorem for partial_z^2 psi1."
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


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate(summary, rows)

    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")

    print(
        json.dumps(
            {
                "artifact_complete": summary["artifact_complete"],
                "blocker_open": summary["blocker_open"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "contract": summary["contract"],
                "global_concavity_proved": summary["global_concavity_proved"],
                "has_adverse_rows": summary["has_adverse_rows"],
                "has_favorable_rows": summary["has_favorable_rows"],
                "out_dir": str(out_dir),
                "route_decision": summary["route_decision"],
                "uniform_global_negative_sign_theorem_proved": summary[
                    "uniform_global_negative_sign_theorem_proved"
                ],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
