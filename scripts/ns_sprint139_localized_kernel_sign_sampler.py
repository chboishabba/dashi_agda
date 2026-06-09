#!/usr/bin/env python3
"""Sprint 139 localized axisymmetric kernel sign sampler.

This deterministic ledger samples the sign of localized contributions to
``partial_z^2 psi1`` relevant to the Sprint 138 ``GlobalConcavityOfPsi1``
blocker.  It uses the standard 5-dimensional radial interpretation of

    Ltilde = partial_r^2 + (3/r) partial_r + partial_z^2

for the axisymmetric variable ``psi1`` and samples the differentiated
fundamental-kernel sign after averaging over the S^3 angular variable.

The ledger is intentionally fail-closed.  It records local concavity support
where the sampled kernel contribution is favorable, but sign-indefinite
nonlocal annular and boundary-sensitive rows keep GlobalConcavityOfPsi1 open.
No global concavity theorem is proved, no full Clay Navier-Stokes solution is
claimed, and no promotion is emitted.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint139_localized_kernel_sign_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint139_localized_kernel_sign_sampler")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_NAME = CONTRACT + "_rows.json"
CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

BLOCKER = "GlobalConcavityOfPsi1"
PARENT_GATE = "AxialMonotonicityOfSwirlProfile"
ROUTE_DECISION = "fail_closed_kernel_sign_indefinite_no_promotion"
KERNEL_MODEL = "5d_radial_green_second_z_derivative_axisymmetric_S3_average"

VARIABLES = {
    "u1": "u^theta / r",
    "omega1": "omega^theta / r",
    "psi1": "psi^theta / r",
    "v": "partial_z u1",
    "Ltilde": "partial_r^2 + (3/r) partial_r + partial_z^2",
    "elliptic_relation": "-Ltilde psi1 = omega1",
    "sampled_kernel": "partial_z^2 |(y,z)-(y_prime,z_prime)|^-3, S^3-angular averaged",
}

ANGLE_STEPS = 721
EPSILON2 = 1.0e-8
SIGN_TOLERANCE = 1.0e-9

SAMPLES = (
    {
        "row_id": "local_radial_patch_same_z_support",
        "region": "local_core",
        "evaluation_r": 1.0,
        "evaluation_z": 0.0,
        "source_r": 0.82,
        "source_z": 0.0,
        "source_weight": 1.0,
        "expected_role": "local_concavity_support",
        "interpretation": (
            "A nearby same-z radial patch gives a negative sampled second-z "
            "kernel contribution for positive omega1, matching the local "
            "concavity direction needed by the barrier source term."
        ),
    },
    {
        "row_id": "local_broadened_radial_patch_support",
        "region": "local_core",
        "evaluation_r": 1.0,
        "evaluation_z": 0.0,
        "source_r": 0.62,
        "source_z": 0.0,
        "source_weight": 1.0,
        "expected_role": "local_concavity_support",
        "interpretation": (
            "A broader same-z local radial contribution remains favorable, "
            "showing that the sampler can register local concavity support."
        ),
    },
    {
        "row_id": "local_axial_offset_same_radius_wrong_sign",
        "region": "local_axial_offset",
        "evaluation_r": 1.0,
        "evaluation_z": 0.0,
        "source_r": 1.0,
        "source_z": 0.32,
        "source_weight": 1.0,
        "expected_role": "nearby_sign_indefinite_warning",
        "interpretation": (
            "A nearby same-radius axial offset can flip the sampled sign, so "
            "locality alone is not a signed kernel theorem."
        ),
    },
    {
        "row_id": "nonlocal_annular_same_z_support_not_global",
        "region": "nonlocal_annulus",
        "evaluation_r": 1.0,
        "evaluation_z": 0.0,
        "source_r": 2.25,
        "source_z": 0.0,
        "source_weight": 1.0,
        "expected_role": "annular_support_case",
        "interpretation": (
            "An annular same-z contribution may be favorable, but this is only "
            "one geometry and cannot establish global concavity."
        ),
    },
    {
        "row_id": "nonlocal_annular_axial_offset_wrong_sign",
        "region": "nonlocal_annulus",
        "evaluation_r": 1.0,
        "evaluation_z": 0.0,
        "source_r": 2.25,
        "source_z": 1.65,
        "source_weight": 1.0,
        "expected_role": "annular_sign_indefinite_obstruction",
        "interpretation": (
            "An annular source displaced in z can contribute with the opposite "
            "sign, exactly the nonlocal obstruction to GlobalConcavityOfPsi1."
        ),
    },
    {
        "row_id": "boundary_layer_near_wall_wrong_sign",
        "region": "boundary_layer",
        "evaluation_r": 1.0,
        "evaluation_z": 0.0,
        "source_r": 3.0,
        "source_z": 2.35,
        "source_weight": 1.0,
        "expected_role": "boundary_sign_indefinite_obstruction",
        "interpretation": (
            "A far annular/boundary-sensitive source can have the unfavorable "
            "sign at the interior evaluation point."
        ),
    },
    {
        "row_id": "outer_axial_tail_wrong_sign",
        "region": "outer_tail",
        "evaluation_r": 1.0,
        "evaluation_z": 0.0,
        "source_r": 0.45,
        "source_z": 1.55,
        "source_weight": 1.0,
        "expected_role": "tail_sign_indefinite_obstruction",
        "interpretation": (
            "An outer axial tail near the axis is unfavorable, so a local "
            "Taylor concavity patch cannot control every source location."
        ),
    },
)

REQUIRED_ROW_IDS = {str(sample["row_id"]) for sample in SAMPLES}


@dataclass(frozen=True)
class KernelSignRow:
    row_id: str
    blocker: str
    parent_gate: str
    region: str
    evaluation_r: float
    evaluation_z: float
    source_r: float
    source_z: float
    source_weight: float
    angular_steps: int
    kernel_average: float
    weighted_contribution: float
    min_point_kernel: float
    max_point_kernel: float
    sign_classification: str
    expected_role: str
    supports_local_concavity: bool
    sign_indefinite_obstruction: bool
    nonlocal_or_boundary: bool
    global_concavity_proved: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    interpretation: str

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["blocker_id"] = self.blocker
        row["blocker_status"] = (
            "open"
            if self.sign_indefinite_obstruction
            else "local_support_only"
        )
        row["blocked_claim"] = "GlobalConcavityOfPsi1"
        row["missing_input"] = (
            "signed global kernel dominance theorem"
            if self.sign_indefinite_obstruction
            else "extension from local sample to global elliptic theorem"
        )
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def second_z_kernel(dy2: float, dz: float) -> float:
    """Return the sign-relevant second-z derivative of rho^-3."""
    rho2 = dy2 + dz * dz + EPSILON2
    return 3.0 * (4.0 * dz * dz - dy2) / (rho2 ** 3.5)


def angular_average_kernel(
    evaluation_r: float,
    evaluation_z: float,
    source_r: float,
    source_z: float,
) -> tuple[float, float, float]:
    """Average over the S^3 angle with weight sin(theta)^2."""
    if ANGLE_STEPS < 3 or ANGLE_STEPS % 2 == 0:
        raise ValueError("ANGLE_STEPS must be odd and at least 3 for Simpson quadrature")

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
        return "negative_supports_concavity"
    if value > SIGN_TOLERANCE:
        return "positive_obstructs_concavity"
    return "near_zero_inconclusive"


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for sample in SAMPLES:
        kernel_average, min_kernel, max_kernel = angular_average_kernel(
            evaluation_r=float(sample["evaluation_r"]),
            evaluation_z=float(sample["evaluation_z"]),
            source_r=float(sample["source_r"]),
            source_z=float(sample["source_z"]),
        )
        weighted_contribution = kernel_average * float(sample["source_weight"]) * (
            float(sample["source_r"]) ** 3
        )
        sign_classification = classify_sign(weighted_contribution)
        supports_local = (
            sample["region"] == "local_core"
            and sign_classification == "negative_supports_concavity"
        )
        nonlocal_or_boundary = sample["region"] in {
            "nonlocal_annulus",
            "boundary_layer",
            "outer_tail",
        }
        sign_obstruction = (
            sign_classification != "negative_supports_concavity"
            or nonlocal_or_boundary
        )
        rows.append(
            KernelSignRow(
                row_id=str(sample["row_id"]),
                blocker=BLOCKER,
                parent_gate=PARENT_GATE,
                region=str(sample["region"]),
                evaluation_r=float(sample["evaluation_r"]),
                evaluation_z=float(sample["evaluation_z"]),
                source_r=float(sample["source_r"]),
                source_z=float(sample["source_z"]),
                source_weight=float(sample["source_weight"]),
                angular_steps=ANGLE_STEPS,
                kernel_average=kernel_average,
                weighted_contribution=weighted_contribution,
                min_point_kernel=min_kernel,
                max_point_kernel=max_kernel,
                sign_classification=sign_classification,
                expected_role=str(sample["expected_role"]),
                supports_local_concavity=supports_local,
                sign_indefinite_obstruction=sign_obstruction,
                nonlocal_or_boundary=nonlocal_or_boundary,
                global_concavity_proved=False,
                full_clay_ns_solved=False,
                clay_navier_stokes_promoted=False,
                interpretation=str(sample["interpretation"]),
            ).as_row()
        )
    return rows


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty row set")
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


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = {row["row_id"] for row in rows}
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_ids))
    local_support_rows = [row for row in rows if row["supports_local_concavity"]]
    positive_rows = [
        row
        for row in rows
        if row["sign_classification"] == "positive_obstructs_concavity"
    ]
    nonlocal_rows = [row for row in rows if row["nonlocal_or_boundary"]]
    obstruction_rows = [row for row in rows if row["sign_indefinite_obstruction"]]
    nonlocal_positive_rows = [
        row
        for row in rows
        if row["nonlocal_or_boundary"]
        and row["sign_classification"] == "positive_obstructs_concavity"
    ]

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if not local_support_rows:
        invariant_failures.append("local_concavity_support_missing")
    if not positive_rows:
        invariant_failures.append("positive_kernel_obstruction_missing")
    if not nonlocal_positive_rows:
        invariant_failures.append("nonlocal_positive_obstruction_missing")
    if not nonlocal_rows:
        invariant_failures.append("nonlocal_rows_missing")
    if any(row["global_concavity_proved"] for row in rows):
        invariant_failures.append("global_concavity_proof_claimed")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")

    invariants_passed = not invariant_failures
    return {
        "contract": CONTRACT,
        "blocker": BLOCKER,
        "parent_gate": PARENT_GATE,
        "kernel_model": KERNEL_MODEL,
        "variables": VARIABLES,
        "row_count": len(rows),
        "angular_steps": ANGLE_STEPS,
        "epsilon2": EPSILON2,
        "sign_tolerance": SIGN_TOLERANCE,
        "route_decision": ROUTE_DECISION,
        "decision": ROUTE_DECISION,
        "fail_closed": True,
        "local_concavity_supported": bool(local_support_rows),
        "local_support_rows": [row["row_id"] for row in local_support_rows],
        "positive_obstruction_rows": [row["row_id"] for row in positive_rows],
        "nonlocal_or_boundary_rows": [row["row_id"] for row in nonlocal_rows],
        "nonlocal_positive_obstruction_rows": [
            row["row_id"] for row in nonlocal_positive_rows
        ],
        "sign_indefinite_obstruction_rows": [
            row["row_id"] for row in obstruction_rows
        ],
        "global_concavity_closed": False,
        "global_concavity_proved": False,
        "global_concavity_proven": False,
        "global_concavity_proof_scope": "not_proved_sampling_only",
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_decision": "hold_no_clay_promotion",
        "blocker_open": True,
        "artifact_complete": invariants_passed,
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Worker 3 owns only scripts/ns_sprint139_localized_kernel_sign_sampler.py "
                "and outputs/ns_sprint139_localized_kernel_sign_sampler/."
            ),
            "R": (
                "Sample localized axisymmetric kernel signs relevant to "
                "GlobalConcavityOfPsi1 without proving global concavity."
            ),
            "C": (
                "Deterministic stdlib Python, fixed S^3 Simpson quadrature, "
                "dataclass rows, JSON, CSV, Markdown, and fail-closed validation."
            ),
            "S": (
                "Same-z local radial patches support concavity, while nearby "
                "axial offsets and nonlocal annular/boundary/tail sources can "
                "produce unfavorable signs."
            ),
            "L": (
                "Ltilde-as-5d-radial Green kernel -> second-z derivative -> "
                "localized S^3 average -> sign classification -> route decision."
            ),
            "P": (
                "Keep GlobalConcavityOfPsi1 open; use the sampler only as a "
                "ledger of support and obstructions."
            ),
            "G": (
                "Validation requires at least one local support row, at least "
                "one positive nonlocal obstruction, no global proof, no full "
                "Clay NS solved flag, and no promotion."
            ),
            "F": (
                "Missing required rows, no positive obstruction, any global "
                "concavity proof claim, or any Clay promotion fails closed."
            ),
        },
    }


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    row_ids = {row["row_id"] for row in rows}
    missing = REQUIRED_ROW_IDS.difference(row_ids)
    if missing:
        raise ValueError("missing required rows: " + ", ".join(sorted(missing)))
    if summary["route_decision"] != ROUTE_DECISION or not summary["fail_closed"]:
        raise ValueError("route decision must remain fail-closed")
    if not summary["local_concavity_supported"]:
        raise ValueError("local concavity support must be present")
    if not summary["nonlocal_positive_obstruction_rows"]:
        raise ValueError("nonlocal positive obstruction must be present")
    if summary["global_concavity_closed"] or summary["global_concavity_proved"]:
        raise ValueError("global concavity must not be closed or proved")
    if not summary["blocker_open"]:
        raise ValueError("GlobalConcavityOfPsi1 blocker must remain open")
    if summary["full_clay_ns_solved"] or summary["clay_navier_stokes_promoted"]:
        raise ValueError("Clay NS promotion is forbidden")
    if any(row["global_concavity_proved"] for row in rows):
        raise ValueError("row claims global concavity proof")
    if any(row["full_clay_ns_solved"] for row in rows):
        raise ValueError("row claims full Clay NS solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        raise ValueError("row promotes Clay Navier-Stokes")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "region",
        "source",
        "weighted contribution",
        "sign",
        "local support",
        "obstruction",
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
                    format_value(row["region"]),
                    source,
                    format_value(row["weighted_contribution"]),
                    f"`{row['sign_classification']}`",
                    format_value(row["supports_local_concavity"]),
                    format_value(row["sign_indefinite_obstruction"]),
                )
            )
            + " |"
        )
    return "\n".join(lines)


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 139 Localized Kernel Sign Sampler",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Blocker: `{BLOCKER}`",
        f"- Parent gate: `{PARENT_GATE}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Kernel model: `{KERNEL_MODEL}`",
        f"- Local concavity supported: `{str(summary['local_concavity_supported']).lower()}`",
        f"- Global concavity proved: `{str(summary['global_concavity_proved']).lower()}`",
        f"- Blocker open: `{str(summary['blocker_open']).lower()}`",
        f"- Full Clay NS solved: `{str(summary['full_clay_ns_solved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        "",
        "## Kernel Sign Rows",
        "",
        markdown_table(rows),
        "",
        "## Interpretation",
        "",
        (
            "Negative weighted contributions are favorable for the local "
            "concavity direction of partial_z^2 psi1 under positive omega1. "
            "Positive rows are obstructions.  Because the sampled nonlocal "
            "annular/boundary/tail geometries include unfavorable signs, the "
            "ledger does not prove GlobalConcavityOfPsi1."
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

    write_json(out_dir / ROWS_NAME, rows)
    write_csv(out_dir / CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")

    print(
        json.dumps(
            {
                "artifact_complete": summary["artifact_complete"],
                "blocker": summary["blocker"],
                "blocker_open": summary["blocker_open"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "contract": summary["contract"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "global_concavity_proved": summary["global_concavity_proved"],
                "local_concavity_supported": summary["local_concavity_supported"],
                "nonlocal_positive_obstruction_rows": summary[
                    "nonlocal_positive_obstruction_rows"
                ],
                "out_dir": str(out_dir),
                "route_decision": summary["route_decision"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
