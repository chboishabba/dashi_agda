#!/usr/bin/env python3
"""Sprint 142 boundary/annulus concavity ledger emitter.

This deterministic ledger records why boundary and annular effects block
``GlobalConcavityOfPsi1`` unless an explicit boundary-compatible
kernel/sign/cancellation theorem is supplied.

The artifact is a blocker ledger, not a proof.  It emits no global
Navier-Stokes proof, does not close ``GlobalConcavityOfPsi1``, and does not
promote to the Clay Navier-Stokes class.
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


CONTRACT = "ns_sprint142_boundary_annulus_concavity_ledger"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint142_boundary_annulus_concavity_ledger")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 142
LANE = 4
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
BLOCKER = "GlobalConcavityOfPsi1"
PARENT_GATE = "AxialMonotonicityOfSwirlProfile"
TARGET_TERM = "2 u1 partial_z^2 psi1"
ELLIPTIC_RELATION = "-Ltilde psi1 = omega1"
DECISION = "fail_closed_boundary_annulus_concavity_blocker_open"
REQUIRED_THEOREM = "BoundaryCompatibleKernelSignCancellationForPsi1Concavity"

REQUIRED_ROW_IDS = {
    "interior_local_support",
    "boundary_image_sign_hazard",
    "annular_shoulder_hazard",
    "axis_regularity_compatibility",
    "missing_theorem",
}


@dataclass(frozen=True)
class ConcavityLedgerRow:
    row_id: str
    ledger_role: str
    status: str
    statement: str
    boundary_effect: str
    annular_effect: str
    sign_or_cancellation_state: str
    required_input: tuple[str, ...]
    local_support_available: bool
    boundary_compatible: bool
    annulus_compatible: bool
    global_concavity_closed: bool
    blocker_open: bool
    global_proof: bool
    clay_navier_stokes_promoted: bool
    promotion_allowed: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["required_input"] = list(self.required_input)
        row["program"] = PROGRAM
        row["blocker"] = BLOCKER
        row["parent_gate"] = PARENT_GATE
        row["target_term"] = TARGET_TERM
        row["elliptic_relation"] = ELLIPTIC_RELATION
        row["required_theorem"] = REQUIRED_THEOREM
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
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


def build_rows() -> list[dict[str, Any]]:
    rows = [
        ConcavityLedgerRow(
            row_id="interior_local_support",
            ledger_role="interior_local_patch",
            status="supported_local_only",
            statement=(
                "Interior Taylor data near the symmetry-center peak can support "
                "a local favorable sign for partial_z^2 psi1."
            ),
            boundary_effect=(
                "The local calculation does not include reflected or boundary "
                "image contributions from the elliptic solve."
            ),
            annular_effect=(
                "The local patch does not control source mass in radial annuli "
                "away from the symmetry center."
            ),
            sign_or_cancellation_state="local_sign_available_no_global_cancellation",
            required_input=(
                "uniform localization radius",
                "proof that admissible first crossings remain inside the local patch",
            ),
            local_support_available=True,
            boundary_compatible=False,
            annulus_compatible=False,
            global_concavity_closed=False,
            blocker_open=True,
            global_proof=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        ConcavityLedgerRow(
            row_id="boundary_image_sign_hazard",
            ledger_role="boundary_kernel_effect",
            status="open_sign_hazard",
            statement=(
                "Boundary-compatible Green representations can introduce image "
                "or correction terms whose second axial derivative is not signed "
                "by the interior local peak calculation."
            ),
            boundary_effect=(
                "A near-boundary source or crossing can receive a contribution "
                "with the wrong sign for the barrier source term."
            ),
            annular_effect=(
                "Annular source placement can couple with boundary corrections "
                "and change the sign balance at an interior crossing."
            ),
            sign_or_cancellation_state="boundary_kernel_sign_not_certified",
            required_input=(
                "boundary-compatible signed kernel theorem",
                "or boundary correction cancellation estimate",
                "or domination bound uniform over admissible boundary layers",
            ),
            local_support_available=False,
            boundary_compatible=False,
            annulus_compatible=False,
            global_concavity_closed=False,
            blocker_open=True,
            global_proof=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        ConcavityLedgerRow(
            row_id="annular_shoulder_hazard",
            ledger_role="annular_source_geometry",
            status="open_annular_hazard",
            statement=(
                "Annular shoulders of omega1 away from the axis can contribute "
                "to partial_z^2 psi1 at a candidate crossing through the "
                "nonlocal elliptic kernel."
            ),
            boundary_effect=(
                "Outer-domain and boundary geometry can amplify or redirect the "
                "annular contribution rather than preserving the local sign."
            ),
            annular_effect=(
                "A radial shoulder can offset favorable center mass and make "
                f"{TARGET_TERM} positive at an admissible first crossing."
            ),
            sign_or_cancellation_state="annular_cancellation_not_proved",
            required_input=(
                "annular exclusion theorem",
                "annular signed-kernel dominance theorem",
                "or cancellation estimate covering off-axis source mass",
            ),
            local_support_available=False,
            boundary_compatible=False,
            annulus_compatible=False,
            global_concavity_closed=False,
            blocker_open=True,
            global_proof=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        ConcavityLedgerRow(
            row_id="axis_regularity_compatibility",
            ledger_role="axis_and_regular_boundary_interface",
            status="compatibility_unproved",
            statement=(
                "Any global concavity theorem must be compatible with the "
                "axisymmetric regularity conditions at r=0 and with the boundary "
                "conditions used by the elliptic psi1 solve."
            ),
            boundary_effect=(
                "Boundary conditions must preserve the claimed sign after "
                "differentiating the elliptic representation twice in z."
            ),
            annular_effect=(
                "Regularity at the axis does not rule out off-axis annular "
                "source configurations."
            ),
            sign_or_cancellation_state="axis_regular_but_global_sign_unlinked",
            required_input=(
                "axis-regular kernel theorem",
                "boundary-condition compatibility proof",
                "uniform statement over interior, axis-adjacent, and annular cases",
            ),
            local_support_available=False,
            boundary_compatible=False,
            annulus_compatible=False,
            global_concavity_closed=False,
            blocker_open=True,
            global_proof=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
        ConcavityLedgerRow(
            row_id="missing_theorem",
            ledger_role="required_theorem_interface",
            status="missing_boundary_compatible_kernel_sign_cancellation_theorem",
            statement=(
                "GlobalConcavityOfPsi1 remains blocked until an explicit theorem "
                "signs, dominates, or cancels boundary and annular contributions "
                "for every admissible first positive crossing."
            ),
            boundary_effect=(
                "No boundary-compatible kernel/sign/cancellation theorem is "
                "available in this ledger."
            ),
            annular_effect=(
                "No annular shoulder exclusion, dominance, or cancellation "
                "theorem is available in this ledger."
            ),
            sign_or_cancellation_state="missing_required_theorem",
            required_input=(
                REQUIRED_THEOREM,
                "quantitative constants compatible with the monitored barrier route",
                "formal promotion receipt that preserves no-gap assumptions",
            ),
            local_support_available=False,
            boundary_compatible=False,
            annulus_compatible=False,
            global_concavity_closed=False,
            blocker_open=True,
            global_proof=False,
            clay_navier_stokes_promoted=False,
            promotion_allowed=False,
        ),
    ]
    materialized = [row.as_row() for row in rows]
    validate_rows(materialized)
    return materialized


def validate_rows(rows: list[dict[str, Any]]) -> None:
    row_ids = {row["row_id"] for row in rows}
    if row_ids != REQUIRED_ROW_IDS:
        missing = sorted(REQUIRED_ROW_IDS - row_ids)
        extra = sorted(row_ids - REQUIRED_ROW_IDS)
        raise ValueError(f"row-id mismatch: missing={missing} extra={extra}")

    for row in rows:
        if row["global_concavity_closed"]:
            raise ValueError(f"{row['row_id']} incorrectly closes {BLOCKER}")
        if row["global_proof"]:
            raise ValueError(f"{row['row_id']} incorrectly emits a global proof")
        if row["clay_navier_stokes_promoted"] or row["promotion_allowed"]:
            raise ValueError(f"{row['row_id']} incorrectly allows promotion")
        if row["claim_closed"] or row["claim_proved"] or row["claim_proven"]:
            raise ValueError(f"{row['row_id']} incorrectly marks the claim proved")


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_hashes = {row["row_id"]: row["row_hash"] for row in rows}
    theorem_available = False
    all_boundary_compatible = all(row["boundary_compatible"] for row in rows)
    all_annulus_compatible = all(row["annulus_compatible"] for row in rows)
    global_concavity_closed = theorem_available and all_boundary_compatible and all_annulus_compatible
    global_proof = global_concavity_closed and False
    clay_promoted = global_proof and False

    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "blocker": BLOCKER,
        "parent_gate": PARENT_GATE,
        "target_term": TARGET_TERM,
        "elliptic_relation": ELLIPTIC_RELATION,
        "decision": DECISION,
        "required_theorem": REQUIRED_THEOREM,
        "required_theorem_available": theorem_available,
        "boundary_compatible_kernel_sign_or_cancellation_theorem_exists": theorem_available,
        "annular_shoulder_theorem_exists": theorem_available,
        "row_count": len(rows),
        "required_rows_present": sorted(REQUIRED_ROW_IDS),
        "local_support_rows": [
            row["row_id"] for row in rows if row["local_support_available"]
        ],
        "open_hazard_rows": [
            row["row_id"] for row in rows if row["blocker_open"]
        ],
        "global_concavity_closed": global_concavity_closed,
        "blocker_open": True,
        "global_proof": global_proof,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": clay_promoted,
        "promotion_allowed": False,
        "validation": {
            "no_global_proof": not global_proof,
            "no_promotion": not clay_promoted,
            "no_claim_closure": not global_concavity_closed,
            "fail_closed": True,
        },
        "row_hashes": row_hashes,
    }
    if summary["global_proof"] or summary["clay_navier_stokes_promoted"]:
        raise ValueError("summary promotion/proof guard failed")
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = [
        "row_id",
        "ledger_role",
        "status",
        "statement",
        "boundary_effect",
        "annular_effect",
        "sign_or_cancellation_state",
        "required_input",
        "local_support_available",
        "boundary_compatible",
        "annulus_compatible",
        "global_concavity_closed",
        "blocker_open",
        "global_proof",
        "clay_navier_stokes_promoted",
        "promotion_allowed",
        "row_hash",
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serialized = dict(row)
            serialized["required_input"] = " | ".join(row["required_input"])
            writer.writerow({field: serialized[field] for field in fieldnames})


def write_markdown(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    lines = [
        "# Sprint 142 Boundary/Annulus Concavity Ledger",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Program: `{PROGRAM}`",
        f"- Blocker: `{BLOCKER}`",
        f"- Parent gate: `{PARENT_GATE}`",
        f"- Decision: `{DECISION}`",
        f"- Required theorem: `{REQUIRED_THEOREM}`",
        f"- Global concavity closed: `{summary['global_concavity_closed']}`",
        f"- Global proof emitted: `{summary['global_proof']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Rows",
        "",
        "| row_id | status | role | blocker effect | required input |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        required = "; ".join(row["required_input"])
        effect = (
            "Boundary compatible: "
            f"{row['boundary_compatible']}; annulus compatible: "
            f"{row['annulus_compatible']}; global concavity closed: "
            f"{row['global_concavity_closed']}."
        )
        lines.append(
            "| {row_id} | {status} | {role} | {effect} | {required} |".format(
                row_id=row["row_id"],
                status=row["status"],
                role=row["ledger_role"],
                effect=effect,
                required=required,
            )
        )
    lines.extend(
        [
            "",
            "## Validation",
            "",
            "- No global proof is emitted.",
            "- No Clay Navier-Stokes promotion is emitted.",
            "- `GlobalConcavityOfPsi1` remains open unless the missing boundary-compatible theorem is supplied.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def emit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)

    rows_json_path = out_dir / ROWS_JSON_NAME
    rows_csv_path = out_dir / ROWS_CSV_NAME
    report_path = out_dir / REPORT_NAME
    summary_path = out_dir / SUMMARY_NAME

    write_json(rows_json_path, rows)
    write_csv(rows_csv_path, rows)
    write_markdown(report_path, summary, rows)

    summary["artifacts"] = {
        "summary_json": str(summary_path.relative_to(repo_root)),
        "rows_json": str(rows_json_path.relative_to(repo_root)),
        "rows_csv": str(rows_csv_path.relative_to(repo_root)),
        "markdown": str(report_path.relative_to(repo_root)),
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
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
