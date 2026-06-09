#!/usr/bin/env python3
"""Sprint 138 global concavity blocker emitter.

This deterministic emitter records ``GlobalConcavityOfPsi1`` as the first
Sprint 138 blocker for ``AxialMonotonicityOfSwirlProfile``.  The ledger is a
proof-obligation surface: it separates the local Taylor concavity available
near the symmetry center from the unresolved global/nonlocal sign control
needed for the axial monotonicity maximum-principle route.

The decision is intentionally fail-closed.  Local concavity is supported, but
global concavity is not closed; the blocker remains open and there is no Clay
Navier-Stokes promotion.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint138_global_concavity_blocker"
BLOCKER = "GlobalConcavityOfPsi1"
PARENT_GATE = "AxialMonotonicityOfSwirlProfile"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint138_global_concavity_blocker")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_NAME = CONTRACT + "_rows.json"
CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

VARIABLES = {
    "u1": "u^theta / r",
    "omega1": "omega^theta / r",
    "psi1": "psi^theta / r",
    "v": "partial_z u1",
    "Ltilde": "partial_r^2 + (3/r) partial_r + partial_z^2",
    "elliptic_relation": "-Ltilde psi1 = omega1",
}

REQUIRED_ROW_IDS = {
    "local_taylor_concavity_near_symmetry_center",
    "elliptic_nonlocal_psi1_dependence_on_omega1",
    "sign_indefinite_kernel_contribution",
    "boundary_annular_contribution",
    "persistence_failure",
    "required_theorem_global_concavity_of_psi1",
}

DECISION = "fail_closed_blocker_open"
LOCAL_CLAIM = "local_concavity_supported"
GLOBAL_CLAIM = "global_concavity_not_closed"
REQUIRED_THEOREM = (
    "For every possible first positive maximum of v=partial_z u1 in the "
    "monitored half-profile, partial_z^2 psi1 must keep the sign needed to "
    "make 2 u1 partial_z^2 psi1 nonpositive or otherwise dominated."
)


@dataclass(frozen=True)
class ConcavityBlockerRow:
    row_id: str
    blocker: str
    parent_gate: str
    status: str
    ledger_role: str
    statement: str
    obstruction_mechanism: str
    support: tuple[str, ...]
    missing_evidence: tuple[str, ...]
    local_concavity_supported: bool
    global_concavity_closed: bool
    blocker_open: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["support"] = list(self.support)
        row["missing_evidence"] = list(self.missing_evidence)
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        ConcavityBlockerRow(
            row_id="local_taylor_concavity_near_symmetry_center",
            blocker=BLOCKER,
            parent_gate=PARENT_GATE,
            status="supported_local",
            ledger_role="local_center_expansion",
            statement=(
                "At the z-reflection symmetry center, a local Taylor expansion "
                "can support partial_z^2 psi1<=0 in a small neighborhood of "
                "the primary axial maximum, provided the center is a genuine "
                "concave stream-profile peak."
            ),
            obstruction_mechanism=(
                "This controls only a local patch and does not rule out "
                "off-center first positive crossings of v."
            ),
            support=(
                "z-reflection symmetry",
                "primary axial maximum geometry",
                "local Taylor concavity near z=0",
            ),
            missing_evidence=(
                "uniform radius of validity",
                "control of crossings outside the local Taylor patch",
            ),
            local_concavity_supported=True,
            global_concavity_closed=False,
            blocker_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        ConcavityBlockerRow(
            row_id="elliptic_nonlocal_psi1_dependence_on_omega1",
            blocker=BLOCKER,
            parent_gate=PARENT_GATE,
            status="open_blocker",
            ledger_role="elliptic_nonlocality",
            statement=(
                "The stream variable psi1 is determined by the elliptic "
                "relation -Ltilde psi1 = omega1, so partial_z^2 psi1 depends "
                "nonlocally on the full omega1 distribution rather than only "
                "on the local sign structure near the symmetry center."
            ),
            obstruction_mechanism=(
                "A local peak calculation for omega1 or psi1 cannot by itself "
                "force global concavity of psi1."
            ),
            support=(
                VARIABLES["elliptic_relation"],
                "Sprint134 corrected axisymmetric elliptic coupling",
            ),
            missing_evidence=(
                "global elliptic comparison theorem for partial_z^2 psi1",
                "monotone-preserving Biot-Savart representation in the full domain",
            ),
            local_concavity_supported=False,
            global_concavity_closed=False,
            blocker_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        ConcavityBlockerRow(
            row_id="sign_indefinite_kernel_contribution",
            blocker=BLOCKER,
            parent_gate=PARENT_GATE,
            status="open_blocker",
            ledger_role="kernel_sign",
            statement=(
                "The differentiated elliptic kernel contributing to "
                "partial_z^2 psi1 is sign-indefinite across source locations, "
                "so favorable near-center mass can be offset by remote or "
                "asymmetric omega1 contributions."
            ),
            obstruction_mechanism=(
                "The maximum-principle source term 2 u1 partial_z^2 psi1 can "
                "become positive at an admissible crossing if the nonlocal "
                "kernel contribution has the wrong sign."
            ),
            support=(
                "second z-derivatives of Green-kernel representations change sign",
                "nonlocal omega1-to-psi1 coupling",
            ),
            missing_evidence=(
                "signed kernel dominance estimate",
                "cancellation bound strong enough for every first-crossing site",
            ),
            local_concavity_supported=False,
            global_concavity_closed=False,
            blocker_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        ConcavityBlockerRow(
            row_id="boundary_annular_contribution",
            blocker=BLOCKER,
            parent_gate=PARENT_GATE,
            status="open_blocker",
            ledger_role="boundary_and_annulus",
            statement=(
                "Boundary layers, annular mass away from the axis, and outer "
                "domain contributions can alter partial_z^2 psi1 at an "
                "interior point even when the symmetry-center profile remains "
                "locally concave."
            ),
            obstruction_mechanism=(
                "A first positive maximum of v can occur in an annular or "
                "near-boundary region where the local center concavity ledger "
                "has no sign authority."
            ),
            support=(
                "elliptic boundary sensitivity",
                "annular source distributions in axisymmetric coordinates",
            ),
            missing_evidence=(
                "boundary-compatible global barrier for psi1 concavity",
                "annular contribution exclusion or domination estimate",
            ),
            local_concavity_supported=False,
            global_concavity_closed=False,
            blocker_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        ConcavityBlockerRow(
            row_id="persistence_failure",
            blocker=BLOCKER,
            parent_gate=PARENT_GATE,
            status="open_blocker",
            ledger_role="time_persistence",
            statement=(
                "Even if the initial profile has a favorable concavity patch, "
                "the current route has no persistence theorem showing that "
                "partial_z^2 psi1 keeps the required sign over the time window "
                "needed for axial monotonicity."
            ),
            obstruction_mechanism=(
                "The barrier argument needs sign control at the first crossing "
                "time, not merely at initial time or at the symmetry center."
            ),
            support=(
                "Sprint137 first-positive-crossing ledger",
                "time-dependent nonlocal elliptic solve",
            ),
            missing_evidence=(
                "transport-stable concavity invariant",
                "a priori estimate preventing concavity loss before crossing",
            ),
            local_concavity_supported=False,
            global_concavity_closed=False,
            blocker_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        ConcavityBlockerRow(
            row_id="required_theorem_global_concavity_of_psi1",
            blocker=BLOCKER,
            parent_gate=PARENT_GATE,
            status="required_theorem_missing",
            ledger_role="closure_requirement",
            statement=REQUIRED_THEOREM,
            obstruction_mechanism=(
                "Without this theorem, AxialMonotonicityOfSwirlProfile cannot "
                "be closed from the local symmetry-center calculation."
            ),
            support=(
                "local concavity support only",
                "maximum-principle source sign requirement from Sprint137",
            ),
            missing_evidence=(
                "GlobalConcavityOfPsi1",
                "signed nonlocal elliptic estimate",
                "boundary and annular contribution control",
                "time persistence of the concavity sign",
            ),
            local_concavity_supported=False,
            global_concavity_closed=False,
            blocker_open=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "blocker",
        "parent_gate",
        "status",
        "ledger_role",
        "statement",
        "obstruction_mechanism",
        "support",
        "missing_evidence",
        "local_concavity_supported",
        "global_concavity_closed",
        "blocker_open",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = dict(row)
            serializable["support"] = "; ".join(serializable["support"])
            serializable["missing_evidence"] = "; ".join(serializable["missing_evidence"])
            writer.writerow(serializable)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["row_id"]: row for row in rows}
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_by_id))
    open_rows = [row for row in rows if row["blocker_open"]]
    local_rows = [row for row in rows if row["local_concavity_supported"]]
    global_closed_rows = [row for row in rows if row["global_concavity_closed"]]

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if not local_rows:
        invariant_failures.append("local_concavity_support_missing")
    if "local_taylor_concavity_near_symmetry_center" not in {
        row["row_id"] for row in local_rows
    }:
        invariant_failures.append("local_taylor_row_not_supported")
    if not open_rows:
        invariant_failures.append("blocker_not_open")
    if global_closed_rows:
        invariant_failures.append("global_concavity_incorrectly_closed")
    if any(row["full_clay_ns_solved"] for row in rows):
        invariant_failures.append("full_clay_ns_solved_detected")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")
    if "partial_z^2 psi1" not in REQUIRED_THEOREM:
        invariant_failures.append("required_theorem_missing_concavity_term")

    invariants_passed = not invariant_failures
    return {
        "contract": CONTRACT,
        "blocker": BLOCKER,
        "parent_gate": PARENT_GATE,
        "row_count": len(rows),
        "variables": VARIABLES,
        "required_theorem": REQUIRED_THEOREM,
        "decision": DECISION,
        "route_decision": DECISION,
        "fail_closed": True,
        "local_concavity_status": LOCAL_CLAIM,
        "local_concavity_supported": bool(local_rows),
        "global_concavity_status": GLOBAL_CLAIM,
        "global_concavity_closed": False,
        "global_concavity_proved": False,
        "global_concavity_proven": False,
        "global_proof_proved": False,
        "global_proof_proven": False,
        "blocker_open": True,
        "blocker_status": "open_blocker",
        "boundary_persistence": "boundary_annular_contribution_and_persistence_failure_open",
        "axial_monotonicity_closed": False,
        "proof_claimed": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_decision": "hold_no_clay_promotion",
        "open_blockers": [row["row_id"] for row in open_rows],
        "supported_local_rows": [row["row_id"] for row in local_rows],
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "artifact_complete": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Worker owns only scripts/ns_sprint138_global_concavity_blocker.py "
                "and outputs/ns_sprint138_global_concavity_blocker/."
            ),
            "R": (
                "Analyze GlobalConcavityOfPsi1 as the first Sprint 138 blocker "
                "for AxialMonotonicityOfSwirlProfile."
            ),
            "C": (
                "Deterministic stdlib Python emitter with dataclass rows, "
                "JSON, CSV, Markdown, validate(), and main()."
            ),
            "S": (
                "Local Taylor concavity near the symmetry center is supported; "
                "elliptic nonlocality, sign-indefinite kernels, boundary/annular "
                "terms, and persistence keep the global theorem open."
            ),
            "L": (
                "local center expansion -> nonlocal psi1 dependence -> "
                "sign-indefinite kernel and boundary annulus -> persistence "
                "failure -> missing required theorem"
            ),
            "P": (
                "Keep the Sprint 138 route fail-closed until a global concavity "
                "theorem for psi1 is proved."
            ),
            "G": (
                "Validation passes only if local concavity is recorded, global "
                "concavity remains unclosed, the blocker remains open, and Clay "
                "flags stay false."
            ),
            "F": (
                "Missing required rows, closing global concavity, claiming axial "
                "monotonicity, flipping the full Clay NS guard, or promoting "
                "Clay fails validation."
            ),
        },
    }


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    row_ids = {row["row_id"] for row in rows}
    missing = REQUIRED_ROW_IDS.difference(row_ids)
    if missing:
        raise ValueError("missing required rows: " + ", ".join(sorted(missing)))
    if summary["blocker"] != BLOCKER:
        raise ValueError("wrong blocker in summary")
    if summary["parent_gate"] != PARENT_GATE:
        raise ValueError("wrong parent gate in summary")
    if summary["decision"] != DECISION or not summary["fail_closed"]:
        raise ValueError("decision must stay fail-closed")
    if not summary["local_concavity_supported"]:
        raise ValueError("local concavity support must be recorded")
    if summary["global_concavity_closed"]:
        raise ValueError("global concavity must remain open")
    if not summary["blocker_open"]:
        raise ValueError("blocker must remain open")
    if summary["axial_monotonicity_closed"] or summary["proof_claimed"]:
        raise ValueError("axial monotonicity/global proof must not be claimed")
    if summary["full_clay_ns_solved"] or summary["clay_navier_stokes_promoted"]:
        raise ValueError("Clay promotion is forbidden")
    if any(row["global_concavity_closed"] for row in rows):
        raise ValueError("row incorrectly closes global concavity")
    if any(row["full_clay_ns_solved"] for row in rows):
        raise ValueError("row claims full Clay NS solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        raise ValueError("row promotes Clay Navier-Stokes")
    if "required_theorem_global_concavity_of_psi1" not in summary["open_blockers"]:
        raise ValueError("required theorem row must remain an open blocker")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 138 Global Concavity Blocker",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Blocker: `{BLOCKER}`",
        f"- Parent gate: `{PARENT_GATE}`",
        f"- Decision: `{summary['decision']}`",
        f"- Local concavity supported: `{str(summary['local_concavity_supported']).lower()}`",
        f"- Global concavity closed: `{str(summary['global_concavity_closed']).lower()}`",
        f"- Blocker open: `{str(summary['blocker_open']).lower()}`",
        f"- Full Clay NS solved: `{str(summary['full_clay_ns_solved']).lower()}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        "",
        "## Required Theorem",
        "",
        summary["required_theorem"],
        "",
        "## Rows",
        "",
        "| Row | Status | Role | Statement | Obstruction |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        statement = row["statement"].replace("|", "\\|")
        obstruction = row["obstruction_mechanism"].replace("|", "\\|")
        lines.append(
            f"| `{row['row_id']}` | `{row['status']}` | `{row['ledger_role']}` | "
            f"{statement} | {obstruction} |"
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
                "decision": summary["decision"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "global_concavity_closed": summary["global_concavity_closed"],
                "local_concavity_supported": summary["local_concavity_supported"],
                "out_dir": str(out_dir),
            },
            sort_keys=True,
        )
    )
    return summary["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
