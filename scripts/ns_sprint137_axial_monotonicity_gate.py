#!/usr/bin/env python3
"""Sprint 137 axial monotonicity gate emitter.

This deterministic emitter models the remaining gate
``AxialMonotonicityOfSwirlProfile`` after the corrected Hou-Luo
axisymmetric-with-swirl surface.  The proof attempt is recorded as a
maximum-principle/barrier ledger for ``v = partial_z u1``.

The ledger is intentionally fail-closed: it records local barrier support near
the symmetric axial maximum, but it does not claim global monotonicity because
global concavity and secondary-peak exclusion remain open blockers.  It does
not promote Clay Navier-Stokes.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint137_axial_monotonicity_gate"
GATE = "AxialMonotonicityOfSwirlProfile"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint137_axial_monotonicity_gate")
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
    "Dt": "partial_t + u^r partial_r + u^z partial_z",
}

U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
V_BARRIER_EQUATION = (
    "D_t v = nu Ltilde v + 2 v partial_z psi1 + 2 u1 partial_z^2 psi1 "
    "- (partial_z u^r) partial_r u1 - (partial_z u^z) v"
)
LOCAL_MAX_CRITERION = (
    "At the first time when v becomes positive in the monitored half-profile, "
    "the interior positive maximum has v>0, partial_r v=partial_z v=0, and "
    "Ltilde v<=0."
)
ROUTE_DECISION = "conditional_fail_closed"

REQUIRED_ROW_IDS = {
    "symmetry_inheritance",
    "v_initial_sign",
    "first_positive_crossing_criterion",
    "source_derivative_term",
    "local_concavity_support",
    "diffusion_at_positive_max_sign",
    "global_concavity_blocker",
    "secondary_peak_blocker",
}


@dataclass(frozen=True)
class BarrierRow:
    row_id: str
    gate: str
    status: str
    ledger_role: str
    statement: str
    maximum_principle_effect: str
    support: tuple[str, ...]
    missing_evidence: tuple[str, ...]
    local_barrier_supported: bool
    global_proof_closed: bool
    blocker: bool
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
        BarrierRow(
            row_id="symmetry_inheritance",
            gate=GATE,
            status="supported_local",
            ledger_role="symmetry",
            statement=(
                "If u1 is even about the axial symmetry plane z=0, then "
                "v=partial_z u1 is odd and v=0 on the symmetry plane."
            ),
            maximum_principle_effect=(
                "The monitored half-profile can impose a zero barrier at the "
                "symmetry plane before searching for a first positive crossing."
            ),
            support=(
                "Sprint134:corrected axisymmetric variables",
                "Hou-Luo symmetric profile ansatz",
            ),
            missing_evidence=(),
            local_barrier_supported=True,
            global_proof_closed=False,
            blocker=False,
            clay_navier_stokes_promoted=False,
        ),
        BarrierRow(
            row_id="v_initial_sign",
            gate=GATE,
            status="assumption_tracked",
            ledger_role="initial_barrier",
            statement=(
                "The candidate monotone half-profile starts with v<=0 on the "
                "chosen side of the symmetry plane, with compatible boundary "
                "and decay conditions."
            ),
            maximum_principle_effect=(
                "A sign-preservation proof may begin only after this initial "
                "barrier is explicitly part of the data class."
            ),
            support=(
                "profile-level monotonicity input",
                "classical solution regularity for pointwise differentiation",
            ),
            missing_evidence=(
                "construction of smooth finite-energy data satisfying the sign "
                "condition globally",
            ),
            local_barrier_supported=True,
            global_proof_closed=False,
            blocker=False,
            clay_navier_stokes_promoted=False,
        ),
        BarrierRow(
            row_id="first_positive_crossing_criterion",
            gate=GATE,
            status="supported_local",
            ledger_role="first_crossing",
            statement=LOCAL_MAX_CRITERION,
            maximum_principle_effect=(
                "At a first positive interior maximum, the transport drift is "
                "harmless and the parabolic contradiction reduces to the sign "
                "of source and commutator terms."
            ),
            support=(
                "classical parabolic maximum-principle geometry",
                "Ltilde commutes with partial_z",
            ),
            missing_evidence=(
                "global compactness or boundary exclusion for every possible "
                "first crossing location",
            ),
            local_barrier_supported=True,
            global_proof_closed=False,
            blocker=False,
            clay_navier_stokes_promoted=False,
        ),
        BarrierRow(
            row_id="source_derivative_term",
            gate=GATE,
            status="conditional",
            ledger_role="differentiated_source",
            statement=(
                "Differentiating the corrected u1 equation gives the source "
                "ledger term 2 v partial_z psi1 + 2 u1 partial_z^2 psi1, plus "
                "transport commutators."
            ),
            maximum_principle_effect=(
                "The dangerous nonhomogeneous term at a first positive maximum "
                "is 2 u1 partial_z^2 psi1; it must be nonpositive or dominated "
                "to close the barrier."
            ),
            support=(
                U1_EQUATION,
                V_BARRIER_EQUATION,
            ),
            missing_evidence=(
                "global sign control for partial_z^2 psi1",
                "uniform domination of transport commutators",
            ),
            local_barrier_supported=True,
            global_proof_closed=False,
            blocker=False,
            clay_navier_stokes_promoted=False,
        ),
        BarrierRow(
            row_id="local_concavity_support",
            gate=GATE,
            status="supported_local",
            ledger_role="local_barrier_closure",
            statement=(
                "Near the symmetric axial maximum, local concavity of the "
                "stream profile supports partial_z^2 psi1<=0 in the active "
                "barrier region when u1>=0."
            ),
            maximum_principle_effect=(
                "On this local patch, 2 u1 partial_z^2 psi1 is nonpositive, "
                "so the first-crossing contradiction is locally plausible."
            ),
            support=(
                "symmetric axial peak geometry",
                "local Taylor expansion at the axial maximum",
            ),
            missing_evidence=(
                "propagation of the concavity patch for the full time window",
                "uniform lower margin away from the peak",
            ),
            local_barrier_supported=True,
            global_proof_closed=False,
            blocker=False,
            clay_navier_stokes_promoted=False,
        ),
        BarrierRow(
            row_id="diffusion_at_positive_max_sign",
            gate=GATE,
            status="supported_local",
            ledger_role="diffusion_sign",
            statement=(
                "At an interior positive maximum of v away from r=0, "
                "Ltilde v = partial_r^2 v + (3/r)partial_r v + partial_z^2 v "
                "is nonpositive because partial_r v=0 and the Hessian is "
                "negative semidefinite."
            ),
            maximum_principle_effect=(
                "The viscosity term nu Ltilde v cannot create the first "
                "positive maximum in the local barrier calculation."
            ),
            support=(
                "interior maximum Hessian sign",
                "axisymmetric Ltilde operator from Sprint134",
            ),
            missing_evidence=(
                "axis boundary handling if the first crossing approaches r=0",
            ),
            local_barrier_supported=True,
            global_proof_closed=False,
            blocker=False,
            clay_navier_stokes_promoted=False,
        ),
        BarrierRow(
            row_id="global_concavity_blocker",
            gate=GATE,
            status="open_blocker",
            ledger_role="global_concavity",
            statement=(
                "The route lacks a global theorem that partial_z^2 psi1 keeps "
                "the sign needed to make 2 u1 partial_z^2 psi1 harmless at "
                "every possible first positive maximum of v."
            ),
            maximum_principle_effect=(
                "Without global concavity, the source derivative can be "
                "positive at an off-peak crossing and the barrier does not close."
            ),
            support=(
                "local concavity near the primary axial maximum only",
            ),
            missing_evidence=(
                "GlobalConcavityOfPsi1",
                "transport-stable concavity region",
                "nonlocal Biot-Savart sign preservation",
            ),
            local_barrier_supported=False,
            global_proof_closed=False,
            blocker=True,
            clay_navier_stokes_promoted=False,
        ),
        BarrierRow(
            row_id="secondary_peak_blocker",
            gate=GATE,
            status="open_blocker",
            ledger_role="secondary_peaks",
            statement=(
                "The route lacks an exclusion theorem for secondary axial "
                "peaks or shoulders where v may form a positive local maximum "
                "outside the locally concave primary region."
            ),
            maximum_principle_effect=(
                "A secondary positive crossing can evade the local barrier even "
                "if the primary symmetry-center calculation is valid."
            ),
            support=(
                "none beyond local primary-peak barrier support",
            ),
            missing_evidence=(
                "SecondaryPeakExclusion",
                "single-peak persistence",
                "global monotone rearrangement or comparison principle",
            ),
            local_barrier_supported=False,
            global_proof_closed=False,
            blocker=True,
            clay_navier_stokes_promoted=False,
        ),
    ]
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "gate",
        "status",
        "ledger_role",
        "statement",
        "maximum_principle_effect",
        "support",
        "missing_evidence",
        "local_barrier_supported",
        "global_proof_closed",
        "blocker",
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
    blockers = [row for row in rows if row["blocker"]]
    local_rows = [
        row
        for row in rows
        if row["row_id"]
        in {
            "symmetry_inheritance",
            "first_positive_crossing_criterion",
            "source_derivative_term",
            "local_concavity_support",
            "diffusion_at_positive_max_sign",
        }
    ]
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_by_id))

    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if "2 u1 partial_z^2 psi1" not in row_by_id["source_derivative_term"]["statement"]:
        invariant_failures.append("source_derivative_term_not_encoded")
    if not all(row["local_barrier_supported"] for row in local_rows):
        invariant_failures.append("local_barrier_support_not_encoded")
    if not blockers:
        invariant_failures.append("no_open_blockers")
    if any(row["global_proof_closed"] for row in rows):
        invariant_failures.append("global_proof_incorrectly_closed")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        invariant_failures.append("clay_promotion_detected")

    invariants_passed = not invariant_failures
    global_proof_closed = False
    clay_promoted = False

    return {
        "contract": CONTRACT,
        "gate": GATE,
        "gate_status": "open_blocked_gap",
        "row_count": len(rows),
        "variables": VARIABLES,
        "u1_equation": U1_EQUATION,
        "v_barrier_equation": V_BARRIER_EQUATION,
        "first_positive_crossing_criterion": LOCAL_MAX_CRITERION,
        "route_decision": ROUTE_DECISION,
        "fail_closed": True,
        "conditional": True,
        "artifact_complete": invariants_passed,
        "local_barrier_supported": invariants_passed
        and all(row["local_barrier_supported"] for row in local_rows),
        "global_concavity_closed": False,
        "secondary_peak_excluded": False,
        "global_proof_closed": global_proof_closed,
        "proof_claimed": global_proof_closed,
        "clay_navier_stokes_promoted": clay_promoted,
        "full_clay_ns_solved": False,
        "promotion_decision": "hold_no_clay_promotion",
        "open_blockers": [row["row_id"] for row in blockers],
        "supported_local_rows": [
            row["row_id"] for row in rows if row["local_barrier_supported"]
        ],
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
        "control_card": {
            "O": (
                "Worker owns only the Sprint137 axial monotonicity gate emitter "
                "and its output directory surface."
            ),
            "R": (
                "Model AxialMonotonicityOfSwirlProfile for v=partial_z u1 "
                "without turning local barrier support into a global theorem."
            ),
            "C": (
                "Deterministic Python emitter with rows JSON, rows CSV, summary "
                "JSON, Markdown report, validate(), and main()."
            ),
            "S": (
                "Symmetry, initial sign, first-crossing, differentiated source, "
                "local concavity, and diffusion sign are explicit ledger states."
            ),
            "L": (
                "Local barrier rows are supported; global concavity and "
                "secondary-peak rows remain open blockers."
            ),
            "P": (
                "Keep the route conditional/fail-closed and use it only as a "
                "gate inventory for later Hou-Luo analysis."
            ),
            "G": (
                "Validation passes only if blockers remain open, global proof is "
                "not closed, and Clay promotion is false."
            ),
            "F": (
                "Any missing required row, missing 2u1 partial_z^2 psi1 term, "
                "closed global proof, or Clay promotion fails validation."
            ),
        },
    }


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    row_ids = {row["row_id"] for row in rows}
    missing = REQUIRED_ROW_IDS.difference(row_ids)
    if missing:
        raise ValueError("missing required rows: " + ", ".join(sorted(missing)))
    if summary["gate"] != GATE:
        raise ValueError("wrong gate in summary")
    if summary["route_decision"] != ROUTE_DECISION:
        raise ValueError("route decision must stay conditional/fail-closed")
    if summary["global_proof_closed"] or summary["proof_claimed"]:
        raise ValueError("global proof must remain open")
    if summary["clay_navier_stokes_promoted"] or summary["full_clay_ns_solved"]:
        raise ValueError("Clay promotion is forbidden")
    if "global_concavity_blocker" not in summary["open_blockers"]:
        raise ValueError("global concavity blocker must remain open")
    if "secondary_peak_blocker" not in summary["open_blockers"]:
        raise ValueError("secondary peak blocker must remain open")
    if "2 u1 partial_z^2 psi1" not in summary["v_barrier_equation"]:
        raise ValueError("source derivative term missing from v ledger equation")
    if summary["invariant_failures"]:
        raise ValueError("; ".join(summary["invariant_failures"]))


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# NS Sprint 137 Axial Monotonicity Gate",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Gate: `{GATE}`",
        f"- Route decision: `{summary['route_decision']}`",
        f"- Local barrier supported: `{str(summary['local_barrier_supported']).lower()}`",
        f"- Global proof closed: `{str(summary['global_proof_closed']).lower()}`",
        f"- Open blockers: `{', '.join(summary['open_blockers'])}`",
        f"- Clay Navier-Stokes promoted: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
        "",
        "## Barrier Equation",
        "",
        f"- `{summary['u1_equation']}`",
        f"- `{summary['v_barrier_equation']}`",
        "",
        "## Rows",
        "",
        "| Row | Status | Role | Statement | Effect |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        statement = row["statement"].replace("|", "\\|")
        effect = row["maximum_principle_effect"].replace("|", "\\|")
        lines.append(
            f"| `{row['row_id']}` | `{row['status']}` | `{row['ledger_role']}` | "
            f"{statement} | {effect} |"
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
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "contract": summary["contract"],
                "exit_code": summary["exit_code"],
                "global_proof_closed": summary["global_proof_closed"],
                "local_barrier_supported": summary["local_barrier_supported"],
                "open_blockers": summary["open_blockers"],
                "route_decision": summary["route_decision"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
