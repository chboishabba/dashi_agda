#!/usr/bin/env python3
"""Sprint 149 energy-width lower-bound analytic ledger emitter.

This deterministic stdlib emitter records the energy-monotonicity route toward
ScalingConsistencyForHouLuoConcentration.  It normalizes candidate lower-width
inequalities of the form delta(t) >= c tau^alpha, compares them against
energy/enstrophy/dissipation and viscous-width constraints, and explicitly
records why energy control alone does not prove alpha < 1.

It is an analytic ledger, not a theorem prover.  It emits fail-closed flags:
no energy-width theorem, no alpha < 1 theorem, no scaling-consistency theorem,
no full Clay Navier-Stokes solution, and no Clay promotion.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint149_energy_width_lower_bound"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint149_energy_width_lower_bound")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 149
LANE = 4
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
TARGET_THEOREM = "ScalingConsistencyForHouLuoConcentration"
MISSING_ENERGY_THEOREM = "EnergyWidthLowerBoundForHouLuoConcentration"
MISSING_ALPHA_THEOREM = "AlphaLessThanOneForHouLuoConcentration"
MISSING_SCALING_THEOREM = TARGET_THEOREM
DECISION = "fail_closed_energy_width_lower_bound_not_proved"
PROMOTION_DECISION = "hold_no_clay_promotion"

TAU = "tau = T - t"
DELTA_LOWER_BOUND = "delta(t) >= c_delta * tau^alpha"
CONCENTRATION_ANSATZ = (
    "active width delta(t), vorticity scale Omega(t) ~ tau^-1, "
    "velocity increment U_delta(t) ~ Omega(t)*delta(t)"
)
ENERGY_WIDTH_INEQUALITY = (
    "E_delta(t) ~ Omega(t)^2 * delta(t)^5 <= E0 implies "
    "delta(t) >= C_E * tau^(2/5) only under the active localized ansatz"
)
ENSTROPHY_WIDTH_INEQUALITY = (
    "Z_delta(t) ~ Omega(t)^2 * delta(t)^3; pointwise bounded enstrophy would "
    "force alpha >= 2/3, while finite dissipation integral only gives "
    "alpha > 1/3 under the same ansatz"
)
VISCOUS_WIDTH_INEQUALITY = (
    "delta(t) >= C_nu * sqrt(nu*tau) corresponds to alpha <= 1/2 for small tau "
    "when constants are uniform and c_delta is positive"
)
ALPHA_LESS_THAN_ONE_OBSTRUCTION = (
    "Energy monotonicity supplies an exponent lower bound such as alpha >= 2/5; "
    "it does not supply an upper bound alpha < 1 without a separate viscous, "
    "transport, or concentration-persistence theorem"
)
GRONWALL_CLOSURE_STATEMENT = (
    "Gronwall closure is conditional on importing a proved lower-width theorem "
    "with constants compatible with the Hou-Luo concentration bootstrap"
)

REQUIRED_ROW_IDS = {
    "delta_power_law_normalization",
    "energy_monotonicity_width_constraint",
    "enstrophy_width_constraint",
    "viscous_lower_width_candidate",
    "energy_alone_alpha_less_than_one_gap",
    "scaling_consistency_theorem_absent",
    "conditional_gronwall_closure",
}

SUMMARY_REQUIRED_FALSE = {
    "energy_width_lower_bound_proved",
    "alpha_less_than_one_proved",
    "scaling_consistency_proved",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
}

THEOREM_SEARCH_PATTERNS = (
    TARGET_THEOREM,
    MISSING_ENERGY_THEOREM,
    MISSING_ALPHA_THEOREM,
)

CONTROL_CARD = {
    "O": (
        "Sprint 149 worker lane 4 owns only "
        "scripts/ns_sprint149_energy_width_lower_bound.py and "
        "outputs/ns_sprint149_energy_width_lower_bound/."
    ),
    "R": (
        "Emit a deterministic analytic ledger for the energy monotonicity route "
        "to ScalingConsistencyForHouLuoConcentration, including explicit absent-theorem blockers."
    ),
    "C": (
        "Single stdlib Python emitter writes rows JSON, rows CSV, summary JSON, "
        "Markdown report, and manifest with stable hashes."
    ),
    "S": (
        "The current state is fail-closed: energy/enstrophy formulas normalize "
        "candidate exponent bounds, but no proved lower-width or alpha < 1 theorem is present."
    ),
    "L": (
        "delta >= c*tau^alpha normalization -> energy lower exponent candidate -> "
        "enstrophy/dissipation candidate -> viscous lower-width candidate -> "
        "alpha < 1 gap -> missing scaling-consistency theorem."
    ),
    "P": (
        "Use this artifact as an obligation ledger for future proof work, not as "
        "a closed analytic theorem or a Clay promotion surface."
    ),
    "G": (
        "Validation passes only when all required rows are present, requested "
        "proof/promotion flags remain false, gronwall_closure_conditional and "
        "artifact_complete are true, and absent-theorem blockers are explicit."
    ),
    "F": (
        "Missing EnergyWidthLowerBoundForHouLuoConcentration, "
        "AlphaLessThanOneForHouLuoConcentration, and a proved "
        "ScalingConsistencyForHouLuoConcentration closure."
    ),
}


@dataclass(frozen=True)
class LedgerRow:
    row_id: str
    ledger_role: str
    normalized_inequality: str
    derived_exponent_constraint: str
    status: str
    support: tuple[str, ...]
    blockers: tuple[str, ...]
    missing_theorem: tuple[str, ...]
    implies_delta_lower_bound: bool
    implies_alpha_lower_bound: bool
    implies_alpha_upper_bound: bool
    implies_alpha_less_than_one: bool
    energy_based: bool
    enstrophy_based: bool
    viscous_based: bool
    conditional_for_gronwall: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        for key in ("support", "blockers", "missing_theorem"):
            row[key] = list(row[key])
        row["contract"] = CONTRACT
        row["sprint"] = SPRINT
        row["lane"] = LANE
        row["program"] = PROGRAM
        row["target_theorem"] = TARGET_THEOREM
        row["tau_definition"] = TAU
        row["delta_lower_bound_form"] = DELTA_LOWER_BOUND
        row["concentration_ansatz"] = CONCENTRATION_ANSATZ
        row["energy_width_lower_bound_proved"] = False
        row["alpha_less_than_one_proved"] = False
        row["scaling_consistency_proved"] = False
        row["gronwall_closure_conditional"] = True
        row["full_clay_ns_solved"] = False
        row["clay_navier_stokes_promoted"] = False
        row["artifact_complete"] = True
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["promotion_allowed"] = False
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


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
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


def theorem_presence_state(repo_root: Path) -> dict[str, dict[str, Any]]:
    search_roots = [repo_root / "DASHI", repo_root / "scripts", repo_root / "outputs"]
    self_path = Path(__file__).resolve()
    generated_out_dir = (repo_root / OUT_DIR_DEFAULT).resolve()
    state: dict[str, dict[str, Any]] = {}
    for pattern in THEOREM_SEARCH_PATTERNS:
        matches: list[str] = []
        proved_false_witnesses: list[str] = []
        for root in search_roots:
            if not root.exists():
                continue
            for path in sorted(root.rglob("*")):
                resolved = path.resolve()
                if resolved == self_path or generated_out_dir in resolved.parents:
                    continue
                if path.is_dir() or path.stat().st_size > 2_000_000:
                    continue
                if path.suffix not in {".agda", ".py", ".json", ".md", ".csv"}:
                    continue
                try:
                    text = path.read_text(encoding="utf-8")
                except UnicodeDecodeError:
                    continue
                if pattern in text:
                    relative = display_path(path, repo_root)
                    matches.append(relative)
                    if (
                        pattern == TARGET_THEOREM
                        and "ScalingConsistencyForHouLuoConcentrationProved" in text
                        and "ScalingConsistencyForHouLuoConcentrationProved = false" in text
                    ):
                        proved_false_witnesses.append(relative)
        state[pattern] = {
            "present_outside_this_emitter": bool(matches),
            "matches": matches[:20],
            "match_count": len(matches),
            "proved_false_witness_seen": bool(proved_false_witnesses),
            "proved_false_witnesses": proved_false_witnesses[:20],
        }
    return state


def build_rows() -> list[dict[str, Any]]:
    rows = [
        LedgerRow(
            row_id="delta_power_law_normalization",
            ledger_role="normalize_candidate_width_law",
            normalized_inequality=DELTA_LOWER_BOUND,
            derived_exponent_constraint="alpha is the width exponent in tau; smaller alpha means wider scale as tau -> 0",
            status="normalized_not_proved",
            support=("standard blowup-time notation", "Hou-Luo active-width bookkeeping"),
            blockers=("no theorem supplies c_delta > 0 uniformly on the concentration interval",),
            missing_theorem=(MISSING_ENERGY_THEOREM,),
            implies_delta_lower_bound=False,
            implies_alpha_lower_bound=False,
            implies_alpha_upper_bound=False,
            implies_alpha_less_than_one=False,
            energy_based=False,
            enstrophy_based=False,
            viscous_based=False,
            conditional_for_gronwall=True,
        ),
        LedgerRow(
            row_id="energy_monotonicity_width_constraint",
            ledger_role="energy_lower_exponent_candidate",
            normalized_inequality=ENERGY_WIDTH_INEQUALITY,
            derived_exponent_constraint="alpha >= 2/5 in the localized Omega ~ tau^-1 ansatz",
            status="candidate_only_energy_does_not_close_width_theorem",
            support=("L2 energy is nonincreasing for smooth Navier-Stokes solutions", CONCENTRATION_ANSATZ),
            blockers=(
                "requires localization and amplitude-to-width ansatz not proved as a theorem",
                "gives a lower bound on alpha, not the needed alpha < 1 upper bound",
                "does not prevent wider concentration laws such as alpha >= 1",
            ),
            missing_theorem=(MISSING_ENERGY_THEOREM, MISSING_SCALING_THEOREM),
            implies_delta_lower_bound=True,
            implies_alpha_lower_bound=True,
            implies_alpha_upper_bound=False,
            implies_alpha_less_than_one=False,
            energy_based=True,
            enstrophy_based=False,
            viscous_based=False,
            conditional_for_gronwall=True,
        ),
        LedgerRow(
            row_id="enstrophy_width_constraint",
            ledger_role="enstrophy_and_dissipation_candidate",
            normalized_inequality=ENSTROPHY_WIDTH_INEQUALITY,
            derived_exponent_constraint="pointwise enstrophy bound suggests alpha >= 2/3; finite dissipation integral suggests alpha > 1/3",
            status="conditional_candidate_not_available_as_pointwise_theorem",
            support=("enstrophy scaling Z_delta ~ Omega^2 delta^3", "energy identity includes nu*integral Z(t) dt"),
            blockers=(
                "3D enstrophy is not known to be uniformly bounded up to a possible singular time",
                "time-integrated dissipation does not give pointwise lower width without persistence information",
                "still supplies lower exponent bounds rather than alpha < 1",
            ),
            missing_theorem=("PointwiseEnstrophyWidthLowerBoundForHouLuoConcentration", MISSING_ALPHA_THEOREM),
            implies_delta_lower_bound=True,
            implies_alpha_lower_bound=True,
            implies_alpha_upper_bound=False,
            implies_alpha_less_than_one=False,
            energy_based=False,
            enstrophy_based=True,
            viscous_based=False,
            conditional_for_gronwall=True,
        ),
        LedgerRow(
            row_id="viscous_lower_width_candidate",
            ledger_role="viscous_diffusion_width_gate",
            normalized_inequality=VISCOUS_WIDTH_INEQUALITY,
            derived_exponent_constraint="a proved parabolic lower width delta >= C*sqrt(nu*tau) would imply alpha <= 1/2, hence alpha < 1",
            status="right_shape_for_alpha_less_than_one_but_theorem_absent",
            support=("parabolic diffusion length heuristic", "viscosity prevents arbitrarily thin persistent active scales if a comparison theorem is proved"),
            blockers=(
                "no localized viscous lower-width theorem is present for the Hou-Luo active concentration set",
                "transport and nonlocal stretching can move the active scale, so heat-length intuition is not enough",
                "constant compatibility with the concentration bootstrap is absent",
            ),
            missing_theorem=("ViscousLowerWidthForHouLuoConcentration", MISSING_ALPHA_THEOREM),
            implies_delta_lower_bound=True,
            implies_alpha_lower_bound=False,
            implies_alpha_upper_bound=True,
            implies_alpha_less_than_one=False,
            energy_based=False,
            enstrophy_based=False,
            viscous_based=True,
            conditional_for_gronwall=True,
        ),
        LedgerRow(
            row_id="energy_alone_alpha_less_than_one_gap",
            ledger_role="alpha_less_than_one_obstruction",
            normalized_inequality=ALPHA_LESS_THAN_ONE_OBSTRUCTION,
            derived_exponent_constraint="energy alone permits alpha >= 1; therefore it does not prove alpha < 1",
            status="blocked_energy_alone_insufficient",
            support=("energy monotonicity is an upper bound on L2 mass", "candidate energy scaling yields alpha >= 2/5"),
            blockers=(
                "alpha < 1 is an upper exponent statement",
                "energy monotonicity has no built-in lower amplitude persistence on the active Hou-Luo scale",
                "a separate viscous or transport theorem is required",
            ),
            missing_theorem=(MISSING_ALPHA_THEOREM, MISSING_SCALING_THEOREM),
            implies_delta_lower_bound=False,
            implies_alpha_lower_bound=False,
            implies_alpha_upper_bound=False,
            implies_alpha_less_than_one=False,
            energy_based=True,
            enstrophy_based=False,
            viscous_based=False,
            conditional_for_gronwall=True,
        ),
        LedgerRow(
            row_id="scaling_consistency_theorem_absent",
            ledger_role="target_theorem_blocker",
            normalized_inequality=f"{TARGET_THEOREM} requires a proved width law plus alpha < 1 compatibility",
            derived_exponent_constraint="not derivable from this ledger",
            status="target_theorem_absent_fail_closed",
            support=("normalized candidate inequalities are recorded",),
            blockers=(
                f"{TARGET_THEOREM} is recorded as an open/false gate where present",
                f"{MISSING_ENERGY_THEOREM} not found as a closed theorem in scanned repo surfaces",
                f"{MISSING_ALPHA_THEOREM} not found as a closed theorem in scanned repo surfaces",
            ),
            missing_theorem=(MISSING_ENERGY_THEOREM, MISSING_ALPHA_THEOREM, MISSING_SCALING_THEOREM),
            implies_delta_lower_bound=False,
            implies_alpha_lower_bound=False,
            implies_alpha_upper_bound=False,
            implies_alpha_less_than_one=False,
            energy_based=True,
            enstrophy_based=True,
            viscous_based=True,
            conditional_for_gronwall=True,
        ),
        LedgerRow(
            row_id="conditional_gronwall_closure",
            ledger_role="conditional_downstream_closure",
            normalized_inequality=GRONWALL_CLOSURE_STATEMENT,
            derived_exponent_constraint="closure remains conditional until the missing width and alpha theorems are imported",
            status="conditional_only",
            support=("candidate inequalities identify the required constant interfaces",),
            blockers=(
                "Gronwall constants depend on a proved positive width constant",
                "no closed alpha < 1 proof is available",
                "conditional closure cannot be promoted to Clay Navier-Stokes",
            ),
            missing_theorem=(MISSING_ENERGY_THEOREM, MISSING_ALPHA_THEOREM, MISSING_SCALING_THEOREM),
            implies_delta_lower_bound=False,
            implies_alpha_lower_bound=False,
            implies_alpha_upper_bound=False,
            implies_alpha_less_than_one=False,
            energy_based=False,
            enstrophy_based=False,
            viscous_based=False,
            conditional_for_gronwall=True,
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]], theorem_state: dict[str, dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["row_id"]: row for row in rows}
    missing_required = sorted(REQUIRED_ROW_IDS.difference(row_by_id))
    extra_rows = sorted(set(row_by_id).difference(REQUIRED_ROW_IDS))
    row_hashes = {row["row_id"]: row["row_hash"] for row in rows}
    absent_theorems = [
        name for name, state in theorem_state.items() if not state["present_outside_this_emitter"]
    ]
    invariant_failures: list[str] = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if extra_rows:
        invariant_failures.append("unexpected_rows:" + ",".join(extra_rows))
    for flag in SUMMARY_REQUIRED_FALSE:
        if any(row[flag] for row in rows):
            invariant_failures.append(f"row_sets_{flag}_true")
    if not all(row["gronwall_closure_conditional"] for row in rows):
        invariant_failures.append("nonconditional_gronwall_row_detected")
    if not row_by_id.get("energy_monotonicity_width_constraint", {}).get("energy_based"):
        invariant_failures.append("energy_constraint_row_missing_energy_basis")
    if row_by_id.get("energy_monotonicity_width_constraint", {}).get("implies_alpha_less_than_one"):
        invariant_failures.append("energy_row_incorrectly_implies_alpha_less_than_one")
    if not row_by_id.get("viscous_lower_width_candidate", {}).get("implies_alpha_upper_bound"):
        invariant_failures.append("viscous_row_missing_alpha_upper_bound_shape")
    if row_by_id.get("viscous_lower_width_candidate", {}).get("implies_alpha_less_than_one"):
        invariant_failures.append("viscous_row_incorrectly_marks_theorem_proved")
    for theorem in (MISSING_ENERGY_THEOREM, MISSING_ALPHA_THEOREM):
        if theorem not in absent_theorems:
            invariant_failures.append(f"theorem_not_absent_as_expected:{theorem}")
    target_state = theorem_state[TARGET_THEOREM]
    if not target_state["present_outside_this_emitter"]:
        invariant_failures.append(f"target_gate_absent:{TARGET_THEOREM}")

    invariants_passed = not invariant_failures
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "target_theorem": TARGET_THEOREM,
        "decision": DECISION,
        "promotion_decision": PROMOTION_DECISION,
        "tau_definition": TAU,
        "delta_lower_bound_form": DELTA_LOWER_BOUND,
        "concentration_ansatz": CONCENTRATION_ANSATZ,
        "energy_width_inequality": ENERGY_WIDTH_INEQUALITY,
        "enstrophy_width_inequality": ENSTROPHY_WIDTH_INEQUALITY,
        "viscous_width_inequality": VISCOUS_WIDTH_INEQUALITY,
        "alpha_less_than_one_obstruction": ALPHA_LESS_THAN_ONE_OBSTRUCTION,
        "gronwall_closure_statement": GRONWALL_CLOSURE_STATEMENT,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": [row["row_id"] for row in rows],
        "missing_required_row_ids": missing_required,
        "extra_row_ids": extra_rows,
        "theorem_presence_state": theorem_state,
        "absent_theorems": absent_theorems,
        "blockers": [
            MISSING_ENERGY_THEOREM,
            MISSING_ALPHA_THEOREM,
            MISSING_SCALING_THEOREM,
            "energy_monotonicity_does_not_imply_alpha_less_than_one",
            "viscous_lower_width_theorem_absent",
        ],
        "energy_width_lower_bound_proved": False,
        "alpha_less_than_one_proved": False,
        "scaling_consistency_proved": False,
        "gronwall_closure_conditional": True,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "clay_promoted": False,
        "promotion_allowed": False,
        "no_promotion": True,
        "artifact_complete": invariants_passed,
        "invariants_passed": invariants_passed,
        "invariant_valid": invariants_passed,
        "invariant_checked": True,
        "invariant_failures": invariant_failures,
        "row_hashes": row_hashes,
        "rows_hash": stable_hash(rows),
        "control_card": CONTROL_CARD,
        "summary_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "row_hashes": row_hashes,
                "absent_theorems": absent_theorems,
                "flags": {
                    "energy_width_lower_bound_proved": False,
                    "alpha_less_than_one_proved": False,
                    "scaling_consistency_proved": False,
                    "gronwall_closure_conditional": True,
                    "full_clay_ns_solved": False,
                    "clay_navier_stokes_promoted": False,
                    "artifact_complete": invariants_passed,
                },
            }
        ),
        "exit_code": 0 if invariants_passed else 1,
    }
    return summary


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    if summary["contract"] != CONTRACT:
        raise ValueError("wrong contract")
    row_ids = {row["row_id"] for row in rows}
    missing = REQUIRED_ROW_IDS.difference(row_ids)
    if missing:
        raise ValueError("missing required rows: " + ", ".join(sorted(missing)))
    extra = row_ids.difference(REQUIRED_ROW_IDS)
    if extra:
        raise ValueError("unexpected rows: " + ", ".join(sorted(extra)))
    for key in SUMMARY_REQUIRED_FALSE:
        if summary[key]:
            raise ValueError(f"{key} must remain false")
        for row in rows:
            if row[key]:
                raise ValueError(f"row {row['row_id']} incorrectly sets {key}=true")
    if not summary["gronwall_closure_conditional"]:
        raise ValueError("gronwall closure must remain conditional")
    if not summary["artifact_complete"]:
        raise ValueError("artifact_complete must be true")
    if not summary["invariants_passed"] or not summary["invariant_valid"]:
        raise ValueError("invariants must pass")
    if summary["promotion_allowed"] or not summary["no_promotion"]:
        raise ValueError("promotion must remain forbidden")
    if summary["invariant_failures"]:
        raise ValueError("invariant failures present: " + ", ".join(summary["invariant_failures"]))


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = list(rows[0].keys())
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = {
                key: "; ".join(value) if isinstance(value, list) else value
                for key, value in row.items()
            }
            writer.writerow(serializable)


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 149 Energy-Width Lower Bound",
        "",
        f"- Contract: `{CONTRACT}`",
        f"- Decision: `{DECISION}`",
        f"- Target theorem: `{TARGET_THEOREM}`",
        f"- Promotion: `{PROMOTION_DECISION}`",
        "",
        "## Normalized Inequalities",
        "",
        f"- Width law: `{DELTA_LOWER_BOUND}`",
        f"- Energy: `{ENERGY_WIDTH_INEQUALITY}`",
        f"- Enstrophy: `{ENSTROPHY_WIDTH_INEQUALITY}`",
        f"- Viscous: `{VISCOUS_WIDTH_INEQUALITY}`",
        f"- Alpha gap: `{ALPHA_LESS_THAN_ONE_OBSTRUCTION}`",
        "",
        "## Rows",
        "",
        "| row_id | status | exponent constraint | alpha<1 |",
        "|---|---|---|---:|",
    ]
    for row in rows:
        lines.append(
            "| {row_id} | {status} | {derived_exponent_constraint} | {alpha} |".format(
                row_id=row["row_id"],
                status=row["status"],
                derived_exponent_constraint=row["derived_exponent_constraint"],
                alpha=str(row["implies_alpha_less_than_one"]).lower(),
            )
        )
    lines.extend(
        [
            "",
            "## Required Flags",
            "",
            f"- `energy_width_lower_bound_proved`: `{str(summary['energy_width_lower_bound_proved']).lower()}`",
            f"- `alpha_less_than_one_proved`: `{str(summary['alpha_less_than_one_proved']).lower()}`",
            f"- `scaling_consistency_proved`: `{str(summary['scaling_consistency_proved']).lower()}`",
            f"- `gronwall_closure_conditional`: `{str(summary['gronwall_closure_conditional']).lower()}`",
            f"- `full_clay_ns_solved`: `{str(summary['full_clay_ns_solved']).lower()}`",
            f"- `clay_navier_stokes_promoted`: `{str(summary['clay_navier_stokes_promoted']).lower()}`",
            f"- `artifact_complete`: `{str(summary['artifact_complete']).lower()}`",
            "",
            "## O/R/C/S/L/P/G/F",
            "",
        ]
    )
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- `{key}`: {summary['control_card'][key]}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / SUMMARY_NAME,
        "rows_json": out_dir / ROWS_JSON_NAME,
        "rows_csv": out_dir / ROWS_CSV_NAME,
        "report": out_dir / REPORT_NAME,
    }
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "decision": DECISION,
        "artifact_complete": summary["artifact_complete"],
        "invariants_passed": summary["invariants_passed"],
        "files": {
            key: {
                "path": display_path(path, repo_root),
                "sha256": file_sha256(path),
            }
            for key, path in files.items()
        },
    }
    manifest["manifest_payload_hash_without_self"] = stable_hash(
        {k: v for k, v in manifest.items() if k != "manifest_payload_hash_without_self"}
    )
    return manifest


def atomic_emit(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> dict[str, Any]:
    out_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=CONTRACT + ".", dir=out_dir.parent) as tmp_name:
        tmp_dir = Path(tmp_name)
        write_json(tmp_dir / SUMMARY_NAME, summary)
        write_json(tmp_dir / ROWS_JSON_NAME, rows)
        write_csv(tmp_dir / ROWS_CSV_NAME, rows)
        (tmp_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")
        write_json(tmp_dir / MANIFEST_NAME, build_manifest(repo_root, tmp_dir, summary))
        if out_dir.exists():
            shutil.rmtree(out_dir)
        os.replace(tmp_dir, out_dir)

    manifest = build_manifest(repo_root, out_dir, summary)
    write_json(out_dir / MANIFEST_NAME, manifest)
    return manifest


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir

    rows = build_rows()
    theorem_state = theorem_presence_state(repo_root)
    summary = build_summary(rows, theorem_state)
    validate(summary, rows)
    manifest = atomic_emit(repo_root, out_dir, rows, summary)
    print(json.dumps({"summary": summary, "manifest": manifest}, indent=2, sort_keys=True))
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
