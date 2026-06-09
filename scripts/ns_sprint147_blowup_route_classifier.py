#!/usr/bin/env python3
"""Sprint 147 post-Sprint146 NS blowup route classifier.

This deterministic emitter classifies the route state after Sprint 146.  It is
an accounting artifact, not a proof artifact: the WBF tower is publishable as a
route packet, the exact Gamma and symmetry-plane facts are recorded, the
maximum-location migration exclusion has failed, the migration-driven blowup
structure is identified, the large-data migration threshold is the highest-alpha
next gate, and full Clay Navier-Stokes is not solved or promoted.
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


CONTRACT = "ns_sprint147_blowup_route_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint147_blowup_route_classifier")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 147
LANE = 6
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
STATE_BASIS = "post_sprint146"
DECISION = "classify_post_sprint146_blowup_routes_fail_closed"

REQUIRED_ROUTE_IDS = {
    "wbf_tower",
    "gamma_max_principle",
    "pure_diffusion_at_symmetry_plane",
    "maximum_location_migration_exclusion_for_v_barrier",
    "migration_driven_blowup_structure",
    "migration_initiation_threshold_for_large_data",
    "full_clay_navier_stokes",
}

SOURCE_ARTIFACTS = {
    "sprint135_hou_luo_blowup_gate_classifier": (
        "outputs/ns_sprint135_hou_luo_blowup_gate_classifier/"
        "ns_sprint135_hou_luo_blowup_gate_classifier_summary.json"
    ),
    "sprint146_maximum_location_migration_gate": (
        "outputs/ns_sprint146_maximum_location_migration_gate/"
        "ns_sprint146_maximum_location_migration_gate_summary.json"
    ),
}

CONTROL_CARD = {
    "O": (
        "Lane 6 owns only the Sprint 147 route-classifier script and generated "
        "outputs/ns_sprint147_blowup_route_classifier/ artifacts."
    ),
    "R": (
        "Classify the post-Sprint146 route state exactly: WBF publishable, "
        "Gamma exact, symmetry-plane pure diffusion exact, migration exclusion "
        "failed, migration-driven structure identified, highest-alpha next gate "
        "selected, and Clay unpromoted."
    ),
    "C": (
        "Single stdlib Python emitter writes rows JSON, rows CSV, summary JSON, "
        "Markdown, and manifest through an atomic staging directory."
    ),
    "S": (
        "The state is not a Clay solution: exact local/control facts coexist "
        "with a failed global maximum-location exclusion and a live threshold gate."
    ),
    "L": (
        "Use fixed route rows, validate required classifications and false "
        "promotion flags, then fail closed if any invariant is missing."
    ),
    "P": (
        "Treat this as a deterministic route packet for Sprint 147 planning, "
        "not as a theorem prover or promotion mechanism."
    ),
    "G": (
        "Validation passes only when all seven required route ids are present, "
        "the requested classifications match exactly, highest-alpha is unique, "
        "and all Clay solved/promoted flags remain false."
    ),
    "F": (
        "Missing: MigrationInitiationThresholdForLargeData proof and the "
        "downstream global Clay Navier-Stokes promotion evidence."
    ),
}


@dataclass(frozen=True)
class RouteRow:
    route_id: str
    route_name: str
    classification: str
    status: str
    alpha_priority: int
    exact: bool
    publishable: bool
    failed: bool
    identified: bool
    next_gate: bool
    highest_alpha_next_gate: bool
    proof_claim: str
    evidence_basis: tuple[str, ...]
    blocker_or_gap: str
    downstream_action: str
    full_clay_ns_solved: bool = False
    clay_navier_stokes_promoted: bool = False
    promotion_allowed: bool = False

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["sprint"] = SPRINT
        row["lane"] = LANE
        row["contract"] = CONTRACT
        row["program"] = PROGRAM
        row["state_basis"] = STATE_BASIS
        row["decision"] = DECISION
        row["evidence_basis"] = list(self.evidence_basis)
        row["claim_closed"] = self.exact or self.publishable or self.failed or self.identified
        row["claim_proved"] = self.exact
        row["claim_proven"] = self.exact
        row["no_global_proof"] = True
        row["no_promotion"] = True
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


def source_artifact_state(repo_root: Path) -> dict[str, dict[str, Any]]:
    state: dict[str, dict[str, Any]] = {}
    for key, relative in SOURCE_ARTIFACTS.items():
        path = repo_root / relative
        entry: dict[str, Any] = {
            "path": relative,
            "exists": path.exists(),
            "sha256": file_sha256(path),
        }
        if path.exists():
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                payload = {}
            for flag in (
                "route_status",
                "decision",
                "maximum_location_migration_lemma_proved",
                "migration_gate_closed",
                "global_barrier_closed",
                "full_clay_ns_solved",
                "clay_navier_stokes_promoted",
                "promotion_allowed",
            ):
                if flag in payload:
                    entry[flag] = payload[flag]
        state[key] = entry
    return state


def build_rows() -> list[dict[str, Any]]:
    rows = [
        RouteRow(
            route_id="wbf_tower",
            route_name="WBF tower",
            classification="publishable",
            status="PUBLISHABLE_ROUTE_PACKET",
            alpha_priority=60,
            exact=False,
            publishable=True,
            failed=False,
            identified=True,
            next_gate=False,
            highest_alpha_next_gate=False,
            proof_claim=(
                "The WBF tower can be published as the current organized route "
                "packet, with no Clay promotion attached."
            ),
            evidence_basis=(
                "post-Sprint146 route ledger",
                "Sprint135 corrected Hou-Luo gate taxonomy",
                "Sprint146 migration gate packet",
            ),
            blocker_or_gap="not_a_full_solution; downstream migration threshold remains open",
            downstream_action="publish_route_packet_without_promotion",
        ),
        RouteRow(
            route_id="gamma_max_principle",
            route_name="Gamma max principle",
            classification="exact",
            status="EXACT_CONTROL_FACT",
            alpha_priority=90,
            exact=True,
            publishable=True,
            failed=False,
            identified=True,
            next_gate=False,
            highest_alpha_next_gate=False,
            proof_claim=(
                "Gamma = r u^theta = r^2 u1 is the exact maximum-principle "
                "variable; u1 itself is controlled only through annular conversion."
            ),
            evidence_basis=(
                "Sprint134 corrected variable accounting",
                "Sprint135 Hou-Luo blowup gate classifier",
            ),
            blocker_or_gap="Gamma upper control does not prove active annular u1 lower persistence",
            downstream_action="use_as_exact_constraint_for_all_route_rows",
        ),
        RouteRow(
            route_id="pure_diffusion_at_symmetry_plane",
            route_name="PureDiffusionAtSymmetryPlane",
            classification="exact",
            status="EXACT_LOCAL_FACT",
            alpha_priority=80,
            exact=True,
            publishable=True,
            failed=False,
            identified=True,
            next_gate=False,
            highest_alpha_next_gate=False,
            proof_claim=(
                "At the pinned symmetry plane the v-barrier reduces to the "
                "pure-diffusion/local damping fact used by the route packet."
            ),
            evidence_basis=(
                "Sprint145 comparison-envelope obstruction",
                "Sprint146 pinned_center local-support row",
            ),
            blocker_or_gap="exact only while the first maximum remains pinned",
            downstream_action="retain_as_local_support_not_global_barrier",
        ),
        RouteRow(
            route_id="maximum_location_migration_exclusion_for_v_barrier",
            route_name="MaximumLocationMigrationExclusionForVBarrier",
            classification="failed",
            status="FAILED_GLOBAL_EXCLUSION",
            alpha_priority=100,
            exact=False,
            publishable=True,
            failed=True,
            identified=True,
            next_gate=False,
            highest_alpha_next_gate=False,
            proof_claim=(
                "The route cannot exclude off-center migration of the first "
                "positive maximum of v = partial_z u1 after Sprint146."
            ),
            evidence_basis=(
                "Sprint146 symmetric_twin_peak_migration row",
                "Sprint146 positive_feedback_candidate row",
                "Sprint146 regularity_partial_recovery_branch row",
            ),
            blocker_or_gap="MaximumLocationMigrationLemma remains unproved",
            downstream_action="do_not_use_global_v_barrier_as_closed",
        ),
        RouteRow(
            route_id="migration_driven_blowup_structure",
            route_name="MigrationDrivenBlowupStructure",
            classification="identified",
            status="IDENTIFIED_LIVE_STRUCTURE",
            alpha_priority=110,
            exact=False,
            publishable=True,
            failed=False,
            identified=True,
            next_gate=False,
            highest_alpha_next_gate=False,
            proof_claim=(
                "The failed exclusion identifies the live structure: blowup, if "
                "pursued on this route, must be driven through controlled "
                "migration and positive nonlocal feedback rather than a pinned "
                "symmetry-plane maximum principle."
            ),
            evidence_basis=(
                "Sprint146 source-sign split",
                "Sprint146 maximum-location velocity proxy",
            ),
            blocker_or_gap="structure identified but not converted to BKM divergence",
            downstream_action="route_future_work_through_migration_threshold_gate",
        ),
        RouteRow(
            route_id="migration_initiation_threshold_for_large_data",
            route_name="MigrationInitiationThresholdForLargeData",
            classification="highest-alpha next gate",
            status="HIGHEST_ALPHA_NEXT_GATE",
            alpha_priority=120,
            exact=False,
            publishable=True,
            failed=False,
            identified=True,
            next_gate=True,
            highest_alpha_next_gate=True,
            proof_claim=(
                "The next gate is a quantitative large-data threshold that "
                "initiates and controls maximum migration strongly enough to "
                "feed the identified blowup structure."
            ),
            evidence_basis=(
                "Gamma exact upper constraint",
                "PureDiffusionAtSymmetryPlane exact local constraint",
                "MaximumLocationMigrationExclusionForVBarrier failed",
                "MigrationDrivenBlowupStructure identified",
            ),
            blocker_or_gap="no threshold theorem, no bootstrap entry, no BKM divergence verification",
            downstream_action="prioritize_as_highest_alpha_next_gate",
        ),
        RouteRow(
            route_id="full_clay_navier_stokes",
            route_name="Full Clay Navier-Stokes",
            classification="not solved/promoted",
            status="NOT_SOLVED_NOT_PROMOTED",
            alpha_priority=0,
            exact=False,
            publishable=False,
            failed=False,
            identified=True,
            next_gate=False,
            highest_alpha_next_gate=False,
            proof_claim=(
                "The full Clay Navier-Stokes existence/smoothness statement is "
                "not solved, not closed, and not promoted by this route packet."
            ),
            evidence_basis=(
                "fail-closed Sprint147 classifier invariant",
                "open migration threshold gate",
            ),
            blocker_or_gap="Clay proof obligations remain outside this classifier",
            downstream_action="hold_no_clay_promotion",
        ),
    ]
    return [row.as_row() for row in rows]


def validate(rows: list[dict[str, Any]], summary: dict[str, Any] | None = None) -> list[str]:
    failures: list[str] = []
    by_id = {str(row["route_id"]): row for row in rows}
    missing = sorted(REQUIRED_ROUTE_IDS.difference(by_id))
    extra = sorted(set(by_id).difference(REQUIRED_ROUTE_IDS))
    if missing:
        failures.append("missing required route ids: " + ", ".join(missing))
    if extra:
        failures.append("unexpected route ids: " + ", ".join(extra))

    expected_classifications = {
        "wbf_tower": "publishable",
        "gamma_max_principle": "exact",
        "pure_diffusion_at_symmetry_plane": "exact",
        "maximum_location_migration_exclusion_for_v_barrier": "failed",
        "migration_driven_blowup_structure": "identified",
        "migration_initiation_threshold_for_large_data": "highest-alpha next gate",
        "full_clay_navier_stokes": "not solved/promoted",
    }
    for route_id, expected in expected_classifications.items():
        row = by_id.get(route_id)
        if row is not None and row["classification"] != expected:
            failures.append(f"{route_id} classification is {row['classification']!r}, expected {expected!r}")

    highest = [row for row in rows if row["highest_alpha_next_gate"]]
    if [row["route_id"] for row in highest] != ["migration_initiation_threshold_for_large_data"]:
        failures.append("highest-alpha next gate is not unique or not migration threshold")

    if any(row["full_clay_ns_solved"] for row in rows):
        failures.append("a row incorrectly marks full Clay NS solved")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        failures.append("a row incorrectly marks Clay NS promoted")
    if any(row["promotion_allowed"] for row in rows):
        failures.append("a row incorrectly allows promotion")

    if summary is not None:
        for flag in ("full_clay_ns_solved", "clay_navier_stokes_promoted", "promotion_allowed"):
            if summary.get(flag) is not False:
                failures.append(f"summary flag {flag} must be false")
    return failures


def build_summary(rows: list[dict[str, Any]], upstream_state: dict[str, dict[str, Any]]) -> dict[str, Any]:
    route_ids = [str(row["route_id"]) for row in rows]
    status_counts: dict[str, int] = {}
    classification_counts: dict[str, int] = {}
    for row in rows:
        status_counts[str(row["status"])] = status_counts.get(str(row["status"]), 0) + 1
        classification_counts[str(row["classification"])] = (
            classification_counts.get(str(row["classification"]), 0) + 1
        )

    highest = [
        row for row in rows if row["route_id"] == "migration_initiation_threshold_for_large_data"
    ][0]
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "state_basis": STATE_BASIS,
        "decision": DECISION,
        "row_count": len(rows),
        "required_route_ids": sorted(REQUIRED_ROUTE_IDS),
        "observed_route_ids": route_ids,
        "missing_required_route_ids": sorted(REQUIRED_ROUTE_IDS.difference(route_ids)),
        "extra_route_ids": sorted(set(route_ids).difference(REQUIRED_ROUTE_IDS)),
        "status_counts": status_counts,
        "classification_counts": classification_counts,
        "wbf_tower_classification": "publishable",
        "wbf_tower_publishable": True,
        "gamma_max_principle_classification": "exact",
        "gamma_max_principle_exact": True,
        "pure_diffusion_at_symmetry_plane_classification": "exact",
        "pure_diffusion_at_symmetry_plane_exact": True,
        "maximum_location_migration_exclusion_for_v_barrier_classification": "failed",
        "maximum_location_migration_exclusion_for_v_barrier_failed": True,
        "migration_driven_blowup_structure_classification": "identified",
        "migration_driven_blowup_structure_identified": True,
        "migration_initiation_threshold_for_large_data_classification": "highest-alpha next gate",
        "highest_alpha_next_gate": highest["route_name"],
        "highest_alpha_next_gate_route_id": highest["route_id"],
        "highest_alpha_next_gate_alpha_priority": highest["alpha_priority"],
        "full_clay_classification": "not solved/promoted",
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "global_proof": False,
        "global_proof_closed": False,
        "no_global_proof": True,
        "no_promotion": True,
        "fail_closed": True,
        "upstream_artifact_state": upstream_state,
        "control_card": CONTROL_CARD,
        "artifact_complete": False,
        "invariants_passed": False,
        "invariant_checked": False,
        "invariant_valid": False,
        "invariant_failures": [],
    }
    failures = validate(rows, summary)
    summary["invariant_failures"] = failures
    summary["invariant_checked"] = True
    summary["invariant_valid"] = not failures
    summary["invariants_passed"] = not failures
    summary["artifact_complete"] = not failures
    summary["summary_hash"] = stable_hash(
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )
    return summary


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = list(rows[0].keys())
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            normalized = {
                key: json.dumps(value, sort_keys=True) if isinstance(value, list) else value
                for key, value in row.items()
            }
            writer.writerow(normalized)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 147 Blowup Route Classifier",
        "",
        "## Decision",
        "",
        f"- Contract: `{summary['contract']}`",
        f"- Decision: `{summary['decision']}`",
        f"- State basis: `{summary['state_basis']}`",
        f"- Row count: `{summary['row_count']}`",
        f"- Highest-alpha next gate: `{summary['highest_alpha_next_gate']}`",
        f"- Full Clay solved: `{summary['full_clay_ns_solved']}`",
        f"- Clay promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## O/R/C/S/L/P/G/F",
        "",
    ]
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.extend(
        [
            "",
            "## Route Classifications",
            "",
            "| route_id | classification | status | alpha | action |",
            "| --- | --- | --- | ---: | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {route_id} | {classification} | {status} | {alpha_priority} | {downstream_action} |".format(
                **row
            )
        )
    lines.extend(
        [
            "",
            "## Fail-Closed Statement",
            "",
            (
                "This classifier publishes the route state only. It does not solve "
                "or promote the full Clay Navier-Stokes problem; the "
                "MigrationInitiationThresholdForLargeData gate remains open."
            ),
            "",
        ]
    )
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> dict[str, Any]:
    files = [
        out_dir / ROWS_JSON_NAME,
        out_dir / ROWS_CSV_NAME,
        out_dir / SUMMARY_NAME,
        out_dir / REPORT_NAME,
    ]
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "decision": DECISION,
        "artifact_complete": summary["artifact_complete"],
        "invariant_valid": summary["invariant_valid"],
        "row_count": len(rows),
        "files": [
            {
                "path": display_path(path, repo_root),
                "exists": path.exists(),
                "sha256": file_sha256(path),
            }
            for path in files
        ],
    }
    manifest["manifest_hash"] = stable_hash(
        {k: v for k, v in manifest.items() if k != "manifest_hash"}
    )
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    staging_parent = final_out.parent
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=staging_parent))
    try:
        write_json(temp_dir / ROWS_JSON_NAME, rows)
        write_csv(temp_dir / ROWS_CSV_NAME, rows)
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")
        manifest = build_manifest(repo_root, temp_dir, rows, summary)
        write_json(temp_dir / MANIFEST_NAME, manifest)
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        manifest = build_manifest(repo_root, final_out, rows, summary)
        write_json(final_out / MANIFEST_NAME, manifest)
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    rows = build_rows()
    upstream_state = source_artifact_state(repo_root)
    summary = build_summary(rows, upstream_state)
    write_outputs(repo_root, args.out_dir, rows, summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "artifact_complete": summary["artifact_complete"],
                "invariant_valid": summary["invariant_valid"],
                "row_count": summary["row_count"],
                "highest_alpha_next_gate": summary["highest_alpha_next_gate"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "out_dir": display_path(
                    args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir,
                    repo_root,
                ),
            },
            sort_keys=True,
        )
    )
    return 0 if summary["invariant_valid"] else 1


if __name__ == "__main__":
    sys.exit(main())
