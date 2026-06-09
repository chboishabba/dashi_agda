#!/usr/bin/env python3
"""Sprint 135 corrected Navier-Stokes programme status assembly.

This deterministic emitter assembles the post-Sprint-134 correction state into
one canonical status surface.  It reads the expected Sprint 134 summary JSON
files when present, but the emitted mathematical status is not contingent on
those files existing: missing upstream summaries are recorded as observations,
not as permission to revive a retracted claim.

The assembled state is deliberately conservative:

* the exact WBF algebraic obstruction rows remain intact;
* ``PureDiffusionU1MaximumPrinciple`` is retracted/superseded by the
  swirl-circulation maximum principle for ``Gamma = r u^theta``;
* ``NoLogAxisymmetricBiotSavartUniform`` is false as a uniform cylinder lemma;
* ``AxisymmetricHouLuoNSViscousDominanceObstruction`` is retracted;
* the Hou-Luo axisymmetric-with-swirl route is open/live, not proved regular
  and not proved blowup;
* full Clay Navier-Stokes is not solved and is not promoted.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint135_corrected_status_assembly"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint135_corrected_status_assembly")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
UPSTREAM_JSON_NAME = CONTRACT + "_upstream_observations.json"
REPORT_NAME = CONTRACT + ".md"

LIVE_BOUNDARY = "hou_luo_axisymmetric_with_swirl_open_candidate"
PURE_U1_RETRACTION = "PureDiffusionU1MaximumPrinciple"
AXS_OBSTRUCTION_RETRACTION = "AxisymmetricHouLuoNSViscousDominanceObstruction"
FALSE_NO_LOG = "NoLogAxisymmetricBiotSavartUniform"

SPRINT134_SUMMARIES = {
    "axisymmetric_equation_correction": Path(
        "outputs/ns_sprint134_axisymmetric_equation_correction/"
        "ns_sprint134_axisymmetric_equation_correction_summary.json"
    ),
    "biot_savart_log_singularity_audit": Path(
        "outputs/ns_sprint134_biot_savart_log_singularity_audit/"
        "ns_sprint134_biot_savart_log_singularity_audit_summary.json"
    ),
    "hou_luo_retraction_status": Path(
        "outputs/ns_sprint134_hou_luo_retraction_status/"
        "ns_sprint134_hou_luo_retraction_status_summary.json"
    ),
}


@dataclass(frozen=True)
class StatusRow:
    row_id: str
    mechanism_class: str
    claim_or_result: str
    current_status: str
    status_kind: str
    sprint134_dependency: str
    upstream_supported_if_present: bool
    proof_surface: str
    programme_consequence: str
    live_ns_boundary: str
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def read_json_if_present(repo_root: Path, rel_path: Path) -> dict[str, Any] | None:
    path = repo_root / rel_path
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def upstream_observations(repo_root: Path) -> dict[str, Any]:
    observations: dict[str, Any] = {}
    for name, rel_path in SPRINT134_SUMMARIES.items():
        payload = read_json_if_present(repo_root, rel_path)
        observations[name] = {
            "path": str(rel_path),
            "present": payload is not None,
            "contract": payload.get("contract") if payload else None,
            "complete": payload.get("complete") if payload else None,
            "exit_code": payload.get("exit_code") if payload else None,
            "full_clay_ns_solved": payload.get("full_clay_ns_solved") if payload else None,
            "clay_navier_stokes_promoted": (
                payload.get("clay_navier_stokes_promoted") if payload else None
            ),
            "selected_fields": selected_upstream_fields(name, payload),
        }
    return observations


def selected_upstream_fields(name: str, payload: dict[str, Any] | None) -> dict[str, Any]:
    if payload is None:
        return {}
    if name == "axisymmetric_equation_correction":
        keys = (
            "old_u1_pure_diffusion_retracted",
            "u1_equation_has_stretching_source",
            "gamma_maximum_principle_replacement",
            "boundary_annulus_u1_bound",
        )
    elif name == "biot_savart_log_singularity_audit":
        keys = (
            "no_log_axisymmetric_biot_savart_uniform",
            "standard_log_singularity_persists",
            "uniform_away_from_axis_claim_retracted",
            "last_ratio",
        )
    else:
        keys = (
            "axs_viscous_dominance_obstruction_retracted",
            "hou_luo_axisymmetric_ns_route_status",
            "source_may_beat_viscosity",
            "wbf_exact_results_intact",
        )
    return {key: payload.get(key) for key in keys}


def upstream_bool(
    observations: dict[str, Any], source: str, field: str, expected: bool | str
) -> bool:
    value = observations.get(source, {}).get("selected_fields", {}).get(field)
    return value == expected


def build_rows(observations: dict[str, Any]) -> list[dict[str, Any]]:
    equation_supported = upstream_bool(
        observations,
        "axisymmetric_equation_correction",
        "old_u1_pure_diffusion_retracted",
        True,
    )
    no_log_supported = upstream_bool(
        observations,
        "biot_savart_log_singularity_audit",
        "no_log_axisymmetric_biot_savart_uniform",
        False,
    )
    retraction_supported = upstream_bool(
        observations,
        "hou_luo_retraction_status",
        "axs_viscous_dominance_obstruction_retracted",
        True,
    )
    live_route_supported = upstream_bool(
        observations,
        "hou_luo_retraction_status",
        "hou_luo_axisymmetric_ns_route_status",
        "open_live_candidate",
    )

    rows = [
        StatusRow(
            row_id="wbf_exact_tower_intact",
            mechanism_class="CLASS_WBF",
            claim_or_result="WBF-L/WBF-S/WBF-MP/WBF-R",
            current_status="exact_unconditional_intact",
            status_kind="preserved_result",
            sprint134_dependency="independent_of_sprint134_corrections",
            upstream_supported_if_present=True,
            proof_surface=(
                "Algebraic and symmetry obstruction identities: anti-correlation, "
                "self-strain Gram computation, multi-packet Reynolds stress, "
                "and zero-mean rotation cycle."
            ),
            programme_consequence=(
                "The WBF no-go tower remains the intact publishable exact core, "
                "but it is route-specific and not a universal Clay proof."
            ),
            live_ns_boundary=LIVE_BOUNDARY,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        StatusRow(
            row_id="pure_u1_diffusion_retracted",
            mechanism_class="CLASS_AXS",
            claim_or_result=PURE_U1_RETRACTION,
            current_status="retracted_superseded",
            status_kind="retracted_claim",
            sprint134_dependency="ns_sprint134_axisymmetric_equation_correction",
            upstream_supported_if_present=equation_supported,
            proof_surface=(
                "Corrected equation: D_t u1 = 2 u1 partial_z psi1 + "
                "nu Ltilde u1.  The maximum-principle variable is "
                "Gamma = r u^theta = r^2 u1."
            ),
            programme_consequence=(
                "Any theorem using pure diffusion of u1 as a maximum principle "
                "gate is superseded by the Gamma circulation gate plus annulus "
                "conversion."
            ),
            live_ns_boundary=LIVE_BOUNDARY,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        StatusRow(
            row_id="swirl_circulation_gate_intact",
            mechanism_class="CLASS_AXS",
            claim_or_result="SwirlCirculationMaximumPrinciple",
            current_status="exact_replacement_gate_intact",
            status_kind="replacement_gate",
            sprint134_dependency="ns_sprint134_axisymmetric_equation_correction",
            upstream_supported_if_present=upstream_bool(
                observations,
                "axisymmetric_equation_correction",
                "gamma_maximum_principle_replacement",
                True,
            ),
            proof_surface=(
                "(partial_t + u^r partial_r + u^z partial_z) Gamma = "
                "nu (Delta - 2/r partial_r) Gamma; ||Gamma(t)||_inf <= "
                "||Gamma(0)||_inf."
            ),
            programme_consequence=(
                "This gives bounded u1 only after localization to a boundary "
                "annulus r >= r0 > 0; it does not close Hou-Luo by itself."
            ),
            live_ns_boundary=LIVE_BOUNDARY,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        StatusRow(
            row_id="uniform_no_log_false",
            mechanism_class="CLASS_AXS",
            claim_or_result=FALSE_NO_LOG,
            current_status="false_as_uniform_cylinder_lemma",
            status_kind="false_lemma",
            sprint134_dependency="ns_sprint134_biot_savart_log_singularity_audit",
            upstream_supported_if_present=no_log_supported,
            proof_surface=(
                "Complete elliptic integral factor retains "
                "K(k) ~ log(4/sqrt(1-k^2)) as k -> 1; the axis-local "
                "extra-r cancellation is not uniform away from r=0."
            ),
            programme_consequence=(
                "Axisymmetric strain estimates regain the logarithmic loss, "
                "invalidating no-log Gronwall closures."
            ),
            live_ns_boundary=LIVE_BOUNDARY,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        StatusRow(
            row_id="axs_viscous_dominance_obstruction_retracted",
            mechanism_class="CLASS_AXS",
            claim_or_result=AXS_OBSTRUCTION_RETRACTION,
            current_status="retracted",
            status_kind="retracted_claim",
            sprint134_dependency="ns_sprint134_hou_luo_retraction_status",
            upstream_supported_if_present=retraction_supported,
            proof_surface=(
                "The previous obstruction depended on false uniform no-log "
                "Biot-Savart control and the superseded pure-u1 diffusion gate."
            ),
            programme_consequence=(
                "The beta>0 Hou-Luo viscous-dominance obstruction is not a "
                "valid theorem in the current programme state."
            ),
            live_ns_boundary=LIVE_BOUNDARY,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        StatusRow(
            row_id="hou_luo_axisymmetric_with_swirl_open",
            mechanism_class="CLASS_AXS",
            claim_or_result="HouLuoAxisymmetricNSWithSwirlRoute",
            current_status="open_live_candidate",
            status_kind="live_boundary",
            sprint134_dependency="ns_sprint134_hou_luo_retraction_status",
            upstream_supported_if_present=live_route_supported,
            proof_surface=(
                "Corrected log-loss source accounting can make source growth "
                "super-polynomial in 1/tau; no proof currently establishes "
                "either finite-time BKM divergence or global regularity."
            ),
            programme_consequence=(
                "This is the current live NS boundary for the programme: study "
                "Hou-Luo with swirl as an open candidate, not as obstructed."
            ),
            live_ns_boundary=LIVE_BOUNDARY,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        StatusRow(
            row_id="full_clay_status_hold",
            mechanism_class="FULL_3D_NS",
            claim_or_result="ClayNavierStokesRegularity",
            current_status="not_solved_not_promoted",
            status_kind="promotion_gate",
            sprint134_dependency="all_current_surfaces",
            upstream_supported_if_present=True,
            proof_surface=(
                "No universal regularity proof, non-circular energy-to-Serrin "
                "estimate, or explicit smooth finite-energy BKM blowup datum "
                "has been produced."
            ),
            programme_consequence=(
                "The programme must keep full Clay flags false and avoid "
                "route-enumeration promotion."
            ),
            live_ns_boundary=LIVE_BOUNDARY,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]], observations: dict[str, Any]) -> dict[str, Any]:
    retracted_claims = [
        row["claim_or_result"] for row in rows if row["status_kind"] == "retracted_claim"
    ]
    false_lemmas = [row["claim_or_result"] for row in rows if row["status_kind"] == "false_lemma"]
    upstream_present = {
        name: observation["present"] for name, observation in observations.items()
    }
    unsupported_if_present = [
        row["row_id"]
        for row in rows
        if row["sprint134_dependency"].startswith("ns_sprint134")
        and observations.get(row["sprint134_dependency"].removeprefix("ns_sprint134_"), {}).get(
            "present", False
        )
        and not row["upstream_supported_if_present"]
    ]

    summary = {
        "contract": CONTRACT,
        "row_count": len(rows),
        "live_ns_boundary": LIVE_BOUNDARY,
        "wbf_exact_intact": True,
        "wbf_exact_results": ["WBF-L", "WBF-S", "WBF-MP", "WBF-R"],
        "pure_u1_diffusion_retracted": True,
        "gamma_circulation_maximum_principle_replacement": True,
        "no_log_axisymmetric_biot_savart_uniform": False,
        "axs_viscous_dominance_obstruction_retracted": True,
        "hou_luo_axisymmetric_with_swirl_open_candidate": True,
        "hou_luo_axisymmetric_ns_route_status": "open_live_candidate",
        "retracted_claims": retracted_claims,
        "false_lemmas": false_lemmas,
        "upstream_sprint134_summaries_present": upstream_present,
        "upstream_observation_count": len(observations),
        "unsupported_rows_when_upstream_present": unsupported_if_present,
        "deterministic_if_upstream_absent": True,
        "full_clay_ns_solved": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "clayNavierStokesPromoted": False,
        "complete": True,
        "exit_code": 0,
        "next_action": (
            "model corrected Hou-Luo source-vs-viscosity dynamics with the "
            "restored logarithmic Biot-Savart loss"
        ),
        "control_card": {
            "O": (
                "Worker 3 owns scripts/ns_sprint135_corrected_status_assembly.py "
                "and outputs/ns_sprint135_corrected_status_assembly only."
            ),
            "R": (
                "Assemble the corrected current NS programme status after the "
                "Sprint 134 equation correction, no-log falsification, and "
                "Hou-Luo obstruction retraction."
            ),
            "C": "deterministic status rows, optional Sprint 134 summary reads, JSON/CSV/Markdown outputs",
            "S": (
                "WBF exact rows intact; pure-u1 diffusion and AXS viscous "
                "dominance are retracted; uniform no-log is false; Hou-Luo "
                "with swirl is open/live."
            ),
            "L": "Sprint 134 corrections -> Sprint 135 canonical status assembly -> promotion hold",
            "P": (
                "Use the corrected assembly as the current NS programme boundary "
                "and route the next work toward Hou-Luo as a live candidate."
            ),
            "G": "full_clay_ns_solved=false; clay_navier_stokes_promoted=false",
            "F": "No full Clay proof; analytic gap is source-vs-viscosity under log-loss dynamics.",
        },
    }
    return summary


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    if not rows:
        raise AssertionError("status rows must be non-empty")
    required_retractions = {PURE_U1_RETRACTION, AXS_OBSTRUCTION_RETRACTION}
    if not required_retractions.issubset(set(summary["retracted_claims"])):
        raise AssertionError("required retracted claims missing")
    if FALSE_NO_LOG not in summary["false_lemmas"]:
        raise AssertionError("NoLogAxisymmetricBiotSavartUniform must be marked false")
    if summary["live_ns_boundary"] != LIVE_BOUNDARY:
        raise AssertionError("incorrect live NS boundary")
    if summary["wbf_exact_intact"] is not True:
        raise AssertionError("WBF exact tower must remain intact")
    if summary["full_clay_ns_solved"] is not False:
        raise AssertionError("full Clay NS must remain unsolved")
    if summary["clay_navier_stokes_promoted"] is not False:
        raise AssertionError("Clay NS promotion must remain false")
    if summary["complete"] is not True or summary["exit_code"] != 0:
        raise AssertionError("assembly must complete with exit_code 0")
    if summary["unsupported_rows_when_upstream_present"]:
        raise AssertionError(
            "upstream summaries present but did not support rows: "
            + ",".join(summary["unsupported_rows_when_upstream_present"])
        )


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "mechanism_class",
        "claim_or_result",
        "current_status",
        "status_kind",
        "sprint134_dependency",
        "upstream_supported_if_present",
        "proof_surface",
        "programme_consequence",
        "live_ns_boundary",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    )
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def markdown_table(rows: list[dict[str, Any]]) -> str:
    columns = (
        "row_id",
        "mechanism_class",
        "claim_or_result",
        "current_status",
        "status_kind",
    )
    lines = [
        "| " + " | ".join(columns) + " |",
        "| " + " | ".join("---" for _ in columns) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(str(row[column]) for column in columns) + " |")
    return "\n".join(lines)


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    report = f"""# Sprint 135 Corrected NS Status Assembly

Contract: `{summary["contract"]}`

Live NS boundary: `{summary["live_ns_boundary"]}`

## Current State

- WBF exact tower intact: `{str(summary["wbf_exact_intact"]).lower()}`
- Pure-u1 diffusion retracted: `{str(summary["pure_u1_diffusion_retracted"]).lower()}`
- Uniform no-log Biot-Savart lemma: `{str(summary["no_log_axisymmetric_biot_savart_uniform"]).lower()}`
- AXS viscous dominance obstruction retracted: `{str(summary["axs_viscous_dominance_obstruction_retracted"]).lower()}`
- Hou-Luo axisymmetric with swirl open candidate: `{str(summary["hou_luo_axisymmetric_with_swirl_open_candidate"]).lower()}`

## Retracted And False

- Retracted claims: `{", ".join(summary["retracted_claims"])}`
- False lemmas: `{", ".join(summary["false_lemmas"])}`

## Rows

{markdown_table(rows)}

## Upstream Sprint 134 Summaries

`{json.dumps(summary["upstream_sprint134_summaries_present"], sort_keys=True)}`

## Promotion

- `full_clay_ns_solved`: `{str(summary["full_clay_ns_solved"]).lower()}`
- `clay_navier_stokes_promoted`: `{str(summary["clay_navier_stokes_promoted"]).lower()}`
- `complete`: `{str(summary["complete"]).lower()}`
"""
    path.write_text(report, encoding="utf-8")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    observations = upstream_observations(repo_root)
    rows = build_rows(observations)
    summary = build_summary(rows, observations)
    validate(rows, summary)

    write_json(out_dir / UPSTREAM_JSON_NAME, observations)
    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_report(out_dir / REPORT_NAME, summary, rows)

    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "row_count": len(rows),
                "live_ns_boundary": LIVE_BOUNDARY,
                "retracted_claims": summary["retracted_claims"],
                "false_lemmas": summary["false_lemmas"],
                "full_clay_ns_solved": False,
                "clay_navier_stokes_promoted": False,
                "complete": True,
                "exit_code": 0,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
