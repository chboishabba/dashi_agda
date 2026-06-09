#!/usr/bin/env python3
"""Sprint 134 Hou-Luo retraction status emitter.

This script records the corrected downstream status after the axisymmetric
Hou-Luo Navier-Stokes obstruction audit found two load-bearing defects:

* the uniform no-log axisymmetric Biot-Savart estimate is false away from the
  axis, so the standard logarithmic kernel loss returns;
* the previous pure-diffusion/max-principle treatment of u1 was the wrong
  variable-level statement.  The robust maximum principle is for the swirl
  circulation Gamma = r u^theta, with boundary-annulus conversion to u1.

The result is a retraction artifact, not a regularity theorem.  It preserves
the exact WBF obstruction rows and the swirl-circulation maximum principle,
but marks AxisymmetricHouLuoNSViscousDominanceObstruction as retracted and
keeps the Hou-Luo axisymmetric NS route open/live.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint134_hou_luo_retraction_status"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint134_hou_luo_retraction_status")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

RETRACTED_THEOREM = "AxisymmetricHouLuoNSViscousDominanceObstruction"
ROUTE_STATUS = "open_live_candidate"


@dataclass(frozen=True)
class RetractionStatusRow:
    row_id: str
    result_or_claim: str
    mechanism_class: str
    previous_status: str
    corrected_status: str
    action: str
    depends_on_false_no_log: bool
    depends_on_pure_u1_diffusion_or_source_bound: bool
    corrected_equation_or_bound: str
    downstream_consequence: str
    hou_luo_axisymmetric_ns_route_status: str
    wbf_exact_results_intact: bool
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    rationale: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        RetractionStatusRow(
            row_id="axs_hou_luo_viscous_dominance_retracted",
            result_or_claim=RETRACTED_THEOREM,
            mechanism_class="CLASS_AXS",
            previous_status="claimed_conditional_obstruction",
            corrected_status="retracted",
            action="retract_theorem_not_promote",
            depends_on_false_no_log=True,
            depends_on_pure_u1_diffusion_or_source_bound=True,
            corrected_equation_or_bound=(
                "D_t u1 = 2 u1 partial_z psi1 + nu L_tilde u1; "
                "the maximum-principle quantity is Gamma = r u_theta = r^2 u1"
            ),
            downstream_consequence=(
                "The prior viscous-dominance proof used a no-log strain "
                "Gronwall and an over-strong source bound; both are invalid "
                "as stated."
            ),
            hou_luo_axisymmetric_ns_route_status=ROUTE_STATUS,
            wbf_exact_results_intact=False,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "The axisymmetric velocity-gradient kernel has the standard "
                "local logarithmic singularity away from r=0, and u1 itself "
                "is not a pure diffusion variable."
            ),
        ),
        RetractionStatusRow(
            row_id="no_log_axisymmetric_biot_savart_uniform_false",
            result_or_claim="NoLogAxisymmetricBiotSavartUniform",
            mechanism_class="CLASS_AXS",
            previous_status="load_bearing_open_lemma",
            corrected_status="false_uniformly_in_cylinder",
            action="mark_false_as_uniform_statement",
            depends_on_false_no_log=False,
            depends_on_pure_u1_diffusion_or_source_bound=False,
            corrected_equation_or_bound=(
                "elliptic-integral kernel retains K(k) ~ log(4/sqrt(1-k^2)) "
                "as k -> 1; near-axis cancellation is not uniform"
            ),
            downstream_consequence=(
                "Biot-Savart strain control reverts to a logarithmic loss, "
                "so Gronwall factors may grow faster than every power of "
                "1/tau."
            ),
            hou_luo_axisymmetric_ns_route_status=ROUTE_STATUS,
            wbf_exact_results_intact=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "The Sprint 128 near-axis r-factor observation does not remove "
                "the coincident-ring singularity throughout the cylinder."
            ),
        ),
        RetractionStatusRow(
            row_id="corrected_swirl_variable_maximum_principle_intact",
            result_or_claim="SwirlCirculationMaximumPrinciple",
            mechanism_class="CLASS_AXS",
            previous_status="u1_maximum_principle_claimed",
            corrected_status="gamma_maximum_principle_intact",
            action="replace_u1_gate_with_gamma_gate",
            depends_on_false_no_log=False,
            depends_on_pure_u1_diffusion_or_source_bound=True,
            corrected_equation_or_bound=(
                "(partial_t + u_r partial_r + u_z partial_z) Gamma = "
                "nu (Delta - 2/r partial_r) Gamma; ||Gamma(t)||_inf <= "
                "||Gamma(0)||_inf"
            ),
            downstream_consequence=(
                "On a boundary annulus r in [r0,1], Gamma control gives "
                "||u1||_inf <= ||Gamma(0)||_inf / r0^2, but not a global "
                "pure-diffusion law for u1."
            ),
            hou_luo_axisymmetric_ns_route_status=ROUTE_STATUS,
            wbf_exact_results_intact=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "The correction preserves the physically relevant swirl "
                "maximum principle while removing the false autonomous u1 "
                "diffusion statement."
            ),
        ),
        RetractionStatusRow(
            row_id="corrected_source_gradient_log_gronwall",
            result_or_claim="CorrectedHouLuoSourceGradientAccounting",
            mechanism_class="CLASS_AXS",
            previous_status="source_bounded_by_polynomial_viscous_comparison",
            corrected_status="log_gronwall_can_overpower_polynomial_viscosity",
            action="invert_dominance_conclusion",
            depends_on_false_no_log=True,
            depends_on_pure_u1_diffusion_or_source_bound=True,
            corrected_equation_or_bound=(
                "partial_z(u1^2)=2 u1 partial_z u1; logarithmic strain "
                "control yields exp(C tau^-beta log(1/tau)) type upper-scale "
                "factors rather than a fixed M0^2/delta polynomial closure"
            ),
            downstream_consequence=(
                "The corrected source-gradient path can be super-polynomial, "
                "equivalently super-exponential in log(1/tau), so the source "
                "may beat the viscous tau-polynomial damping term."
            ),
            hou_luo_axisymmetric_ns_route_status=ROUTE_STATUS,
            wbf_exact_results_intact=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "With log-loss Gronwall, source amplification is no longer "
                "controlled by the polynomial comparison used in Sprint 130/131."
            ),
        ),
        RetractionStatusRow(
            row_id="wbf_exact_obstruction_tower_intact",
            result_or_claim="WBF-L/WBF-S/WBF-MP/WBF-R",
            mechanism_class="CLASS_WBF",
            previous_status="exact_unconditional",
            corrected_status="exact_unconditional_intact",
            action="preserve",
            depends_on_false_no_log=False,
            depends_on_pure_u1_diffusion_or_source_bound=False,
            corrected_equation_or_bound=(
                "algebraic WBF identities are independent of axisymmetric "
                "Biot-Savart no-log and u1/Gamma variable corrections"
            ),
            downstream_consequence=(
                "The four exact WBF obstruction results remain publishable "
                "route-specific no-go statements."
            ),
            hou_luo_axisymmetric_ns_route_status=ROUTE_STATUS,
            wbf_exact_results_intact=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "Their proofs are algebraic or symmetry identities, not "
                "axisymmetric strain estimates."
            ),
        ),
        RetractionStatusRow(
            row_id="hou_luo_axisymmetric_ns_route_open_live",
            result_or_claim="HouLuoAxisymmetricNSRoute",
            mechanism_class="CLASS_AXS",
            previous_status="claimed_obstructed_in_beta_gt_0_window",
            corrected_status=ROUTE_STATUS,
            action="mark_open_neither_obstructed_nor_confirmed",
            depends_on_false_no_log=True,
            depends_on_pure_u1_diffusion_or_source_bound=True,
            corrected_equation_or_bound=(
                "available corrections establish neither global regularity nor "
                "finite-time BKM blowup for axisymmetric NS with swirl"
            ),
            downstream_consequence=(
                "The route should now be studied as a live candidate: either "
                "find a positive blowup construction or a new non-circular "
                "regularity estimate."
            ),
            hou_luo_axisymmetric_ns_route_status=ROUTE_STATUS,
            wbf_exact_results_intact=True,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "The retraction removes the claimed NS-specific obstruction "
                "without replacing it by a proof of blowup."
            ),
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    retracted = [row for row in rows if row["corrected_status"] == "retracted"]
    false_no_log = [
        row for row in rows if row["result_or_claim"] == "NoLogAxisymmetricBiotSavartUniform"
    ]
    source_rows = [
        row for row in rows if row["row_id"] == "corrected_source_gradient_log_gronwall"
    ]
    wbf_rows = [row for row in rows if row["mechanism_class"] == "CLASS_WBF"]
    open_live_rows = [
        row
        for row in rows
        if row["hou_luo_axisymmetric_ns_route_status"] == ROUTE_STATUS
    ]
    return {
        "contract": CONTRACT,
        "theorem_retracted": RETRACTED_THEOREM,
        "axs_viscous_dominance_obstruction_retracted": True,
        "retraction_reason_dependencies": [
            "NoLogAxisymmetricBiotSavartUniform is false as a uniform cylinder estimate",
            "u1 is not a pure-diffusion maximum-principle variable",
            "the source requires gradient accounting: partial_z(u1^2)=2u1 partial_z u1",
        ],
        "corrected_maximum_principle_quantity": "Gamma = r u_theta = r^2 u1",
        "corrected_u1_equation_has_stretching_source": True,
        "corrected_source_gradient_with_log_gronwall": True,
        "source_can_be_super_polynomial_in_tau_inverse": True,
        "source_can_be_super_exponential_in_log_tau_inverse": True,
        "source_may_beat_viscosity": True,
        "hou_luo_axisymmetric_ns_route_status": ROUTE_STATUS,
        "hou_luo_axisymmetric_ns_obstructed": False,
        "hou_luo_axisymmetric_ns_confirmed_blowup": False,
        "wbf_exact_results_intact": all(row["wbf_exact_results_intact"] for row in wbf_rows),
        "wbf_intact_results": [row["result_or_claim"] for row in wbf_rows],
        "false_uniform_lemmas": [row["result_or_claim"] for row in false_no_log],
        "retracted_results": [row["result_or_claim"] for row in retracted],
        "row_count": len(rows),
        "open_live_row_count": len(open_live_rows),
        "source_gradient_rows": [row["result_or_claim"] for row in source_rows],
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "clayNavierStokesPromoted": False,
        "complete": True,
        "exit_code": 0,
    }


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_rows_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty retraction status table")
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def markdown_table(rows: list[dict[str, Any]]) -> str:
    columns = [
        "row_id",
        "result_or_claim",
        "previous_status",
        "corrected_status",
        "action",
    ]
    lines = [
        "| " + " | ".join(columns) + " |",
        "| " + " | ".join("---" for _ in columns) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(str(row[column]) for column in columns) + " |")
    return "\n".join(lines)


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    report = f"""# Sprint 134 Hou-Luo Retraction Status

Contract: `{summary["contract"]}`

Retracted theorem: `{summary["theorem_retracted"]}`

Axisymmetric viscous dominance obstruction retracted:
`{summary["axs_viscous_dominance_obstruction_retracted"]}`

Hou-Luo axisymmetric NS route status:
`{summary["hou_luo_axisymmetric_ns_route_status"]}`

## Corrected Consequence

The previous obstruction relied on a uniform no-log axisymmetric Biot-Savart
bound and a pure-diffusion/source-bound treatment of `u1`.  The corrected
accounting uses the circulation maximum principle for
`Gamma = r u_theta = r^2 u1`, while the source remains
`partial_z(u1^2)=2 u1 partial_z u1`.  With the logarithmic strain loss restored,
the Gronwall factor can be super-polynomial in `1/tau`, equivalently
super-exponential in `log(1/tau)`, so the source may beat polynomial viscous
damping.

## Status Table

{markdown_table(rows)}

## Promotion

- `full_clay_ns_solved`: `{summary["full_clay_ns_solved"]}`
- `clay_navier_stokes_promoted`: `{summary["clay_navier_stokes_promoted"]}`
- `complete`: `{summary["complete"]}`
"""
    path.write_text(report, encoding="utf-8")


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    if not rows:
        raise AssertionError("expected non-empty status table")
    if summary["axs_viscous_dominance_obstruction_retracted"] is not True:
        raise AssertionError("AXS viscous dominance obstruction must be retracted")
    if summary["hou_luo_axisymmetric_ns_route_status"] != ROUTE_STATUS:
        raise AssertionError("Hou-Luo route must be marked open/live")
    if summary["full_clay_ns_solved"] is not False:
        raise AssertionError("full Clay NS must remain unsolved")
    if summary["clay_navier_stokes_promoted"] is not False:
        raise AssertionError("Clay promotion must remain false")
    if summary["complete"] is not True or summary["exit_code"] != 0:
        raise AssertionError("emitter must report complete exit-zero status")
    if RETRACTED_THEOREM not in summary["retracted_results"]:
        raise AssertionError("retracted theorem missing from summary")
    if summary["wbf_exact_results_intact"] is not True:
        raise AssertionError("WBF exact results should remain intact")
    if not summary["source_can_be_super_exponential_in_log_tau_inverse"]:
        raise AssertionError("corrected source-gradient consequence missing")


def main() -> int:
    args = parse_args()
    out_dir = args.repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate(rows, summary)

    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_rows_csv(out_dir / ROWS_CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_report(out_dir / REPORT_NAME, summary, rows)

    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "row_count": len(rows),
                "axs_viscous_dominance_obstruction_retracted": True,
                "hou_luo_axisymmetric_ns_route_status": ROUTE_STATUS,
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
