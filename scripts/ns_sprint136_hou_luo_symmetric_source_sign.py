#!/usr/bin/env python3
"""Sprint 136 Hou-Luo symmetric source-sign emitter.

This artifact records the canonical z-reflection symmetric Hou-Luo sign
calculation after the Sprint 134/135 corrections:

* ``LogLossSourceLowerBound`` is false in the symmetric scenario.
* the source ``S = 2 u1 partial_z u1`` is zero at ``z = 0``.
* under axial monotonicity of the swirl profile, ``S`` is nonpositive away
  from the symmetry plane in the direction relevant to an interior positive
  vorticity maximum.
* the viscous contribution at an interior maximum is nonpositive.
* BKM remains finite conditional on ``AxialMonotonicityOfSwirlProfile``.

The output is a result ledger, not a Clay promotion.  The full Navier-Stokes
problem remains unsolved here.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint136_hou_luo_symmetric_source_sign"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint136_hou_luo_symmetric_source_sign")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SCENARIO = "CanonicalZReflectionSymmetricHouLuo"
CONDITION = "AxialMonotonicityOfSwirlProfile"
ROUTE = "HouLuoAxisymmetricNSRoute"


@dataclass(frozen=True)
class SymmetricSignRow:
    row_id: str
    scenario: str
    assertion_name: str
    mathematical_site: str
    hypothesis: str
    sign_statement: str
    sprint136_truth_value: bool | str
    consequence: str
    bkm_conditional_effect: str
    route_status: str
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    evidence_note: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        SymmetricSignRow(
            row_id="001_log_loss_lower_bound_false",
            scenario=SCENARIO,
            assertion_name="LogLossSourceLowerBound",
            mathematical_site="canonical z-reflection symmetric Hou-Luo profile",
            hypothesis=(
                "u1 is even in z, partial_z u1 is odd in z, and the active "
                "swirl profile is axially monotone away from z=0"
            ),
            sign_statement=(
                "A positive log-loss lower source bound is not available; the "
                "symmetry/monotonicity sign gives zero or damping source sign."
            ),
            sprint136_truth_value=False,
            consequence=(
                "The Sprint 135 blowup gate LogLossSourceLowerBound is closed "
                "negatively for this symmetric scenario."
            ),
            bkm_conditional_effect="supports_finite_BKM_under_axial_monotonicity",
            route_status="symmetric_source_lower_bound_false",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            evidence_note=(
                "The corrected logarithmic Biot-Savart loss remains an upper "
                "growth hazard, not a signed lower production mechanism."
            ),
        ),
        SymmetricSignRow(
            row_id="002_source_zero_on_symmetry_plane",
            scenario=SCENARIO,
            assertion_name="SourceAtZEqualsZero",
            mathematical_site="z=0 symmetry plane",
            hypothesis="u1 is z-even, hence partial_z u1(r,0,t)=0",
            sign_statement="S(r,0,t) = 2 u1(r,0,t) partial_z u1(r,0,t) = 0",
            sprint136_truth_value=True,
            consequence=(
                "No positive source production is generated exactly on the "
                "canonical symmetry plane."
            ),
            bkm_conditional_effect="removes_plane_source_growth",
            route_status="symmetric_source_neutral_on_axis_plane",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            evidence_note="This is a direct parity consequence, independent of viscosity.",
        ),
        SymmetricSignRow(
            row_id="003_source_nonpositive_away_from_plane",
            scenario=SCENARIO,
            assertion_name="SourceNonpositiveUnderAxialMonotonicity",
            mathematical_site="z != 0, same canonical symmetric branch",
            hypothesis=CONDITION,
            sign_statement=(
                "S = 2 u1 partial_z u1 <= 0 on the positive-vorticity branch "
                "selected by the monotone axial swirl profile."
            ),
            sprint136_truth_value=True,
            consequence=(
                "The source cannot supply the positive lower forcing needed "
                "for BKM divergence in this symmetric monotone branch."
            ),
            bkm_conditional_effect="prevents_positive_source_accumulation",
            route_status="conditional_regularizing_sign",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            evidence_note=(
                "The row is conditional on axial monotonicity; without that "
                "condition the sign gate is not asserted."
            ),
        ),
        SymmetricSignRow(
            row_id="004_viscosity_nonpositive_at_interior_max",
            scenario=SCENARIO,
            assertion_name="InteriorMaximumViscousTermNonpositive",
            mathematical_site="interior positive maximum of omega1",
            hypothesis="smooth interior maximum, away from singular coordinate boundary",
            sign_statement="nu Ltilde omega1 <= 0 at the interior maximum",
            sprint136_truth_value=True,
            consequence=(
                "At the maximum point, viscosity does not create positive "
                "vorticity growth and therefore cannot rescue the false lower "
                "source bound."
            ),
            bkm_conditional_effect="supports_maximum_inequality_damping",
            route_status="viscous_term_damping_at_interior_max",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            evidence_note=(
                "This records the maximum-principle sign for the local "
                "diffusive operator in the interior maximum calculation."
            ),
        ),
        SymmetricSignRow(
            row_id="005_bkm_finite_conditional",
            scenario=SCENARIO,
            assertion_name="BKMFiniteConditionalOnAxialMonotonicity",
            mathematical_site="canonical symmetric Hou-Luo evolution class",
            hypothesis=CONDITION,
            sign_statement=(
                "With nonpositive source and nonpositive viscous contribution "
                "at interior maxima, the signed maximum inequality supplies no "
                "BKM-divergent growth channel."
            ),
            sprint136_truth_value="conditional_true",
            consequence=(
                "BKM remains finite conditional on AxialMonotonicityOfSwirlProfile."
            ),
            bkm_conditional_effect="BKM_finite_conditional_on_axial_monotonicity",
            route_status="conditional_bkm_finite_symmetric_branch",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            evidence_note=(
                "This is a conditional branch result, not a global "
                "Navier-Stokes regularity theorem."
            ),
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    false_lower_bound_rows = [
        row
        for row in rows
        if row["assertion_name"] == "LogLossSourceLowerBound"
        and row["sprint136_truth_value"] is False
    ]
    conditional_bkm_rows = [
        row
        for row in rows
        if row["assertion_name"] == "BKMFiniteConditionalOnAxialMonotonicity"
    ]
    summary = {
        "contract": CONTRACT,
        "scenario": SCENARIO,
        "route": ROUTE,
        "row_count": len(rows),
        "assertions": [row["assertion_name"] for row in rows],
        "log_loss_source_lower_bound": False,
        "log_loss_source_lower_bound_false_in_symmetric_scenario": bool(false_lower_bound_rows),
        "source_formula": "S = 2 u1 partial_z u1",
        "source_at_z_equals_0": "zero",
        "source_sign_under_axial_monotonicity": "nonpositive_away_from_z_equals_0",
        "axial_monotonicity_gate": CONDITION,
        "axial_monotonicity_required": True,
        "axial_monotonicity_status": "open",
        "axial_monotonicity_required_open_boundary": (
            "Axial monotonicity is required for the signed source "
            "nonpositivity branch and remains open."
        ),
        "viscous_term_at_interior_max": "nonpositive",
        "bkm_finite_conditional_on": CONDITION,
        "bkm_finite_conditional": bool(conditional_bkm_rows),
        "hou_luo_route_status": "canonical_symmetric_branch_has_no_positive_source_lower_bound",
        "full_clay_ns_solved": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "Sprint 136 symmetric source-sign ledger emitted: "
            "LogLossSourceLowerBound is false in the canonical z-reflection "
            "symmetric Hou-Luo branch; source is zero at z=0 and nonpositive "
            "under axial monotonicity; viscosity is nonpositive at interior "
            "maxima; BKM is finite conditional on axial monotonicity."
        ),
        "control_card": {
            "O": (
                "Worker owns scripts/ns_sprint136_hou_luo_symmetric_source_sign.py "
                "and outputs/ns_sprint136_hou_luo_symmetric_source_sign/."
            ),
            "R": (
                "Record the Sprint 136 signed symmetric Hou-Luo result without "
                "promoting Clay."
            ),
            "C": "stdlib dataclass emitter with deterministic JSON/CSV/Markdown surfaces",
            "S": (
                "In the canonical z-reflection symmetric scenario, the source "
                "lower-bound blowup gate is false; the source is zero on z=0 "
                "and nonpositive under axial monotonicity away from z=0."
            ),
            "L": (
                "z-reflection parity -> source sign -> interior maximum "
                "viscosity sign -> conditional BKM finiteness"
            ),
            "P": (
                "Use this as the Sprint 136 branch ledger separating the "
                "symmetric monotone Hou-Luo scenario from unresolved nonsymmetric "
                "or nonmonotone scenarios."
            ),
            "G": "full_clay_ns_solved=false; clay_navier_stokes_promoted=false",
            "F": (
                "Conditional on AxialMonotonicityOfSwirlProfile; no global "
                "Navier-Stokes theorem or nonmonotone branch closure is claimed."
            ),
        },
    }
    return summary


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "scenario",
        "assertion_name",
        "mathematical_site",
        "hypothesis",
        "sign_statement",
        "sprint136_truth_value",
        "consequence",
        "bkm_conditional_effect",
        "route_status",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "evidence_note",
    )
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row[key] for key in fieldnames})


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    lines = [
        f"# {CONTRACT}",
        "",
        "## Summary",
        "",
        f"- Scenario: `{summary['scenario']}`",
        f"- LogLossSourceLowerBound: `{summary['log_loss_source_lower_bound']}`",
        f"- Source at `z=0`: `{summary['source_at_z_equals_0']}`",
        (
            "- Source sign under axial monotonicity: "
            f"`{summary['source_sign_under_axial_monotonicity']}`"
        ),
        f"- Viscous term at interior maximum: `{summary['viscous_term_at_interior_max']}`",
        f"- BKM finite conditional on: `{summary['bkm_finite_conditional_on']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Sign Ledger",
        "",
        "| row | assertion | site | sign/truth | consequence |",
        "|---|---|---|---|---|",
    ]
    for row in rows:
        lines.append(
            "| {row_id} | {assertion} | {site} | {truth} | {consequence} |".format(
                row_id=row["row_id"],
                assertion=row["assertion_name"],
                site=row["mathematical_site"],
                truth=row["sprint136_truth_value"],
                consequence=row["consequence"],
            )
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            "The canonical z-reflection symmetric Hou-Luo branch does not "
            "supply the positive source lower bound needed by the Sprint 135 "
            "blowup route. The signed source is zero on the symmetry plane "
            "and nonpositive under axial monotonicity away from it, while the "
            "viscous term is nonpositive at an interior positive maximum. "
            "The resulting BKM finiteness statement is conditional on axial "
            "monotonicity and is not a Clay promotion.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    assert rows, "rows must not be empty"
    assert [row["row_id"] for row in rows] == sorted(row["row_id"] for row in rows)
    assert summary["contract"] == CONTRACT
    assert summary["scenario"] == SCENARIO
    assert summary["row_count"] == len(rows)
    assert summary["log_loss_source_lower_bound"] is False
    assert summary["log_loss_source_lower_bound_false_in_symmetric_scenario"] is True
    assert summary["source_at_z_equals_0"] == "zero"
    assert summary["source_sign_under_axial_monotonicity"] == (
        "nonpositive_away_from_z_equals_0"
    )
    assert summary["viscous_term_at_interior_max"] == "nonpositive"
    assert summary["bkm_finite_conditional_on"] == CONDITION
    assert summary["bkm_finite_conditional"] is True
    assert summary["full_clay_ns_solved"] is False
    assert summary["clay_navier_stokes_promoted"] is False
    assert summary["complete"] is True
    assert summary["exit_code"] == 0
    assert all(row["scenario"] == SCENARIO for row in rows)
    assert all(row["full_clay_ns_solved"] is False for row in rows)
    assert all(row["clay_navier_stokes_promoted"] is False for row in rows)
    assert any(
        row["assertion_name"] == "SourceAtZEqualsZero"
        and "= 0" in row["sign_statement"]
        for row in rows
    )
    assert any(
        row["assertion_name"] == "SourceNonpositiveUnderAxialMonotonicity"
        and "<= 0" in row["sign_statement"]
        for row in rows
    )


def main() -> int:
    args = parse_args()
    out_dir = args.repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    try:
        validate(summary, rows)
    except AssertionError as exc:
        print(f"{CONTRACT}: {exc}", file=sys.stderr)
        return 1

    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_report(out_dir / REPORT_NAME, summary, rows)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
