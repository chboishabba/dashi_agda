#!/usr/bin/env python3
"""Sprint 134 corrected axisymmetric Hou-Luo equation emitter.

This deterministic artifact retracts the Sprint 130/131 assertion that
``u1 = u^theta / r`` is a pure diffusion quantity.  In the standard Hou-Luo
axisymmetric variables, ``u1`` has a stretching source.  The maximum-principle
quantity is instead the swirl circulation ``Gamma = r u^theta = r^2 u1``.

The output is intentionally narrow: it records the corrected PDE surface and
the boundary-annulus conversion needed by later Hou-Luo analyses.  It does not
promote full Clay Navier-Stokes regularity.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint134_axisymmetric_equation_correction"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint134_axisymmetric_equation_correction")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_NAME = CONTRACT + "_rows.json"
CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

VARIABLE_DEFINITIONS = {
    "u1": "u^theta / r",
    "omega1": "omega^theta / r",
    "psi1": "psi^theta / r",
    "Gamma": "r * u^theta = r^2 * u1",
    "Ltilde": "partial_r^2 + (3/r) partial_r + partial_z^2",
    "Dt": "partial_t + u^r partial_r + u^z partial_z",
}

CORRECTED_U1_EQUATION = "D_t u1 = 2 u1 partial_z psi1 + nu Ltilde u1"
CORRECTED_OMEGA1_EQUATION = "D_t omega1 = partial_z(u1^2) + nu Ltilde omega1"
GAMMA_EQUATION = (
    "(partial_t + u^r partial_r + u^z partial_z) Gamma = "
    "nu (Delta - 2/r partial_r) Gamma"
)
BOUNDARY_ANNULUS_BOUND = "r in [r0, 1], r0 > 0, ||Gamma(t)||_inf <= M0 => ||u1(t)||_inf <= M0 / r0^2"


@dataclass(frozen=True)
class CorrectionRow:
    row_id: str
    lemma: str
    status: str
    assertion_type: str
    corrected_statement: str
    supersedes_or_supports: tuple[str, ...]
    variables_used: tuple[str, ...]
    proof_role: str
    clay_relevance: str
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["supersedes_or_supports"] = list(row["supersedes_or_supports"])
        row["variables_used"] = list(row["variables_used"])
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        CorrectionRow(
            row_id="axisymmetric_variable_definitions",
            lemma="StandardAxisymmetricSwirlVariables",
            status="corrected",
            assertion_type="definitions",
            corrected_statement=(
                "Use u1 = u^theta/r, omega1 = omega^theta/r, psi1 = "
                "psi^theta/r, Gamma = r u^theta = r^2 u1, and "
                "Ltilde = partial_r^2 + (3/r)partial_r + partial_z^2."
            ),
            supersedes_or_supports=(
                "Sprint130:PureDiffusionU1MaximumPrinciple",
                "Sprint131:HouLuoObstructionAssembly",
            ),
            variables_used=("u1", "omega1", "psi1", "Gamma", "Ltilde"),
            proof_role=(
                "Pins the exact variables before any maximum-principle or "
                "source-gradient estimate is invoked."
            ),
            clay_relevance="Local equation correction only; no full 3D regularity claim.",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        CorrectionRow(
            row_id="u1_equation_has_stretching_source",
            lemma="AxisymmetricSwirlEquationCorrection.U1EquationHasStretchingSource",
            status="corrected",
            assertion_type="pde_identity",
            corrected_statement=CORRECTED_U1_EQUATION,
            supersedes_or_supports=(
                "retracts:PureDiffusionU1MaximumPrinciple",
                "supports:AxisymmetricHouLuoNSCorrectedObstruction",
            ),
            variables_used=("u1", "psi1", "Ltilde", "nu"),
            proof_role=(
                "Records that u1 is not a pure diffusion variable; it contains "
                "the stretching source 2 u1 partial_z psi1."
            ),
            clay_relevance=(
                "Prevents downstream proofs from using a false u1 maximum principle."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        CorrectionRow(
            row_id="omega1_equation_has_quadratic_source",
            lemma="AxisymmetricSwirlEquationCorrection.Omega1EquationHasQuadraticSource",
            status="intact_corrected_surface",
            assertion_type="pde_identity",
            corrected_statement=CORRECTED_OMEGA1_EQUATION,
            supersedes_or_supports=(
                "supports:QuadraticSourceGradientUpperBound",
                "supports:CorrectedViscousDominanceNearBlowup",
            ),
            variables_used=("omega1", "u1", "Ltilde", "nu"),
            proof_role=(
                "Keeps the exact Hou-Luo amplification source as "
                "partial_z(u1^2)=2 u1 partial_z u1."
            ),
            clay_relevance="Axisymmetric mechanism surface only.",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        CorrectionRow(
            row_id="old_u1_pure_diffusion_retraction",
            lemma="PureDiffusionU1MaximumPrinciple",
            status="retracted_superseded",
            assertion_type="retraction",
            corrected_statement=(
                "The statement D_t u1 = nu Ltilde u1 is false in the standard "
                "Hou-Luo variables; u1 has the source 2 u1 partial_z psi1."
            ),
            supersedes_or_supports=(
                "superseded_by:AxisymmetricSwirlEquationCorrection",
                "superseded_by:SwirlCirculationMaximumPrinciple",
            ),
            variables_used=("u1", "psi1", "Ltilde", "nu"),
            proof_role=(
                "Explicitly blocks promotion of any proof depending on a pure "
                "diffusion maximum principle for u1."
            ),
            clay_relevance="Retraction narrows the proven axisymmetric support.",
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        CorrectionRow(
            row_id="gamma_maximum_principle",
            lemma="SwirlCirculationMaximumPrinciple",
            status="replacement_gate",
            assertion_type="maximum_principle",
            corrected_statement=GAMMA_EQUATION + "; hence ||Gamma(t)||_inf <= ||Gamma(0)||_inf.",
            supersedes_or_supports=(
                "replaces:PureDiffusionU1MaximumPrinciple",
                "supports:BoundaryAnnulusU1Bound",
            ),
            variables_used=("Gamma", "u^r", "u^z", "nu"),
            proof_role=(
                "Identifies the true maximum-principle quantity: swirl "
                "circulation Gamma, not u1."
            ),
            clay_relevance=(
                "Useful only after localization away from r=0; not a global "
                "3D regularity theorem."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        CorrectionRow(
            row_id="boundary_annulus_u1_bound",
            lemma="BoundaryAnnulusU1Bound",
            status="replacement_gate",
            assertion_type="annulus_conversion",
            corrected_statement=BOUNDARY_ANNULUS_BOUND,
            supersedes_or_supports=(
                "supports:QuadraticSourceGradientUpperBound",
                "supports:AxisymmetricHouLuoNSCorrectedObstruction",
            ),
            variables_used=("Gamma", "u1", "r0", "M0"),
            proof_role=(
                "Converts the Gamma maximum principle into a bounded u1 "
                "amplitude only on a boundary annulus r >= r0 > 0."
            ),
            clay_relevance="Hou-Luo boundary-annulus support only.",
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
        "lemma",
        "status",
        "assertion_type",
        "corrected_statement",
        "supersedes_or_supports",
        "variables_used",
        "proof_role",
        "clay_relevance",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = dict(row)
            serializable["supersedes_or_supports"] = "; ".join(serializable["supersedes_or_supports"])
            serializable["variables_used"] = "; ".join(serializable["variables_used"])
            writer.writerow(serializable)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_by_id = {row["row_id"]: row for row in rows}
    corrected_lemmas = [row["lemma"] for row in rows if row["status"] in {"corrected", "intact_corrected_surface"}]
    replacement_gates = [row["lemma"] for row in rows if row["status"] == "replacement_gate"]
    retracted = [row["lemma"] for row in rows if row["status"] == "retracted_superseded"]
    required_rows = {
        "u1_equation_has_stretching_source",
        "omega1_equation_has_quadratic_source",
        "old_u1_pure_diffusion_retraction",
        "gamma_maximum_principle",
        "boundary_annulus_u1_bound",
    }
    missing_required = sorted(required_rows.difference(row_by_id))
    invariant_failures = []
    if missing_required:
        invariant_failures.append("missing_required_rows:" + ",".join(missing_required))
    if "2 u1 partial_z psi1" not in row_by_id["u1_equation_has_stretching_source"]["corrected_statement"]:
        invariant_failures.append("u1_source_not_encoded")
    if "partial_z(u1^2)" not in row_by_id["omega1_equation_has_quadratic_source"]["corrected_statement"]:
        invariant_failures.append("omega1_source_not_encoded")
    if "r^2" not in VARIABLE_DEFINITIONS["Gamma"] or "u1" not in VARIABLE_DEFINITIONS["Gamma"]:
        invariant_failures.append("gamma_definition_not_encoded")
    if "M0 / r0^2" not in row_by_id["boundary_annulus_u1_bound"]["corrected_statement"]:
        invariant_failures.append("annulus_bound_not_encoded")

    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "variables": VARIABLE_DEFINITIONS,
        "corrected_u1_equation": CORRECTED_U1_EQUATION,
        "corrected_omega1_equation": CORRECTED_OMEGA1_EQUATION,
        "gamma_equation": GAMMA_EQUATION,
        "boundary_annulus_conversion": BOUNDARY_ANNULUS_BOUND,
        "axisymmetric_swirl_equation_corrected": True,
        "u1_equation_has_stretching_source": True,
        "omega1_equation_has_quadratic_source": True,
        "old_u1_pure_diffusion_retracted": True,
        "pure_diffusion_u1_maximum_principle_superseded": True,
        "gamma_maximum_principle_replacement": True,
        "boundary_annulus_u1_bound": True,
        "corrected_lemmas": corrected_lemmas,
        "replacement_gates": replacement_gates,
        "retracted_or_superseded": retracted,
        "downstream_required_updates": [
            "replace all u1 pure-diffusion references with Gamma maximum principle",
            "localize u1 amplitude bounds to annuli r >= r0 > 0",
            "rerun Hou-Luo source estimates using partial_z(u1^2)=2 u1 partial_z u1",
        ],
        "invariant_failures": invariant_failures,
        "invariants_passed": not invariant_failures,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "complete": not invariant_failures,
        "exit_code": 0 if not invariant_failures else 1,
    }


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 134 Axisymmetric Equation Correction",
        "",
        f"Contract: `{CONTRACT}`",
        "",
        "This artifact retracts the old pure-diffusion assertion for `u1` and "
        "records the corrected Hou-Luo axisymmetric PDE surface.",
        "",
        "## Corrected Equations",
        "",
        f"- `{CORRECTED_U1_EQUATION}`",
        f"- `{CORRECTED_OMEGA1_EQUATION}`",
        f"- `{GAMMA_EQUATION}`",
        f"- `{BOUNDARY_ANNULUS_BOUND}`",
        "",
        "## Rows",
        "",
        "| Row | Status | Lemma | Corrected statement |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        statement = row["corrected_statement"].replace("|", "\\|")
        lines.append(f"| `{row['row_id']}` | `{row['status']}` | `{row['lemma']}` | {statement} |")
    lines.extend(
        [
            "",
            f"`axisymmetric_swirl_equation_corrected={str(summary['axisymmetric_swirl_equation_corrected']).lower()}`",
            f"`old_u1_pure_diffusion_retracted={str(summary['old_u1_pure_diffusion_retracted']).lower()}`",
            f"`full_clay_ns_solved={str(summary['full_clay_ns_solved']).lower()}`",
            f"`clay_navier_stokes_promoted={str(summary['clay_navier_stokes_promoted']).lower()}`",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    out_dir = args.repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)

    write_json(out_dir / ROWS_NAME, rows)
    write_csv(out_dir / CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")

    print(json.dumps(summary, indent=2, sort_keys=True))
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
