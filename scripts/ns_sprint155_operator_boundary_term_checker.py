#!/usr/bin/env python3
"""Sprint 155 weighted operator boundary-term checker/emitter.

This deterministic stdlib emitter records the integration-by-parts accounting
for the axisymmetric weighted operator Ltilde in divergence form with measure
r dr dz.  It is a checker/ledger, not a proof: it verifies the numeric sample
budgets encoded below, writes JSON/CSV/Markdown artifacts, and keeps all BKM
and Clay promotion flags false.
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
from fractions import Fraction
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint155_operator_boundary_term_checker"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint155_operator_boundary_term_checker")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 155
LANE = 3
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
LEDGER = "WeightedLtildeIbpOperatorBoundaryTermChecker"
OPERATOR = "Ltilde f = (1/r) partial_r(r partial_r f) + partial_z^2 f"
WEIGHTED_MEASURE = "r dr dz"
DECISION = "fail_closed_weighted_ltilde_ibp_has_boundary_and_commutator_obligations"

NU = Fraction(1, 1)
INNER_RADIUS = Fraction(1, 64)
OUTER_RADIUS = Fraction(4, 1)
AXIAL_HALF_HEIGHT = Fraction(3, 1)
CUTOFF_THICKNESS = Fraction(1, 8)
C_GRAD_CUTOFF = Fraction(2, 1)
C_LAP_CUTOFF = Fraction(6, 1)
TRACE_CONSTANT_WALL = Fraction(9, 4)
POINCARE_CONSTANT_CORE = Fraction(16, 25)
YOUNG_EPSILON_GRADIENT = Fraction(1, 8)
DISSIPATION_RESERVE = Fraction(128, 1)
POINCARE_RESERVE = Fraction(40, 1)
WALL_TRACE_RESERVE = Fraction(36, 1)

REQUIRED_ROW_IDS = {
    "divergence_form_weighted_ltilde",
    "weighted_ibp_bulk_coercive_gradient",
    "axis_boundary_r_zero_regularity",
    "radial_wall_outward_normal_sign",
    "axial_wall_outward_normal_sign",
    "cutoff_gradient_commutator_young_split",
    "cutoff_laplacian_commutator_budget",
    "radial_weight_derivative_no_extra_bad_term",
    "poincare_core_absorption",
    "poincare_annular_absorption_gap",
    "simultaneous_operator_constants",
    "bkm_clay_guard",
}

FAIL_CLOSED_FLAGS = {
    "weighted_ltilde_ibp_proved": False,
    "operator_domain_closed": False,
    "boundary_sign_theorem_closed": False,
    "cutoff_commutator_closed": False,
    "poincare_absorption_closed": False,
    "simultaneous_constants_valid": False,
    "bkm_guard_closed": False,
    "bkm_finite": False,
    "clay_navier_stokes_promoted": False,
    "clay_solution": False,
    "clay": False,
    "bkm": False,
}

CONTROL_CARD = {
    "O": (
        "Worker 3 owns only scripts/ns_sprint155_operator_boundary_term_checker.py "
        "and outputs/ns_sprint155_operator_boundary_term_checker/."
    ),
    "R": (
        "Emit a checker for weighted Ltilde integration by parts in divergence "
        "form, radial measure r dr dz, boundary/wall signs, cutoff-gradient "
        "commutators, and Poincare absorption rows."
    ),
    "C": (
        "One stdlib Python emitter writes rows JSON, rows CSV, summary JSON, "
        "Markdown, and manifest through an atomic output-directory replacement."
    ),
    "S": (
        "The numeric sample has positive interior diffusion and several "
        "absorbed estimates, but wall sign certification, annular Poincare "
        "closure, and simultaneous theorem constants remain open."
    ),
    "L": (
        "Divergence form -> weighted IBP -> boundary signs -> cutoff "
        "commutators -> Poincare absorption -> simultaneous constants -> "
        "BKM/Clay guard."
    ),
    "P": (
        "Use this artifact as operator-boundary accounting only; do not cite it "
        "as analytic closure, finite BKM control, or a Clay Navier-Stokes proof."
    ),
    "G": (
        "Promotion is blocked unless all required rows are theorem-closed and "
        "all fail-closed flags flip through a separate proof artifact."
    ),
    "F": (
        "Missing: boundary-compatible sign theorem at walls, annular Poincare "
        "closure under the active cutoff family, simultaneous constants, and "
        "standard BKM/Clay translation."
    ),
}


@dataclass(frozen=True)
class OperatorRow:
    row_id: str
    category: str
    status: str
    expression: str
    sign_expectation: str
    bulk_gradient_credit: Fraction
    boundary_load: Fraction
    cutoff_commutator_load: Fraction
    poincare_load: Fraction
    absorption_reserve: Fraction
    theorem_required: str
    theorem_closed: bool
    notes: str

    def as_row(self) -> dict[str, Any]:
        total_load = self.boundary_load + self.cutoff_commutator_load + self.poincare_load
        net_margin = self.bulk_gradient_credit + self.absorption_reserve - total_load
        numerically_absorbed = net_margin >= 0 and self.status in {
            "identity_recorded",
            "coercive",
            "absorbed",
            "compatible",
        }
        closed = numerically_absorbed and self.theorem_closed

        row = asdict(self)
        row.update(
            {
                "sprint": SPRINT,
                "lane": LANE,
                "contract": CONTRACT,
                "program": PROGRAM,
                "ledger": LEDGER,
                "operator": OPERATOR,
                "weighted_measure": WEIGHTED_MEASURE,
                "decision": DECISION,
                "bulk_gradient_credit": fraction_to_str(self.bulk_gradient_credit),
                "boundary_load": fraction_to_str(self.boundary_load),
                "cutoff_commutator_load": fraction_to_str(self.cutoff_commutator_load),
                "poincare_load": fraction_to_str(self.poincare_load),
                "absorption_reserve": fraction_to_str(self.absorption_reserve),
                "total_load": fraction_to_str(total_load),
                "net_margin": fraction_to_str(net_margin),
                "net_margin_float": round(float(net_margin), 12),
                "numerically_absorbed": numerically_absorbed,
                "closed": closed,
                "claim_closed": False,
                "claim_proved": False,
                "claim_proven": False,
                "promotion_allowed": False,
                "fail_closed": True,
            }
        )
        row.update(FAIL_CLOSED_FLAGS)
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


def fraction_to_str(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def build_constant_budget() -> dict[str, Any]:
    cutoff_gradient_scale = C_GRAD_CUTOFF / CUTOFF_THICKNESS
    cutoff_laplacian_scale = C_LAP_CUTOFF / (CUTOFF_THICKNESS * CUTOFF_THICKNESS)
    young_dual_constant = Fraction(1, 4) / YOUNG_EPSILON_GRADIENT
    radial_log_span = OUTER_RADIUS / INNER_RADIUS
    return {
        "nu": fraction_to_str(NU),
        "inner_radius": fraction_to_str(INNER_RADIUS),
        "outer_radius": fraction_to_str(OUTER_RADIUS),
        "axial_half_height": fraction_to_str(AXIAL_HALF_HEIGHT),
        "cutoff_thickness": fraction_to_str(CUTOFF_THICKNESS),
        "cutoff_gradient_bound": fraction_to_str(C_GRAD_CUTOFF),
        "cutoff_laplacian_bound": fraction_to_str(C_LAP_CUTOFF),
        "cutoff_gradient_scale": fraction_to_str(cutoff_gradient_scale),
        "cutoff_gradient_scale_float": round(float(cutoff_gradient_scale), 12),
        "cutoff_laplacian_scale": fraction_to_str(cutoff_laplacian_scale),
        "cutoff_laplacian_scale_float": round(float(cutoff_laplacian_scale), 12),
        "trace_constant_wall": fraction_to_str(TRACE_CONSTANT_WALL),
        "poincare_constant_core": fraction_to_str(POINCARE_CONSTANT_CORE),
        "young_epsilon_gradient": fraction_to_str(YOUNG_EPSILON_GRADIENT),
        "young_dual_constant": fraction_to_str(young_dual_constant),
        "radial_log_span_outer_over_inner": fraction_to_str(radial_log_span),
        "dissipation_reserve": fraction_to_str(DISSIPATION_RESERVE),
        "poincare_reserve": fraction_to_str(POINCARE_RESERVE),
        "wall_trace_reserve": fraction_to_str(WALL_TRACE_RESERVE),
    }


def build_rows() -> list[dict[str, Any]]:
    raw_rows = [
        OperatorRow(
            row_id="divergence_form_weighted_ltilde",
            category="operator_normal_form",
            status="identity_recorded",
            expression="int phi f Ltilde f r dr dz = int phi f div_rz(r grad f) dr dz",
            sign_expectation="neutral_identity_before_ibp",
            bulk_gradient_credit=Fraction(0, 1),
            boundary_load=Fraction(0, 1),
            cutoff_commutator_load=Fraction(0, 1),
            poincare_load=Fraction(0, 1),
            absorption_reserve=Fraction(0, 1),
            theorem_required="WeightedDivergenceFormForLtilde",
            theorem_closed=False,
            notes="Records the divergence-form normalization with the radial weight inside the divergence.",
        ),
        OperatorRow(
            row_id="weighted_ibp_bulk_coercive_gradient",
            category="ibp_bulk",
            status="coercive",
            expression="-nu int phi |grad f|^2 r dr dz",
            sign_expectation="favorable_negative_dissipation",
            bulk_gradient_credit=DISSIPATION_RESERVE,
            boundary_load=Fraction(0, 1),
            cutoff_commutator_load=Fraction(0, 1),
            poincare_load=Fraction(0, 1),
            absorption_reserve=Fraction(0, 1),
            theorem_required="WeightedLtildeIbpBulkCoercivity",
            theorem_closed=False,
            notes="The sample reserve is positive, but theorem-level domain and trace hypotheses are not closed here.",
        ),
        OperatorRow(
            row_id="axis_boundary_r_zero_regularity",
            category="axis_boundary",
            status="compatible",
            expression="lim_{r->0} r phi f partial_r f = 0",
            sign_expectation="zero_by_axis_weight_and_regularity",
            bulk_gradient_credit=Fraction(0, 1),
            boundary_load=Fraction(0, 1),
            cutoff_commutator_load=Fraction(0, 1),
            poincare_load=Fraction(0, 1),
            absorption_reserve=Fraction(4, 1),
            theorem_required="AxisRegularityWeightedBoundaryVanishes",
            theorem_closed=False,
            notes="The r factor gives the expected vanishing boundary contribution for regular axisymmetric data.",
        ),
        OperatorRow(
            row_id="radial_wall_outward_normal_sign",
            category="wall_boundary",
            status="open_sign",
            expression="nu int_{r=R} phi f partial_n f R dz",
            sign_expectation="requires_dirichlet_or_robin_dissipative_wall_sign",
            bulk_gradient_credit=Fraction(0, 1),
            boundary_load=Fraction(21, 1),
            cutoff_commutator_load=Fraction(0, 1),
            poincare_load=Fraction(0, 1),
            absorption_reserve=WALL_TRACE_RESERVE,
            theorem_required="RadialWallTraceSignOrAbsorption",
            theorem_closed=False,
            notes="Numerically below the wall trace reserve, but boundary condition sign is not certified.",
        ),
        OperatorRow(
            row_id="axial_wall_outward_normal_sign",
            category="wall_boundary",
            status="open_sign",
            expression="nu int_{z=+-H} phi f partial_n f r dr",
            sign_expectation="top_bottom_wall_flux_must_be_nonpositive_or_absorbed",
            bulk_gradient_credit=Fraction(0, 1),
            boundary_load=Fraction(17, 1),
            cutoff_commutator_load=Fraction(0, 1),
            poincare_load=Fraction(0, 1),
            absorption_reserve=WALL_TRACE_RESERVE,
            theorem_required="AxialWallTraceSignOrAbsorption",
            theorem_closed=False,
            notes="The sign depends on the wall model and cannot be promoted from a numeric trace budget alone.",
        ),
        OperatorRow(
            row_id="cutoff_gradient_commutator_young_split",
            category="cutoff_commutator",
            status="absorbed",
            expression="nu int f grad phi dot grad f r dr dz",
            sign_expectation="indefinite_absorbed_by_young_gradient_split",
            bulk_gradient_credit=Fraction(32, 1),
            boundary_load=Fraction(0, 1),
            cutoff_commutator_load=Fraction(19, 1),
            poincare_load=Fraction(0, 1),
            absorption_reserve=Fraction(0, 1),
            theorem_required="CutoffGradientCommutatorYoungAbsorption",
            theorem_closed=False,
            notes="Uses epsilon=1/8 with the encoded cutoff gradient scale; theorem closure remains separate.",
        ),
        OperatorRow(
            row_id="cutoff_laplacian_commutator_budget",
            category="cutoff_commutator",
            status="absorbed",
            expression="nu int |f|^2 |Ltilde phi| r dr dz",
            sign_expectation="adverse_zero_order_cutoff_leakage",
            bulk_gradient_credit=Fraction(0, 1),
            boundary_load=Fraction(0, 1),
            cutoff_commutator_load=Fraction(29, 1),
            poincare_load=Fraction(0, 1),
            absorption_reserve=Fraction(35, 1),
            theorem_required="CutoffLtildeCommutatorZeroOrderBudget",
            theorem_closed=False,
            notes="The sample zero-order cutoff load fits under reserve after localization constants are fixed.",
        ),
        OperatorRow(
            row_id="radial_weight_derivative_no_extra_bad_term",
            category="radial_weight",
            status="compatible",
            expression="partial_r(r partial_r f) paired against f with dr dz",
            sign_expectation="weight_derivative_is_inside_divergence",
            bulk_gradient_credit=Fraction(8, 1),
            boundary_load=Fraction(0, 1),
            cutoff_commutator_load=Fraction(0, 1),
            poincare_load=Fraction(0, 1),
            absorption_reserve=Fraction(0, 1),
            theorem_required="NoUnpairedRadialWeightDerivativeTerm",
            theorem_closed=False,
            notes="The checker explicitly forbids adding a standalone adverse (1/r) partial_r term after weighted IBP.",
        ),
        OperatorRow(
            row_id="poincare_core_absorption",
            category="poincare_absorption",
            status="absorbed",
            expression="int_core phi |f-f_core_mean|^2 r dr dz <= C_P int_core phi |grad f|^2 r dr dz",
            sign_expectation="zero_order_core_absorbed_by_gradient",
            bulk_gradient_credit=Fraction(30, 1),
            boundary_load=Fraction(0, 1),
            cutoff_commutator_load=Fraction(0, 1),
            poincare_load=Fraction(18, 1),
            absorption_reserve=POINCARE_RESERVE,
            theorem_required="WeightedCorePoincareAbsorption",
            theorem_closed=False,
            notes="The fixed C_P=16/25 sample leaves positive margin for the core zero-order term.",
        ),
        OperatorRow(
            row_id="poincare_annular_absorption_gap",
            category="poincare_absorption",
            status="open_gap",
            expression="int_annulus phi |f|^2 r dr dz <= C_ann int_annulus |grad f|^2 r dr dz",
            sign_expectation="requires_annular_mean_or_boundary_anchor",
            bulk_gradient_credit=Fraction(12, 1),
            boundary_load=Fraction(0, 1),
            cutoff_commutator_load=Fraction(0, 1),
            poincare_load=Fraction(57, 1),
            absorption_reserve=Fraction(20, 1),
            theorem_required="WeightedAnnularPoincareWithAnchor",
            theorem_closed=False,
            notes="This is the explicit failing numeric row: annular zero-order load exceeds the available reserve.",
        ),
        OperatorRow(
            row_id="simultaneous_operator_constants",
            category="constant_compatibility",
            status="open_constants",
            expression="C_trace, C_cutoff, C_P, epsilon, nu reserves must hold simultaneously",
            sign_expectation="requires_single_constant_pack",
            bulk_gradient_credit=Fraction(0, 1),
            boundary_load=Fraction(6, 1),
            cutoff_commutator_load=Fraction(7, 1),
            poincare_load=Fraction(5, 1),
            absorption_reserve=Fraction(10, 1),
            theorem_required="SimultaneousWeightedOperatorConstantPack",
            theorem_closed=False,
            notes="Even absorbed component rows do not imply a single compatible theorem-level constant pack.",
        ),
        OperatorRow(
            row_id="bkm_clay_guard",
            category="promotion_guard",
            status="guard_false",
            expression="operator-boundary ledger does not imply finite integral ||omega||_infty dt or Clay NS",
            sign_expectation="no_promotion",
            bulk_gradient_credit=Fraction(0, 1),
            boundary_load=Fraction(0, 1),
            cutoff_commutator_load=Fraction(0, 1),
            poincare_load=Fraction(0, 1),
            absorption_reserve=Fraction(0, 1),
            theorem_required="SeparateBkmAndClayPromotionTheorem",
            theorem_closed=False,
            notes="BKM and Clay booleans are intentionally false regardless of numeric budget rows.",
        ),
    ]
    return [row.as_row() for row in raw_rows]


def validate_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = {row["row_id"] for row in rows}
    missing = sorted(REQUIRED_ROW_IDS - row_ids)
    unexpected = sorted(row_ids - REQUIRED_ROW_IDS)
    duplicate_count = len(rows) - len(row_ids)
    bad_promotion_rows = [
        row["row_id"]
        for row in rows
        if row["clay"] or row["bkm"] or row["clay_solution"] or row["clay_navier_stokes_promoted"]
    ]
    open_rows = [
        row["row_id"]
        for row in rows
        if row["status"].startswith("open") or row["status"] in {"guard_false", "open_gap", "open_constants"}
    ]
    negative_margin_rows = [row["row_id"] for row in rows if Fraction(row["net_margin"]) < 0]
    numerically_absorbed_rows = [row["row_id"] for row in rows if row["numerically_absorbed"]]
    theorem_closed_rows = [row["row_id"] for row in rows if row["theorem_closed"]]
    valid = (
        not missing
        and not unexpected
        and duplicate_count == 0
        and not bad_promotion_rows
        and len(rows) == len(REQUIRED_ROW_IDS)
        and not theorem_closed_rows
    )
    return {
        "valid": valid,
        "missing_required_rows": missing,
        "unexpected_rows": unexpected,
        "duplicate_count": duplicate_count,
        "bad_promotion_rows": bad_promotion_rows,
        "open_rows": open_rows,
        "negative_margin_rows": negative_margin_rows,
        "numerically_absorbed_rows": numerically_absorbed_rows,
        "theorem_closed_rows": theorem_closed_rows,
        "all_bkm_and_clay_false": not bad_promotion_rows,
    }


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = sorted({key for row in rows for key in row})
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 155 Operator Boundary Term Checker",
        "",
        "This artifact checks the weighted `Ltilde` integration-by-parts ledger for radial measure `r dr dz`.",
        "It is not a proof artifact, and all BKM/Clay promotion flags remain false.",
        "",
        "## Decision",
        "",
        f"- decision: `{summary['decision']}`",
        f"- valid emitter output: `{summary['validation']['valid']}`",
        f"- BKM false: `{summary['bkm']}`",
        f"- Clay false: `{summary['clay']}`",
        f"- negative margin rows: `{', '.join(summary['validation']['negative_margin_rows'])}`",
        "",
        "## Numeric Budgets",
        "",
    ]
    for key, value in summary["constant_budget"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Rows",
            "",
            "| row | status | sign | margin | theorem closed |",
            "| --- | --- | --- | ---: | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {row_id} | {status} | {sign_expectation} | {net_margin} | {theorem_closed} |".format(
                **row
            )
        )
    lines.extend(
        [
            "",
            "## Open Obligations",
            "",
            "- Prove the radial and axial wall boundary signs or provide a trace absorption theorem tied to the wall model.",
            "- Close the annular weighted Poincare row with a mean-zero condition, boundary anchor, or annular exclusion theorem.",
            "- Package cutoff, trace, Young, viscosity, and Poincare constants into one simultaneous theorem.",
            "- Supply a separate BKM/Clay promotion theorem before changing any promotion flag.",
            "",
            "## Control Card",
            "",
        ]
    )
    for key, value in CONTROL_CARD.items():
        lines.append(f"- {key}: {value}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, files: list[Path]) -> dict[str, Any]:
    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "ledger": LEDGER,
        "files": [
            {
                "path": display_path(path, repo_root),
                "sha256": file_sha256(path),
                "bytes": path.stat().st_size if path.exists() else None,
            }
            for path in files
        ],
        "output_dir": display_path(out_dir, repo_root),
    }


def emit(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    repo_root = repo_root.resolve()
    out_dir = out_dir if out_dir.is_absolute() else repo_root / out_dir
    rows = build_rows()
    validation = validate_rows(rows)
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "ledger": LEDGER,
        "operator": OPERATOR,
        "weighted_measure": WEIGHTED_MEASURE,
        "decision": DECISION,
        "row_count": len(rows),
        "required_row_count": len(REQUIRED_ROW_IDS),
        "constant_budget": build_constant_budget(),
        "validation": validation,
        "control_card": CONTROL_CARD,
        "promotion_allowed": False,
        "fail_closed": True,
        "claim_closed": False,
        "claim_proved": False,
        "claim_proven": False,
        "emitted_files": [
            display_path(out_dir / ROWS_JSON_NAME, repo_root),
            display_path(out_dir / ROWS_CSV_NAME, repo_root),
            display_path(out_dir / SUMMARY_NAME, repo_root),
            display_path(out_dir / REPORT_NAME, repo_root),
            display_path(out_dir / MANIFEST_NAME, repo_root),
        ],
        **FAIL_CLOSED_FLAGS,
    }
    summary["summary_hash"] = stable_hash(summary)

    tmp_parent = out_dir.parent
    tmp_parent.mkdir(parents=True, exist_ok=True)
    tmp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=tmp_parent))
    try:
        rows_json = tmp_dir / ROWS_JSON_NAME
        rows_csv = tmp_dir / ROWS_CSV_NAME
        summary_json = tmp_dir / SUMMARY_NAME
        report_md = tmp_dir / REPORT_NAME
        manifest_json = tmp_dir / MANIFEST_NAME

        write_json(rows_json, rows)
        write_csv(rows_csv, rows)
        write_json(summary_json, summary)
        report_md.write_text(build_report(summary, rows), encoding="utf-8")
        manifest = build_manifest(repo_root, out_dir, [rows_json, rows_csv, summary_json, report_md])
        write_json(manifest_json, manifest)

        if out_dir.exists():
            shutil.rmtree(out_dir)
        os.replace(tmp_dir, out_dir)
    except Exception:
        shutil.rmtree(tmp_dir, ignore_errors=True)
        raise

    summary_path = out_dir / SUMMARY_NAME
    return json.loads(summary_path.read_text(encoding="utf-8"))


def main() -> int:
    args = parse_args()
    summary = emit(args.repo_root, args.out_dir)
    print(json.dumps(
        {
            "contract": summary["contract"],
            "decision": summary["decision"],
            "row_count": summary["row_count"],
            "valid": summary["validation"]["valid"],
            "bkm": summary["bkm"],
            "clay": summary["clay"],
            "output_dir": str(args.out_dir),
        },
        indent=2,
        sort_keys=True,
    ))
    return 0 if summary["validation"]["valid"] else 1


if __name__ == "__main__":
    sys.exit(main())
