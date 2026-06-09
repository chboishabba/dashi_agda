#!/usr/bin/env python3
"""Sprint 151 scale-delta cutoff error budget ledger.

This deterministic stdlib emitter records a cutoff-localization budget for a
formal Navier-Stokes/Hou-Luo route interface.  It is an accounting artifact, not
a proof: every proof-level flag remains false unless a theorem is explicitly
available.  The rows normalize symbolic powers of the cutoff thickness delta
against fixed numeric samples so that absorbed/support/open/blocker status is
stable across runs.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint151_cutoff_error_budget"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint151_cutoff_error_budget")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 151
LANE = 3
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
LEDGER = "ScaleDeltaCutoffErrorBudget"
DELTA_SYMBOL = "delta"
DELTA_SAMPLE = Fraction(1, 16)
ENERGY_SAMPLE = Fraction(3, 4)
GRADIENT_NORM_SAMPLE = Fraction(5, 2)
DIFFUSION_COEFFICIENT = Fraction(1, 64)
SOURCE_AMPLITUDE_SAMPLE = Fraction(9, 5)
ANNULAR_MASS_SAMPLE = Fraction(3, 10)
BASE_ABSORPTION_MARGIN = Fraction(240, 1)
DECISION = "fail_closed_cutoff_budget_has_open_and_blocker_rows"

CLASSIFICATIONS = ("absorbed", "support", "open", "blocker")
REQUIRED_ROW_IDS = {
    "cutoff_gradient_scale_delta_inverse",
    "cutoff_laplacian_scale_delta_inverse_square",
    "transport_flux_cutoff_boundary",
    "diffusion_leakage_cutoff_laplacian",
    "source_localization_core_window",
    "annular_leakage_outer_shell",
    "absorption_margin_transport_diffusion",
    "absorption_margin_annular_source",
}


@dataclass(frozen=True)
class BudgetRow:
    row_id: str
    category: str
    classification: str
    symbolic_term: str
    normalized_bound: str
    delta_power: int
    coefficient: Fraction
    measured_load: Fraction
    absorption_capacity: Fraction | None
    theorem_required: str
    theorem_level: bool
    proof_flag: bool
    notes: str

    def as_row(self) -> dict[str, Any]:
        scale_factor = DELTA_SAMPLE ** self.delta_power
        normalized_load = self.coefficient * scale_factor * self.measured_load
        capacity = self.absorption_capacity
        if capacity is None:
            budget_ratio: Fraction | None = None
            margin: Fraction | None = None
        else:
            budget_ratio = normalized_load / capacity
            margin = capacity - normalized_load

        row = asdict(self)
        row["coefficient"] = fraction_to_str(self.coefficient)
        row["measured_load"] = fraction_to_str(self.measured_load)
        row["absorption_capacity"] = (
            None if capacity is None else fraction_to_str(capacity)
        )
        row["sprint"] = SPRINT
        row["lane"] = LANE
        row["contract"] = CONTRACT
        row["program"] = PROGRAM
        row["ledger"] = LEDGER
        row["delta_symbol"] = DELTA_SYMBOL
        row["delta_sample"] = fraction_to_str(DELTA_SAMPLE)
        row["scale_factor_at_delta_sample"] = fraction_to_str(scale_factor)
        row["numeric_load_at_delta_sample"] = fraction_to_str(normalized_load)
        row["numeric_load_float"] = round(float(normalized_load), 12)
        row["budget_ratio"] = None if budget_ratio is None else fraction_to_str(budget_ratio)
        row["budget_ratio_float"] = (
            None if budget_ratio is None else round(float(budget_ratio), 12)
        )
        row["absorption_margin"] = None if margin is None else fraction_to_str(margin)
        row["absorbed_numerically"] = (
            False if margin is None else margin >= 0 and self.classification == "absorbed"
        )
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["clay_navier_stokes_promoted"] = False
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


def display_path(path: Path, repo_root: Path) -> str:
    try:
        return str(path.relative_to(repo_root))
    except ValueError:
        return str(path)


def fraction_to_str(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def build_rows() -> list[dict[str, Any]]:
    rows = [
        BudgetRow(
            row_id="cutoff_gradient_scale_delta_inverse",
            category="cutoff_derivative_scale",
            classification="support",
            symbolic_term="|grad phi_delta| <= C_grad / delta",
            normalized_bound="C_grad * delta^-1",
            delta_power=-1,
            coefficient=Fraction(2, 1),
            measured_load=ENERGY_SAMPLE,
            absorption_capacity=None,
            theorem_required="SmoothCutoffDerivativeBoundGradient",
            theorem_level=False,
            proof_flag=False,
            notes=(
                "Records the expected first-derivative scale.  It supports the "
                "budget but does not prove the analytic cutoff theorem here."
            ),
        ),
        BudgetRow(
            row_id="cutoff_laplacian_scale_delta_inverse_square",
            category="cutoff_derivative_scale",
            classification="support",
            symbolic_term="|lap phi_delta| <= C_lap / delta^2",
            normalized_bound="C_lap * delta^-2",
            delta_power=-2,
            coefficient=Fraction(5, 1),
            measured_load=ENERGY_SAMPLE,
            absorption_capacity=None,
            theorem_required="SmoothCutoffDerivativeBoundLaplacian",
            theorem_level=False,
            proof_flag=False,
            notes=(
                "Records the second-derivative scale that drives the diffusion "
                "leakage row.  No theorem-level certification is emitted."
            ),
        ),
        BudgetRow(
            row_id="transport_flux_cutoff_boundary",
            category="transport_flux",
            classification="absorbed",
            symbolic_term="int |u| |omega|^2 |grad phi_delta|",
            normalized_bound="C_transport * U * E_local * delta^-1",
            delta_power=-1,
            coefficient=Fraction(1, 8),
            measured_load=ENERGY_SAMPLE * GRADIENT_NORM_SAMPLE,
            absorption_capacity=Fraction(80, 1),
            theorem_required="CutoffTransportFluxAbsorption",
            theorem_level=False,
            proof_flag=False,
            notes=(
                "The deterministic sample is below the allocated absorption "
                "capacity, so this row is numerically absorbed only."
            ),
        ),
        BudgetRow(
            row_id="diffusion_leakage_cutoff_laplacian",
            category="diffusion_leakage",
            classification="absorbed",
            symbolic_term="nu int |omega|^2 |lap phi_delta|",
            normalized_bound="nu * C_lap * E_local * delta^-2",
            delta_power=-2,
            coefficient=DIFFUSION_COEFFICIENT * Fraction(5, 1),
            measured_load=ENERGY_SAMPLE,
            absorption_capacity=Fraction(75, 1),
            theorem_required="CutoffDiffusionLeakageAbsorption",
            theorem_level=False,
            proof_flag=False,
            notes=(
                "The laplacian scale is large, but the fixed viscosity-weighted "
                "sample remains under the local diffusion absorption reserve."
            ),
        ),
        BudgetRow(
            row_id="source_localization_core_window",
            category="source_localization",
            classification="open",
            symbolic_term="int phi_delta source_core",
            normalized_bound="C_source * source_amplitude * localization_quality",
            delta_power=0,
            coefficient=Fraction(7, 3),
            measured_load=SOURCE_AMPLITUDE_SAMPLE,
            absorption_capacity=Fraction(4, 1),
            theorem_required="LocalizedSourceDominanceOrCancellation",
            theorem_level=False,
            proof_flag=False,
            notes=(
                "The sampled source load slightly exceeds its reserve and lacks a "
                "dominance/cancellation theorem, so the row stays open."
            ),
        ),
        BudgetRow(
            row_id="annular_leakage_outer_shell",
            category="annular_leakage",
            classification="blocker",
            symbolic_term="int_{annulus(delta)} leakage_outer |grad phi_delta|",
            normalized_bound="C_annular * M_annular * delta^-1",
            delta_power=-1,
            coefficient=Fraction(9, 2),
            measured_load=ANNULAR_MASS_SAMPLE,
            absorption_capacity=Fraction(12, 1),
            theorem_required="AnnularLeakageExclusionOrDomination",
            theorem_level=False,
            proof_flag=False,
            notes=(
                "At the cutoff thickness sample, annular leakage overwhelms the "
                "reserved margin.  This is the explicit blocker row."
            ),
        ),
        BudgetRow(
            row_id="absorption_margin_transport_diffusion",
            category="absorption_margin",
            classification="absorbed",
            symbolic_term="M_td - transport_flux - diffusion_leakage",
            normalized_bound="M_td >= C_t delta^-1 + nu C_lap delta^-2",
            delta_power=0,
            coefficient=Fraction(1, 1),
            measured_load=Fraction(30, 1),
            absorption_capacity=BASE_ABSORPTION_MARGIN,
            theorem_required="JointTransportDiffusionAbsorptionMargin",
            theorem_level=False,
            proof_flag=False,
            notes=(
                "A coarse combined reserve remains positive for the deterministic "
                "transport/diffusion sample, so this is an absorbed budget margin."
            ),
        ),
        BudgetRow(
            row_id="absorption_margin_annular_source",
            category="absorption_margin",
            classification="open",
            symbolic_term="M_as - source_localization - annular_leakage",
            normalized_bound="M_as >= C_source + C_annular delta^-1",
            delta_power=0,
            coefficient=Fraction(1, 1),
            measured_load=Fraction(95, 1),
            absorption_capacity=Fraction(90, 1),
            theorem_required="JointAnnularSourceAbsorptionMargin",
            theorem_level=False,
            proof_flag=False,
            notes=(
                "The joint annular/source reserve is negative at the sample; it "
                "is open because the annular row is already the sharper blocker."
            ),
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = [row["row_id"] for row in rows]
    classification_counts = {
        name: sum(1 for row in rows if row["classification"] == name)
        for name in CLASSIFICATIONS
    }
    open_rows = [
        row["row_id"]
        for row in rows
        if row["classification"] in {"open", "blocker"}
    ]
    absorbed_rows = [
        row["row_id"]
        for row in rows
        if row["classification"] == "absorbed"
    ]
    support_rows = [
        row["row_id"]
        for row in rows
        if row["classification"] == "support"
    ]
    proof_flags_true = [row["row_id"] for row in rows if row["proof_flag"]]
    theorem_level_true = [row["row_id"] for row in rows if row["theorem_level"]]

    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "ledger": LEDGER,
        "decision": DECISION,
        "delta_symbol": DELTA_SYMBOL,
        "delta_sample": fraction_to_str(DELTA_SAMPLE),
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": row_ids,
        "missing_required_row_ids": sorted(REQUIRED_ROW_IDS.difference(row_ids)),
        "extra_row_ids": sorted(set(row_ids).difference(REQUIRED_ROW_IDS)),
        "classification_counts": classification_counts,
        "absorbed_rows": absorbed_rows,
        "support_rows": support_rows,
        "open_or_blocker_rows": open_rows,
        "proof_flags_true": proof_flags_true,
        "theorem_level_true": theorem_level_true,
        "cutoff_gradient_scale_recorded": True,
        "cutoff_laplacian_scale_recorded": True,
        "transport_flux_absorbed_numerically": "transport_flux_cutoff_boundary"
        in absorbed_rows,
        "diffusion_leakage_absorbed_numerically": "diffusion_leakage_cutoff_laplacian"
        in absorbed_rows,
        "source_localization_closed": False,
        "annular_leakage_closed": False,
        "absorption_margins_close_all_errors": False,
        "claim_closed": False,
        "claim_proved": False,
        "claim_proven": False,
        "global_proof": False,
        "clay_navier_stokes_promoted": False,
        "validation_passed": False,
    }
    summary["summary_hash"] = stable_hash(
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )
    return summary


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    errors: list[str] = []
    classifications = {row["classification"] for row in rows}
    if summary["missing_required_row_ids"]:
        errors.append(f"missing required rows: {summary['missing_required_row_ids']}")
    if summary["extra_row_ids"]:
        errors.append(f"unexpected rows: {summary['extra_row_ids']}")
    if not classifications.issubset(set(CLASSIFICATIONS)):
        errors.append(f"unknown classifications: {sorted(classifications)}")
    for required in CLASSIFICATIONS:
        if summary["classification_counts"][required] == 0:
            errors.append(f"classification absent: {required}")
    if summary["proof_flags_true"]:
        errors.append(f"proof flags unexpectedly true: {summary['proof_flags_true']}")
    if summary["theorem_level_true"]:
        errors.append(f"theorem-level flags unexpectedly true: {summary['theorem_level_true']}")
    if not summary["open_or_blocker_rows"]:
        errors.append("ledger incorrectly closes all rows")
    if any(row["claim_closed"] or row["claim_proved"] or row["claim_proven"] for row in rows):
        errors.append("at least one row incorrectly proves or closes the claim")
    if any(row["clay_navier_stokes_promoted"] for row in rows):
        errors.append("at least one row incorrectly emits Clay promotion")

    row_by_id = {row["row_id"]: row for row in rows}
    if row_by_id["transport_flux_cutoff_boundary"]["classification"] != "absorbed":
        errors.append("transport flux row must be classified absorbed")
    if row_by_id["diffusion_leakage_cutoff_laplacian"]["classification"] != "absorbed":
        errors.append("diffusion leakage row must be classified absorbed")
    if row_by_id["source_localization_core_window"]["classification"] != "open":
        errors.append("source localization row must be classified open")
    if row_by_id["annular_leakage_outer_shell"]["classification"] != "blocker":
        errors.append("annular leakage row must be classified blocker")

    if errors:
        raise ValueError("; ".join(errors))

    summary["validation_passed"] = True
    summary["validation_errors"] = []
    summary["summary_hash"] = stable_hash(
        {k: v for k, v in summary.items() if k != "summary_hash"}
    )


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    key: json.dumps(value, sort_keys=True)
                    if isinstance(value, list)
                    else value
                    for key, value in row.items()
                }
            )


def write_markdown(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    lines = [
        f"# {CONTRACT}",
        "",
        "## Decision",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Delta sample: `{summary['delta_sample']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        f"- Claim closed: `{summary['claim_closed']}`",
        f"- Proof flags true: `{summary['proof_flags_true']}`",
        f"- Clay promotion: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Classification Counts",
        "",
    ]
    for name in CLASSIFICATIONS:
        lines.append(f"- {name}: `{summary['classification_counts'][name]}`")
    lines.extend(
        [
            "",
            "## Rows",
            "",
            "| row_id | category | class | symbolic term | numeric load | capacity | ratio | theorem required |",
            "| --- | --- | --- | --- | ---: | ---: | ---: | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {row_id} | {category} | {classification} | {symbolic_term} | "
            "{numeric_load_at_delta_sample} | {absorption_capacity} | "
            "{budget_ratio} | {theorem_required} |".format(
                row_id=row["row_id"],
                category=row["category"],
                classification=row["classification"],
                symbolic_term=row["symbolic_term"].replace("|", "/"),
                numeric_load_at_delta_sample=row["numeric_load_at_delta_sample"],
                absorption_capacity=row["absorption_capacity"],
                budget_ratio=row["budget_ratio"],
                theorem_required=row["theorem_required"],
            )
        )
    lines.extend(
        [
            "",
            "## Governance",
            "",
            "This ledger is deterministic cutoff-budget accounting.  It records "
            "symbolic delta powers and fixed numeric samples, but it emits no "
            "theorem-level proof, no global closure, and no Clay promotion.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate(rows, summary)

    summary_path = out_dir / SUMMARY_NAME
    rows_json_path = out_dir / ROWS_JSON_NAME
    rows_csv_path = out_dir / ROWS_CSV_NAME
    report_path = out_dir / REPORT_NAME
    manifest_path = out_dir / MANIFEST_NAME

    write_json(summary_path, summary)
    write_json(rows_json_path, rows)
    write_csv(rows_csv_path, rows)
    write_markdown(report_path, summary, rows)

    manifest = {
        "contract": CONTRACT,
        "files": {
            "summary": display_path(summary_path, repo_root),
            "rows_json": display_path(rows_json_path, repo_root),
            "rows_csv": display_path(rows_csv_path, repo_root),
            "markdown": display_path(report_path, repo_root),
            "manifest": display_path(manifest_path, repo_root),
        },
        "sha256": {
            "summary": file_sha256(summary_path),
            "rows_json": file_sha256(rows_json_path),
            "rows_csv": file_sha256(rows_csv_path),
            "markdown": file_sha256(report_path),
        },
        "validation_passed": summary["validation_passed"],
    }
    write_json(manifest_path, manifest)

    print(json.dumps(manifest, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
