#!/usr/bin/env python3
"""Sprint 153 source/dissipation/leakage balance ledger.

This deterministic stdlib emitter compares the localized vortex-stretching core
source against a half-coercive viscous dissipation reserve and the Sprint152
bounded-leakage residual interface.  It is an accounting artifact, not a proof:
Young split rows and residual/open rows keep all simultaneous constants, model
validity, BKM, and Clay promotion flags false unless every required row is
closed.
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


CONTRACT = "ns_sprint153_source_dissipation_balance"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint153_source_dissipation_balance")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 153
LANE = 4
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
LEDGER = "LocalizedSourceHalfCoerciveDissipationLeakageBalance"
PARENT_GATE = "Sprint153SourceDissipationBalance"
DECISION = "fail_closed_source_dissipation_balance_has_residual_and_open_rows"

CLASSIFICATIONS = ("absorbed", "residual", "open")
REQUIRED_ROW_IDS = {
    "localized_vortex_stretching_core_source",
    "half_coercive_viscous_dissipation_reserve",
    "sprint152_bounded_leakage_residual",
    "young_split_core_gradient_absorbed",
    "young_split_core_amplitude_residual",
    "young_split_leakage_gradient_absorbed",
    "young_split_leakage_amplitude_residual",
    "source_vs_half_dissipation_plus_leakage",
    "simultaneous_constants_compatibility",
    "model_validity_bkm_clay_guard",
}

CONTROL_CARD = {
    "O": (
        "Worker 4 owns only the Sprint153 source/dissipation balance emitter "
        "and outputs/ns_sprint153_source_dissipation_balance/ artifacts."
    ),
    "R": (
        "Emit JSON/CSV/manifest rows comparing localized vortex-stretching core "
        "source to half-coercive viscous dissipation and the Sprint152 bounded "
        "leakage residual, with Young-split accounting and fail-closed flags."
    ),
    "C": (
        "A single stdlib Python script writes rows JSON, rows CSV, summary JSON, "
        "Markdown, and manifest through an atomic output-directory swap."
    ),
    "S": (
        "The deterministic sample absorbs gradient pieces but leaves amplitude "
        "and leakage residuals open; there is no Sprint152 source artifact in "
        "this checkout, so the residual is recorded as an interface obligation."
    ),
    "L": (
        "Rows -> closed classifications -> simultaneous constants -> model "
        "validity -> BKM guard -> Clay guard."
    ),
    "P": (
        "Use this ledger to isolate which Young remainders and leakage residuals "
        "must close before the route can promote any downstream theorem flag."
    ),
    "G": (
        "Promotion is permitted only when every required row is present and every "
        "row classification is absorbed/closed; otherwise constants, model "
        "validity, BKM, and Clay booleans must remain false."
    ),
    "F": (
        "Missing evidence: theorem-level control of Young amplitude remainders, "
        "Sprint152 leakage residual closure, simultaneous constants, and the "
        "standard BKM/Clay translation."
    ),
}


@dataclass(frozen=True)
class BalanceRow:
    row_id: str
    category: str
    classification: str
    expression: str
    source_load: Fraction
    half_dissipation_credit: Fraction
    leakage_residual_load: Fraction
    young_epsilon: Fraction | None
    theorem_required: str
    proof_flag: bool
    notes: str

    def as_row(self) -> dict[str, Any]:
        net_margin = (
            self.half_dissipation_credit
            - self.source_load
            - self.leakage_residual_load
        )
        closed = self.classification == "absorbed" and net_margin >= 0 and self.proof_flag
        numerically_absorbed = self.classification == "absorbed" and net_margin >= 0

        row = asdict(self)
        row.update(
            {
                "sprint": SPRINT,
                "lane": LANE,
                "contract": CONTRACT,
                "program": PROGRAM,
                "ledger": LEDGER,
                "parent_gate": PARENT_GATE,
                "decision": DECISION,
                "source_load": fraction_to_str(self.source_load),
                "half_dissipation_credit": fraction_to_str(self.half_dissipation_credit),
                "leakage_residual_load": fraction_to_str(self.leakage_residual_load),
                "young_epsilon": (
                    None if self.young_epsilon is None else fraction_to_str(self.young_epsilon)
                ),
                "net_margin": fraction_to_str(net_margin),
                "net_margin_float": round(float(net_margin), 12),
                "numerically_absorbed": numerically_absorbed,
                "closed": closed,
                "claim_closed": closed,
                "claim_proved": False,
                "claim_proven": False,
                "simultaneous_constants_valid": False,
                "model_validity_closed": False,
                "bkm_guard_closed": False,
                "clay_navier_stokes_promoted": False,
                "promotion_allowed": False,
                "fail_closed": not closed,
            }
        )
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


def build_rows() -> list[dict[str, Any]]:
    rows = [
        BalanceRow(
            row_id="localized_vortex_stretching_core_source",
            category="core_source",
            classification="residual",
            expression="int phi_R (omega dot grad u dot omega)_core",
            source_load=Fraction(42, 1),
            half_dissipation_credit=Fraction(0, 1),
            leakage_residual_load=Fraction(0, 1),
            young_epsilon=None,
            theorem_required="LocalizedVortexStretchingCoreSourceLowerUpperPin",
            proof_flag=False,
            notes="Core source is recorded as the active load to compare against the reserve.",
        ),
        BalanceRow(
            row_id="half_coercive_viscous_dissipation_reserve",
            category="viscous_dissipation",
            classification="absorbed",
            expression="(nu/2) int phi_R |grad omega|^2",
            source_load=Fraction(0, 1),
            half_dissipation_credit=Fraction(48, 1),
            leakage_residual_load=Fraction(0, 1),
            young_epsilon=None,
            theorem_required="HalfCoerciveLocalizedViscousDissipationReserve",
            proof_flag=False,
            notes="The deterministic reserve is positive, but theorem-level coercivity is not emitted.",
        ),
        BalanceRow(
            row_id="sprint152_bounded_leakage_residual",
            category="bounded_leakage_residual",
            classification="residual",
            expression="R_152 <= bounded leakage residual entering localized balance",
            source_load=Fraction(0, 1),
            half_dissipation_credit=Fraction(0, 1),
            leakage_residual_load=Fraction(17, 1),
            young_epsilon=None,
            theorem_required="Sprint152BoundedLeakageResidualClosedWithConstants",
            proof_flag=False,
            notes="No Sprint152 artifact is present locally; this row preserves the interface obligation.",
        ),
        BalanceRow(
            row_id="young_split_core_gradient_absorbed",
            category="young_split",
            classification="absorbed",
            expression="a_core b_grad <= epsilon |grad omega|^2 + C_epsilon a_core^2",
            source_load=Fraction(9, 1),
            half_dissipation_credit=Fraction(16, 1),
            leakage_residual_load=Fraction(0, 1),
            young_epsilon=Fraction(1, 8),
            theorem_required="YoungSplitCoreGradientAbsorption",
            proof_flag=False,
            notes="Gradient part is numerically absorbed by the half-coercive reserve.",
        ),
        BalanceRow(
            row_id="young_split_core_amplitude_residual",
            category="young_split",
            classification="residual",
            expression="C_epsilon a_core^2 remains after gradient absorption",
            source_load=Fraction(21, 1),
            half_dissipation_credit=Fraction(0, 1),
            leakage_residual_load=Fraction(0, 1),
            young_epsilon=Fraction(1, 8),
            theorem_required="YoungSplitCoreAmplitudeResidualControl",
            proof_flag=False,
            notes="Amplitude remainder lacks a uniform source-side closure lemma.",
        ),
        BalanceRow(
            row_id="young_split_leakage_gradient_absorbed",
            category="young_split",
            classification="absorbed",
            expression="a_leak b_grad <= epsilon |grad omega|^2 + C_epsilon a_leak^2",
            source_load=Fraction(5, 1),
            half_dissipation_credit=Fraction(8, 1),
            leakage_residual_load=Fraction(0, 1),
            young_epsilon=Fraction(1, 16),
            theorem_required="YoungSplitLeakageGradientAbsorption",
            proof_flag=False,
            notes="Leakage-gradient piece is numerically absorbed by the remaining reserve.",
        ),
        BalanceRow(
            row_id="young_split_leakage_amplitude_residual",
            category="young_split",
            classification="residual",
            expression="C_epsilon a_leak^2 remains after leakage-gradient absorption",
            source_load=Fraction(0, 1),
            half_dissipation_credit=Fraction(0, 1),
            leakage_residual_load=Fraction(11, 1),
            young_epsilon=Fraction(1, 16),
            theorem_required="YoungSplitLeakageAmplitudeResidualControl",
            proof_flag=False,
            notes="Leakage amplitude remainder is bounded but not closed.",
        ),
        BalanceRow(
            row_id="source_vs_half_dissipation_plus_leakage",
            category="comparison",
            classification="open",
            expression="S_core <= (nu/2)D + R_152 + Young residuals",
            source_load=Fraction(42, 1),
            half_dissipation_credit=Fraction(48, 1),
            leakage_residual_load=Fraction(28, 1),
            young_epsilon=None,
            theorem_required="CoreSourceDominatedByHalfDissipationAndClosedLeakage",
            proof_flag=False,
            notes="The sampled total has negative margin once Sprint152 and Young residuals are included.",
        ),
        BalanceRow(
            row_id="simultaneous_constants_compatibility",
            category="constants",
            classification="open",
            expression="one epsilon/constant package closes source, dissipation, and leakage rows",
            source_load=Fraction(1, 1),
            half_dissipation_credit=Fraction(0, 1),
            leakage_residual_load=Fraction(1, 1),
            young_epsilon=None,
            theorem_required="SimultaneousConstantsCompatibilityForSprint153",
            proof_flag=False,
            notes="Constants cannot be promoted while residual/open comparison rows remain.",
        ),
        BalanceRow(
            row_id="model_validity_bkm_clay_guard",
            category="governance",
            classification="open",
            expression="closed localized balance -> model validity -> BKM -> Clay",
            source_load=Fraction(1, 1),
            half_dissipation_credit=Fraction(0, 1),
            leakage_residual_load=Fraction(1, 1),
            young_epsilon=None,
            theorem_required="ModelValidityBkmClayTranslationAfterAllRowsClosed",
            proof_flag=False,
            notes="Downstream validity, BKM, and Clay flags stay false until every row is closed.",
        ),
    ]
    return [row.as_row() for row in rows]


def validate(rows: list[dict[str, Any]], summary: dict[str, Any] | None = None) -> list[str]:
    errors: list[str] = []
    row_ids = {str(row["row_id"]) for row in rows}
    if missing := sorted(REQUIRED_ROW_IDS - row_ids):
        errors.append("missing required rows: " + ", ".join(missing))
    if extra := sorted(row_ids - REQUIRED_ROW_IDS):
        errors.append("unexpected rows: " + ", ".join(extra))
    classifications = {str(row["classification"]) for row in rows}
    if not classifications.issubset(set(CLASSIFICATIONS)):
        errors.append("unknown classifications: " + ", ".join(sorted(classifications)))
    for required in CLASSIFICATIONS:
        if required not in classifications:
            errors.append(f"classification absent: {required}")

    all_rows_closed = all(bool(row["closed"]) for row in rows)
    for row in rows:
        if row["classification"] in {"residual", "open"} and row["closed"]:
            errors.append(f"{row['row_id']} residual/open row cannot be closed")
        for flag in (
            "claim_proved",
            "claim_proven",
            "simultaneous_constants_valid",
            "model_validity_closed",
            "bkm_guard_closed",
            "clay_navier_stokes_promoted",
            "promotion_allowed",
        ):
            if row.get(flag):
                errors.append(f"{row['row_id']} incorrectly sets {flag}=true")

    if summary is not None:
        if summary["all_required_rows_closed"] != all_rows_closed:
            errors.append("summary all_required_rows_closed mismatch")
        guard_flags = (
            "simultaneous_constants_valid",
            "model_validity_closed",
            "bkm_guard_closed",
            "clay_navier_stokes_promoted",
            "promotion_allowed",
        )
        for flag in guard_flags:
            if summary.get(flag) is not all_rows_closed:
                errors.append(f"summary {flag} must equal all_required_rows_closed")
        if not summary["open_or_residual_rows"]:
            errors.append("ledger must expose residual/open rows for this sprint state")
    return errors


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    classification_counts = {
        name: sum(1 for row in rows if row["classification"] == name)
        for name in CLASSIFICATIONS
    }
    open_or_residual_rows = [
        row["row_id"] for row in rows if row["classification"] in {"residual", "open"}
    ]
    absorbed_rows = [row["row_id"] for row in rows if row["classification"] == "absorbed"]
    all_required_rows_closed = all(bool(row["closed"]) for row in rows)
    net_margin_total = sum(
        Fraction(str(row["net_margin"])) if "/" not in str(row["net_margin"]) else parse_fraction(str(row["net_margin"]))
        for row in rows
    )

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "ledger": LEDGER,
        "parent_gate": PARENT_GATE,
        "decision": DECISION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": [row["row_id"] for row in rows],
        "missing_required_row_ids": sorted(REQUIRED_ROW_IDS - {row["row_id"] for row in rows}),
        "classification_counts": classification_counts,
        "absorbed_rows": absorbed_rows,
        "open_or_residual_rows": open_or_residual_rows,
        "young_split_rows": [
            row["row_id"] for row in rows if str(row["row_id"]).startswith("young_split_")
        ],
        "all_required_rows_closed": all_required_rows_closed,
        "total_net_margin": fraction_to_str(net_margin_total),
        "localized_vortex_stretching_core_source": "42",
        "half_coercive_viscous_dissipation_reserve": "48",
        "sprint152_bounded_leakage_residual": "17",
        "simultaneous_constants_valid": all_required_rows_closed,
        "model_validity_closed": all_required_rows_closed,
        "bkm_guard_closed": all_required_rows_closed,
        "clay_navier_stokes_promoted": all_required_rows_closed,
        "promotion_allowed": all_required_rows_closed,
        "claim_closed": all_required_rows_closed,
        "claim_proved": False,
        "claim_proven": False,
        "fail_closed": not all_required_rows_closed,
        "control_card": CONTROL_CARD,
        "validation_passed": False,
        "validation_errors": [],
    }
    errors = validate(rows, summary)
    summary["validation_errors"] = errors
    summary["validation_passed"] = not errors
    summary["summary_hash"] = stable_hash(
        {key: value for key, value in summary.items() if key != "summary_hash"}
    )
    return summary


def parse_fraction(value: str) -> Fraction:
    numerator, denominator = value.split("/", 1)
    return Fraction(int(numerator), int(denominator))


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 153 Source/Dissipation Balance",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        f"- All required rows closed: `{summary['all_required_rows_closed']}`",
        f"- Simultaneous constants valid: `{summary['simultaneous_constants_valid']}`",
        f"- Model validity closed: `{summary['model_validity_closed']}`",
        f"- BKM guard closed: `{summary['bkm_guard_closed']}`",
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
            "## Rows",
            "",
            "| row_id | category | class | source | half dissipation | leakage | margin | theorem |",
            "| --- | --- | --- | ---: | ---: | ---: | ---: | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {row_id} | {category} | {classification} | {source_load} | "
            "{half_dissipation_credit} | {leakage_residual_load} | {net_margin} | "
            "{theorem_required} |".format(**row)
        )
    lines.extend(
        [
            "",
            "## Guard",
            "",
            "This ledger closes no theorem-level Navier-Stokes claim. Residual/open "
            "rows force simultaneous constants, model validity, BKM, and Clay "
            "promotion booleans to remain false.",
            "",
        ]
    )
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / SUMMARY_NAME,
        "rows_json": out_dir / ROWS_JSON_NAME,
        "rows_csv": out_dir / ROWS_CSV_NAME,
        "markdown": out_dir / REPORT_NAME,
        "manifest": out_dir / MANIFEST_NAME,
    }
    manifest: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "decision": DECISION,
        "validation_passed": summary["validation_passed"],
        "all_required_rows_closed": summary["all_required_rows_closed"],
        "simultaneous_constants_valid": summary["simultaneous_constants_valid"],
        "model_validity_closed": summary["model_validity_closed"],
        "bkm_guard_closed": summary["bkm_guard_closed"],
        "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
        "promotion_allowed": summary["promotion_allowed"],
        "files": {
            key: {
                "path": display_path(path, repo_root),
                "exists": path.exists(),
                "sha256": file_sha256(path),
            }
            for key, path in files.items()
        },
    }
    manifest["manifest_hash"] = stable_hash(
        {key: value for key, value in manifest.items() if key != "manifest_hash"}
    )
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / ROWS_JSON_NAME, rows)
        write_csv(temp_dir / ROWS_CSV_NAME, rows)
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")
        write_json(temp_dir / MANIFEST_NAME, build_manifest(repo_root, temp_dir, summary))
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        write_json(final_out / MANIFEST_NAME, build_manifest(repo_root, final_out, summary))
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    rows = build_rows()
    summary = build_summary(rows)
    write_outputs(repo_root, args.out_dir, rows, summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "validation_passed": summary["validation_passed"],
                "row_count": summary["row_count"],
                "classification_counts": summary["classification_counts"],
                "all_required_rows_closed": summary["all_required_rows_closed"],
                "simultaneous_constants_valid": summary["simultaneous_constants_valid"],
                "model_validity_closed": summary["model_validity_closed"],
                "bkm_guard_closed": summary["bkm_guard_closed"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "out_dir": display_path(
                    args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir,
                    repo_root,
                ),
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
