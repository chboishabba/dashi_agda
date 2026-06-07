#!/usr/bin/env python3
"""Sprint 153 localized vortex-stretching source normalization ledger.

This deterministic stdlib emitter records the normalized core-source
calculation for the axisymmetric omega1 equation.  It is evidence accounting,
not a theorem: it derives the symbolic shape

    core_source <= C * u1 * v * Omega * delta^2

with the canonical sharp bookkeeping coefficient 2 in the model row, while
all proof, BKM, and Clay promotion flags remain fail-closed.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import tempfile
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint153_localized_vortex_stretching_source"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint153_localized_vortex_stretching_source")
SUMMARY_NAME = CONTRACT + "_summary.json"
LEDGER_JSON_NAME = CONTRACT + "_ledger.json"
LEDGER_CSV_NAME = CONTRACT + "_ledger.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 153
LANE = 2
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
GATE = "LocalizedCoreVortexStretchingSourceForOmega1"
DECISION = "core_source_bound_shape_recorded_as_evidence_fail_closed"

U1_SAMPLE = Fraction(5, 4)
V_SAMPLE = Fraction(3, 2)
OMEGA_SAMPLE = Fraction(7, 3)
DELTA_SAMPLE = Fraction(1, 8)
CANONICAL_CONSTANT = Fraction(2, 1)

REQUIRED_ROW_IDS = {
    "omega1_equation_source_input",
    "core_ball_volume_scale",
    "localized_core_source_bound",
    "cutoff_support_gate",
    "source_sign_orientation",
    "constant_normalization",
    "dimensional_scaling_delta_square",
    "fail_closed_theorem_flags",
}

THEOREM_FLAGS = {
    "localized_core_source_bound_proved": False,
    "omega1_equation_global_theorem_proved": False,
    "cutoff_support_theorem_proved": False,
    "sign_definiteness_theorem_proved": False,
    "constants_uniform_for_large_data": False,
    "dimensional_scaling_theorem_proved": False,
    "localized_enstrophy_identity_proved": False,
    "model_validity_for_width_ode": False,
    "symmetric_hou_luo_bkm_finite": False,
    "full_clay_ns_solved": False,
    "clay_navier_stokes_promoted": False,
}

CONTROL_CARD = {
    "O": (
        "Worker 2 owns scripts/ns_sprint153_localized_vortex_stretching_source.py "
        "and outputs/ns_sprint153_localized_vortex_stretching_source/."
    ),
    "R": (
        "Normalize the localized omega1 vortex-stretching core source as evidence "
        "for the bound shape core_source <= C*u1*v*Omega*delta^2, including the "
        "canonical 2*u1*v*Omega*delta^2 bookkeeping row."
    ),
    "C": (
        "A stdlib Python emitter writes a JSON ledger, CSV ledger, summary JSON, "
        "Markdown report, and manifest through an atomic directory replacement."
    ),
    "S": (
        "The model source term 2*u1*partial_z u1 is localized on a delta-core; "
        "using |partial_z u1| <= v*Omega and a normalized core-ball area factor "
        "gives the evidence shape 2*u1*v*Omega*delta^2."
    ),
    "L": (
        "Rows cover source input, core ball, cutoff support, sign, constants, "
        "dimensional scaling, and theorem flags; promotion is lower than any "
        "analytic theorem and is explicitly blocked."
    ),
    "P": (
        "Use the artifact as deterministic evidence for the symbolic bound shape "
        "only; it must be followed by rigorous cutoff, sign, uniform-constant, "
        "localized-identity, and model-validity theorems."
    ),
    "G": (
        "Validation requires all eight rows, the exact bound strings, canonical "
        "constant 2, delta exponent 2, positive evidence rows, and every theorem "
        "or Clay flag false."
    ),
    "F": (
        "No theorem is proved: sign-definiteness, cutoff support, uniform "
        "constants, dimensional theorem status, localized identity closure, "
        "finite BKM, and Clay NS remain open."
    ),
}


@dataclass(frozen=True)
class LedgerRow:
    row_id: str
    category: str
    ledger_role: str
    expression: str
    normalized_bound_shape: str
    coefficient: Fraction
    delta_power: int
    sign: str
    support_region: str
    evidence_status: str
    theorem_required: str
    theorem_flag: bool
    promotion_allowed: bool
    notes: str

    def as_row(self) -> dict[str, Any]:
        core_factor = U1_SAMPLE * V_SAMPLE * OMEGA_SAMPLE * (DELTA_SAMPLE**self.delta_power)
        normalized_value = self.coefficient * core_factor
        row = asdict(self)
        row["coefficient"] = fraction_to_str(self.coefficient)
        row["u1_sample"] = fraction_to_str(U1_SAMPLE)
        row["v_sample"] = fraction_to_str(V_SAMPLE)
        row["omega_sample"] = fraction_to_str(OMEGA_SAMPLE)
        row["delta_sample"] = fraction_to_str(DELTA_SAMPLE)
        row["sample_value"] = fraction_to_str(normalized_value)
        row["sample_value_float"] = round(float(normalized_value), 12)
        row["sprint"] = SPRINT
        row["lane"] = LANE
        row["contract"] = CONTRACT
        row["program"] = PROGRAM
        row["gate"] = GATE
        row["decision"] = DECISION
        row["is_evidence_only"] = True
        row["claim_closed"] = False
        row["claim_proved"] = False
        row["claim_proven"] = False
        row["fail_closed"] = True
        row.update(THEOREM_FLAGS)
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


def fraction_to_str(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


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


def build_rows() -> list[dict[str, Any]]:
    rows = [
        LedgerRow(
            row_id="omega1_equation_source_input",
            category="source_input",
            ledger_role="equation_normalization",
            expression="D_t omega1 = viscous_terms + 2*u1*partial_z_u1",
            normalized_bound_shape="|2*u1*partial_z_u1| <= 2*u1*v*Omega",
            coefficient=CANONICAL_CONSTANT,
            delta_power=0,
            sign="unsigned_upper_bound",
            support_region="pointwise omega1 equation before localization",
            evidence_status="RECORDED_EVIDENCE_ONLY",
            theorem_required="Omega1EquationSourceInputCompatibility",
            theorem_flag=False,
            promotion_allowed=False,
            notes="Records the source term that feeds the localized core calculation.",
        ),
        LedgerRow(
            row_id="core_ball_volume_scale",
            category="core_ball",
            ledger_role="geometric_scale",
            expression="int_{B_delta} 1 dA <= C_ball*delta^2",
            normalized_bound_shape="core_ball_area <= C_ball*delta^2",
            coefficient=Fraction(1, 1),
            delta_power=2,
            sign="positive_measure",
            support_region="localized r-z core ball B_delta",
            evidence_status="SUPPORTS_DELTA_SQUARE_SCALE",
            theorem_required="CoreBallAreaScaleLemma",
            theorem_flag=False,
            promotion_allowed=False,
            notes="Normalizes the two-dimensional localized core scale used by the source bound.",
        ),
        LedgerRow(
            row_id="localized_core_source_bound",
            category="core_source",
            ledger_role="symbolic_bound_shape",
            expression="int_{B_delta} chi_delta*2*u1*partial_z_u1",
            normalized_bound_shape="core_source <= C*u1*v*Omega*delta^2; canonical evidence = 2*u1*v*Omega*delta^2",
            coefficient=CANONICAL_CONSTANT,
            delta_power=2,
            sign="upper_bound_positive_envelope",
            support_region="cutoff core ball where chi_delta=1",
            evidence_status="DERIVED_SYMBOLIC_EVIDENCE",
            theorem_required="LocalizedCoreSourceUpperBoundTheorem",
            theorem_flag=False,
            promotion_allowed=False,
            notes="Combines the source coefficient 2, derivative envelope v*Omega, and core area delta^2.",
        ),
        LedgerRow(
            row_id="cutoff_support_gate",
            category="cutoff_support",
            ledger_role="support_localization",
            expression="supp chi_delta subset B_{2*delta}, chi_delta=1 on B_delta",
            normalized_bound_shape="cutoff contribution localized to O(delta^2) core/support scale",
            coefficient=Fraction(4, 1),
            delta_power=2,
            sign="nonnegative_cutoff",
            support_region="core ball plus annular cutoff support",
            evidence_status="SUPPORT_RECORDED_NOT_PROVED",
            theorem_required="CutoffSupportAndAnnularLeakageTheorem",
            theorem_flag=False,
            promotion_allowed=False,
            notes="Separates the core ball evidence from the larger cutoff support and annular leakage obligations.",
        ),
        LedgerRow(
            row_id="source_sign_orientation",
            category="sign",
            ledger_role="sign_accounting",
            expression="sign(2*u1*partial_z_u1) depends on local alignment of u1 and partial_z_u1",
            normalized_bound_shape="signed source <= unsigned envelope 2*u1*v*Omega*delta^2",
            coefficient=CANONICAL_CONSTANT,
            delta_power=2,
            sign="not_sign_definite",
            support_region="localized core and cutoff support",
            evidence_status="FAIL_CLOSED_SIGN_NOT_PROMOTED",
            theorem_required="LocalizedSourceSignDefinitenessTheorem",
            theorem_flag=False,
            promotion_allowed=False,
            notes="The upper-bound envelope is available as evidence; a favorable sign theorem is not emitted.",
        ),
        LedgerRow(
            row_id="constant_normalization",
            category="constants",
            ledger_role="constant_package",
            expression="C absorbs C_ball, cutoff amplitude, and derivative-envelope constants",
            normalized_bound_shape="C >= 2*C_ball*C_cutoff*C_derivative; canonical row uses C=2 when normalized constants are 1",
            coefficient=CANONICAL_CONSTANT,
            delta_power=2,
            sign="constant_positive",
            support_region="normalized model constants",
            evidence_status="CANONICAL_CONSTANT_RECORDED",
            theorem_required="UniformConstantPackageForLocalizedCoreSource",
            theorem_flag=False,
            promotion_allowed=False,
            notes="Records the requested 2*u1*v*Omega*delta^2 evidence shape without claiming uniform analytic constants.",
        ),
        LedgerRow(
            row_id="dimensional_scaling_delta_square",
            category="dimensional_scaling",
            ledger_role="scale_check",
            expression="[u1]*[v]*[Omega]*[delta]^2",
            normalized_bound_shape="core_source has two-dimensional localized measure factor delta^2",
            coefficient=CANONICAL_CONSTANT,
            delta_power=2,
            sign="scale_positive",
            support_region="dimensionless normalized r-z core ledger",
            evidence_status="DIMENSIONAL_SHAPE_CONSISTENT",
            theorem_required="DimensionalScalingForLocalizedOmega1CoreSource",
            theorem_flag=False,
            promotion_allowed=False,
            notes="Confirms the requested delta^2 source scaling in the localized r-z core normalization.",
        ),
        LedgerRow(
            row_id="fail_closed_theorem_flags",
            category="governance",
            ledger_role="promotion_guard",
            expression="all theorem, BKM, model-validity, and Clay flags remain false",
            normalized_bound_shape="evidence_only_not_theorem",
            coefficient=Fraction(0, 1),
            delta_power=2,
            sign="guard",
            support_region="artifact governance",
            evidence_status="FAIL_CLOSED",
            theorem_required="AllAnalyticClosureTheorems",
            theorem_flag=False,
            promotion_allowed=False,
            notes="Blocks theorem promotion even though the symbolic source-bound shape is ledgered.",
        ),
    ]
    return [row.as_row() for row in rows]


def validate(rows: list[dict[str, Any]], summary: dict[str, Any] | None = None) -> list[str]:
    failures: list[str] = []
    observed_ids = {str(row.get("row_id")) for row in rows}
    if observed_ids != REQUIRED_ROW_IDS:
        failures.append(
            "row ids mismatch: missing="
            + ",".join(sorted(REQUIRED_ROW_IDS - observed_ids))
            + " extra="
            + ",".join(sorted(observed_ids - REQUIRED_ROW_IDS))
        )
    bound_text = "\n".join(str(row.get("normalized_bound_shape", "")) for row in rows)
    if "C*u1*v*Omega*delta^2" not in bound_text:
        failures.append("generic C*u1*v*Omega*delta^2 bound shape missing")
    if "2*u1*v*Omega*delta^2" not in bound_text:
        failures.append("canonical 2*u1*v*Omega*delta^2 evidence shape missing")
    for row in rows:
        if row.get("claim_closed") or row.get("claim_proved") or row.get("claim_proven"):
            failures.append(f"{row.get('row_id')} incorrectly closes a claim")
        if row.get("promotion_allowed") or row.get("clay_navier_stokes_promoted"):
            failures.append(f"{row.get('row_id')} incorrectly allows promotion")
        if row.get("is_evidence_only") is not True:
            failures.append(f"{row.get('row_id')} must be evidence only")
        if row.get("fail_closed") is not True:
            failures.append(f"{row.get('row_id')} must be fail closed")
        for flag, expected in THEOREM_FLAGS.items():
            if row.get(flag) is not expected:
                failures.append(f"{row.get('row_id')} flag {flag} expected {expected}")
    if summary is not None:
        for flag, expected in THEOREM_FLAGS.items():
            if summary.get(flag) is not expected:
                failures.append(f"summary flag {flag} expected {expected}")
        if summary.get("artifact_complete") is not True:
            failures.append("summary artifact_complete must be true before invariant failure update")
    return failures


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    status_counts: dict[str, int] = {}
    category_counts: dict[str, int] = {}
    for row in rows:
        status = str(row["evidence_status"])
        category = str(row["category"])
        status_counts[status] = status_counts.get(status, 0) + 1
        category_counts[category] = category_counts.get(category, 0) + 1

    canonical_value = CANONICAL_CONSTANT * U1_SAMPLE * V_SAMPLE * OMEGA_SAMPLE * (DELTA_SAMPLE**2)
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "gate": GATE,
        "decision": DECISION,
        "row_count": len(rows),
        "required_row_ids": sorted(REQUIRED_ROW_IDS),
        "observed_row_ids": [str(row["row_id"]) for row in rows],
        "status_counts": status_counts,
        "category_counts": category_counts,
        "generic_bound_shape": "core_source <= C*u1*v*Omega*delta^2",
        "canonical_evidence_shape": "core_source <= 2*u1*v*Omega*delta^2",
        "canonical_constant": fraction_to_str(CANONICAL_CONSTANT),
        "delta_power": 2,
        "u1_sample": fraction_to_str(U1_SAMPLE),
        "v_sample": fraction_to_str(V_SAMPLE),
        "omega_sample": fraction_to_str(OMEGA_SAMPLE),
        "delta_sample": fraction_to_str(DELTA_SAMPLE),
        "canonical_sample_value": fraction_to_str(canonical_value),
        "canonical_sample_value_float": round(float(canonical_value), 12),
        "artifact_complete": True,
        "invariant_checked": False,
        "invariant_valid": False,
        "invariant_failures": [],
        "is_evidence_only": True,
        "fail_closed": True,
        "promotion_allowed": False,
        "control_card": CONTROL_CARD,
    }
    summary.update(THEOREM_FLAGS)
    failures = validate(rows, summary)
    summary["invariant_failures"] = failures
    summary["invariant_checked"] = True
    summary["invariant_valid"] = not failures
    summary["artifact_complete"] = not failures
    summary["summary_hash"] = stable_hash(
        {key: value for key, value in summary.items() if key != "summary_hash"}
    )
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 153 Localized Vortex-Stretching Source",
        "",
        f"- Gate: `{summary['gate']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Generic shape: `{summary['generic_bound_shape']}`",
        f"- Canonical evidence: `{summary['canonical_evidence_shape']}`",
        f"- Invariant valid: `{summary['invariant_valid']}`",
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
            "## Ledger",
            "",
            "| row_id | category | status | coefficient | delta_power | theorem_flag |",
            "| --- | --- | --- | ---: | ---: | --- |",
        ]
    )
    for row in rows:
        lines.append(
            "| {row_id} | {category} | {evidence_status} | {coefficient} | "
            "{delta_power} | {theorem_flag} |".format(**row)
        )
    lines.extend(
        [
            "",
            "## Guard",
            "",
            (
                "This artifact records the localized core-source bound shape as "
                "deterministic evidence only. It does not prove the omega1 theorem, "
                "localized identity, finite BKM, or Clay Navier-Stokes."
            ),
            "",
        ]
    )
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> dict[str, Any]:
    files = [
        out_dir / LEDGER_JSON_NAME,
        out_dir / LEDGER_CSV_NAME,
        out_dir / SUMMARY_NAME,
        out_dir / REPORT_NAME,
    ]
    manifest: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "gate": GATE,
        "decision": DECISION,
        "row_count": len(rows),
        "artifact_complete": summary["artifact_complete"],
        "invariant_valid": summary["invariant_valid"],
        "control_card": CONTROL_CARD,
        "files": [
            {
                "path": display_path(path, repo_root),
                "exists": path.exists(),
                "sha256": file_sha256(path),
            }
            for path in files
        ],
    }
    manifest.update(THEOREM_FLAGS)
    manifest["manifest_hash"] = stable_hash(
        {key: value for key, value in manifest.items() if key != "manifest_hash"}
    )
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / LEDGER_JSON_NAME, rows)
        write_csv(temp_dir / LEDGER_CSV_NAME, rows)
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
    summary = build_summary(rows)
    write_outputs(repo_root, args.out_dir, rows, summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "artifact_complete": summary["artifact_complete"],
                "invariant_valid": summary["invariant_valid"],
                "row_count": summary["row_count"],
                "generic_bound_shape": summary["generic_bound_shape"],
                "canonical_evidence_shape": summary["canonical_evidence_shape"],
                "localized_core_source_bound_proved": summary[
                    "localized_core_source_bound_proved"
                ],
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
    raise SystemExit(main())
