#!/usr/bin/env python3
"""Sprint 161 defect-monotonicity gap emitter.

This stdlib-only emitter records the local defect energy D_r monotonicity
surface.  It is intentionally fail-closed: symmetric Hou-Luo machinery supports
scoped axisymmetric-with-swirl transport/continuation statements, but the
sign, pressure, and alignment hypotheses needed for a general 3D monotonicity
theorem are not closed here.
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


CONTRACT = "ns_sprint161_defect_monotonicity_gap"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"
MANIFEST_NAME = CONTRACT + "_manifest.json"

SPRINT = 161
LANE = 3
PROGRAM = "DefectMonotonicityGapLedger"
DECISION = "fail_closed_general_3d_defect_monotonicity_gap"

LOCAL_DEFECT_ENERGY = (
    "D_r(t,x0) = normalized localized defect/enstrophy-energy excess on a "
    "parabolic ball Q_r(t,x0), compared against the scale-compatible "
    "dissipation and flux budget."
)

CONTROL_CARD = {
    "O": "Lane 3 owns the Sprint161 defect-monotonicity gap emitter.",
    "R": (
        "Normalize the D_r monotonicity obstruction: local defect energy, "
        "needed sign/pressure/alignment hypotheses, symmetric support, and "
        "the remaining general 3D gap."
    ),
    "C": "One Python stdlib script writes JSON, CSV, Markdown, and manifest artifacts.",
    "S": (
        "Sprint157-160 isolate a symmetric Hou-Luo publication packet while "
        "keeping full Clay and mechanism-exhaustion promotion false."
    ),
    "L": (
        "D_r monotonicity would need a closed local sign ledger, pressure "
        "control, and alignment persistence outside the symmetric class."
    ),
    "P": "Use this as a normalized obstruction ledger, not as a monotonicity theorem.",
    "G": (
        "Symmetric machinery can support scoped axisymmetric-with-swirl rows; "
        "general smooth finite-energy 3D Navier-Stokes remains guarded false."
    ),
    "F": (
        "General 3D remains open because nonlocal pressure, vortex-stretching "
        "alignment, and sign-definite defect flux are not closed without the "
        "symmetry hypotheses."
    ),
}

FULL_CLAY_FALSE_FLAGS = (
    "MechanismExhaustionForFullClayNS",
    "FullClayMechanismExhaustion",
    "GeneralSmoothFiniteEnergyNSRegularity",
    "fullClay",
    "full_clay",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "fullNavierStokesSolutionConstructed",
    "clay_navier_stokes_promoted",
    "clayNavierStokesPromoted",
    "promotion_allowed",
    "promotionAllowed",
    "ClaySubmissionReady",
    "ClaySubmissionPromotionPacket",
)


@dataclass(frozen=True)
class DefectRow:
    row_id: str
    category: str
    normalized_object: str
    status: str
    closed: bool
    fail_closed: bool
    local_defect_energy_D_r: str
    needed_sign_hypothesis: str
    needed_pressure_hypothesis: str
    needed_alignment_hypothesis: str
    symmetric_machinery_support: str
    general_3d_gap: str
    support_artifacts: tuple[str, ...]
    promotion_allowed: bool = False

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row.update(
            {
                "sprint": SPRINT,
                "lane": LANE,
                "contract": CONTRACT,
                "program": PROGRAM,
                "decision": DECISION,
                "DefectMonotonicityForGeneral3D": False,
                "defect_monotonicity_for_general_3d": False,
                "SymmetricHouLuoMachinerySupportsScopedRows": True,
                "symmetric_hou_luo_machinery_supports_scoped_rows": True,
                "General3DDefectMonotonicityGapOpen": True,
                "general_3d_defect_monotonicity_gap_open": True,
                **full_clay_false_flags(),
            }
        )
        row["support_artifacts"] = list(self.support_artifacts)
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


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def full_clay_false_flags() -> dict[str, bool]:
    return {flag: False for flag in FULL_CLAY_FALSE_FLAGS}


def build_rows() -> list[dict[str, Any]]:
    specs = [
        DefectRow(
            row_id="local_defect_energy_D_r",
            category="normalized_object",
            normalized_object="LocalDefectEnergyD_r",
            status="DEFINED_LEDGER_OBJECT_FAIL_CLOSED",
            closed=False,
            fail_closed=True,
            local_defect_energy_D_r=LOCAL_DEFECT_ENERGY,
            needed_sign_hypothesis=(
                "A sign-definite localized flux/source inequality for D_r "
                "under scale-compatible cutoff errors."
            ),
            needed_pressure_hypothesis=(
                "Pressure decomposition with nonlocal tail controlled at the "
                "same scale as the localized defect budget."
            ),
            needed_alignment_hypothesis=(
                "Persistence of vortex-stretching alignment that prevents "
                "uncontrolled positive defect production."
            ),
            symmetric_machinery_support=(
                "Symmetric Hou-Luo rows give scoped continuation support inside "
                "axisymmetric-with-swirl and reflection-symmetric hypotheses."
            ),
            general_3d_gap=(
                "The D_r object is normalized, but no monotone quantity is "
                "proved for arbitrary smooth finite-energy 3D data."
            ),
            support_artifacts=(
                "outputs/ns_sprint160_symmetric_publication_isolation/ns_sprint160_symmetric_publication_isolation_summary.json",
            ),
        ),
        DefectRow(
            row_id="sign_hypothesis",
            category="needed_hypothesis",
            normalized_object="SignDefiniteDefectFlux",
            status="OPEN_FAIL_CLOSED",
            closed=False,
            fail_closed=True,
            local_defect_energy_D_r=LOCAL_DEFECT_ENERGY,
            needed_sign_hypothesis=(
                "For all admissible cutoffs and centers, the combined local "
                "transport, vortex-stretching, and commutator remainder must "
                "be nonpositive after dissipation is charged."
            ),
            needed_pressure_hypothesis="Pressure must not reintroduce positive unbudgeted flux.",
            needed_alignment_hypothesis="Alignment errors must be sign-compatible with the D_r budget.",
            symmetric_machinery_support=(
                "Symmetry reduces selected sign channels in the Hou-Luo packet, "
                "but only after imposing axisymmetry/reflection structure."
            ),
            general_3d_gap=(
                "General 3D vortex stretching has no sign in the current ledger, "
                "so D_r monotonicity cannot be promoted."
            ),
            support_artifacts=(
                "outputs/ns_sprint139_commutator_sign_route/ns_sprint139_commutator_sign_route_summary.json",
                "outputs/ns_sprint142_kernel_sign_stress_sampler/ns_sprint142_kernel_sign_stress_sampler_summary.json",
            ),
        ),
        DefectRow(
            row_id="pressure_hypothesis",
            category="needed_hypothesis",
            normalized_object="PressureTailAndLocalProjectionControl",
            status="OPEN_FAIL_CLOSED",
            closed=False,
            fail_closed=True,
            local_defect_energy_D_r=LOCAL_DEFECT_ENERGY,
            needed_sign_hypothesis="The pressure contribution must be compatible with the sign ledger.",
            needed_pressure_hypothesis=(
                "A local/nonlocal pressure split must bound pressure tails, "
                "harmonic leakage, and cutoff-gradient terms without losing "
                "critical scaling."
            ),
            needed_alignment_hypothesis="Alignment rows must absorb pressure-coupled stretching terms.",
            symmetric_machinery_support=(
                "Axisymmetric reductions help localize the symmetric packet, "
                "but they do not supply a universal 3D pressure monotonicity rule."
            ),
            general_3d_gap=(
                "Pressure is nonlocal and can couple remote energy into Q_r; "
                "the current symmetric machinery does not exhaust that channel."
            ),
            support_artifacts=(
                "outputs/ns_sprint145_envelope_constant_budget/ns_sprint145_envelope_constant_budget_summary.json",
                "outputs/ns_sprint155_model_validity_assembler/ns_sprint155_model_validity_assembler_summary.json",
            ),
        ),
        DefectRow(
            row_id="alignment_hypothesis",
            category="needed_hypothesis",
            normalized_object="VortexStretchingAlignmentPersistence",
            status="OPEN_FAIL_CLOSED",
            closed=False,
            fail_closed=True,
            local_defect_energy_D_r=LOCAL_DEFECT_ENERGY,
            needed_sign_hypothesis="Alignment must force the stretching source into the nonpositive ledger.",
            needed_pressure_hypothesis="Pressure must preserve, not destroy, the alignment budget.",
            needed_alignment_hypothesis=(
                "A stable cone/correlation condition must persist across scales "
                "and times for arbitrary 3D vorticity geometry."
            ),
            symmetric_machinery_support=(
                "The symmetric route records alignment/correlation support only "
                "inside the Hou-Luo geometric class."
            ),
            general_3d_gap=(
                "No current artifact rules out adverse 3D vorticity geometry or "
                "loss of alignment under the full flow."
            ),
            support_artifacts=(
                "outputs/ns_sprint118_alignment_sign_sampler/ns_sprint118_alignment_sign_sampler_summary.json",
                "outputs/ns_sprint118_geometric_correlation_audit/ns_sprint118_geometric_correlation_audit_summary.json",
            ),
        ),
        DefectRow(
            row_id="symmetric_machinery_support",
            category="support_boundary",
            normalized_object="SymmetricHouLuoScopedSupport",
            status="SCOPED_SUPPORT_ONLY",
            closed=True,
            fail_closed=False,
            local_defect_energy_D_r=LOCAL_DEFECT_ENERGY,
            needed_sign_hypothesis="Scoped sign reductions are available only under symmetric assumptions.",
            needed_pressure_hypothesis="Scoped pressure handling is tied to the symmetric Hou-Luo packet.",
            needed_alignment_hypothesis="Scoped alignment support is tied to axisymmetric/reflection structure.",
            symmetric_machinery_support=(
                "Sprint157-160 support a publication-isolated symmetric "
                "regularity-class packet with full Clay flags false."
            ),
            general_3d_gap=(
                "Scoped support is not mechanism exhaustion for full 3D "
                "Navier-Stokes."
            ),
            support_artifacts=(
                "outputs/ns_sprint157_bkm_integral_estimate/ns_sprint157_bkm_integral_estimate_summary.json",
                "outputs/ns_sprint158_theorem_statement_closure/ns_sprint158_theorem_statement_closure_summary.json",
                "outputs/ns_sprint160_symmetric_publication_isolation/ns_sprint160_symmetric_publication_isolation_summary.json",
            ),
        ),
        DefectRow(
            row_id="general_3d_open_gap",
            category="open_gap",
            normalized_object="General3DDefectMonotonicity",
            status="OPEN_FAIL_CLOSED",
            closed=False,
            fail_closed=True,
            local_defect_energy_D_r=LOCAL_DEFECT_ENERGY,
            needed_sign_hypothesis="Global-in-class sign-definite D_r inequality remains absent.",
            needed_pressure_hypothesis="General nonlocal pressure closure remains absent.",
            needed_alignment_hypothesis="General 3D alignment persistence remains absent.",
            symmetric_machinery_support=(
                "Symmetric machinery supports the restricted Hou-Luo class and "
                "guards against overclaiming."
            ),
            general_3d_gap=(
                "Without the sign, pressure, and alignment hypotheses, D_r is "
                "a diagnostic ledger object rather than a monotone quantity for "
                "arbitrary 3D data."
            ),
            support_artifacts=(
                "outputs/ns_sprint159_mechanism_exhaustion_gap/ns_sprint159_mechanism_exhaustion_gap_summary.json",
                "outputs/ns_sprint160_symmetric_publication_isolation/ns_sprint160_symmetric_publication_isolation_summary.json",
            ),
        ),
    ]
    return [spec.as_row() for spec in specs]


def full_clay_flags_false(records: list[dict[str, Any]] | dict[str, Any]) -> bool:
    if isinstance(records, dict):
        return all(records.get(flag) is False for flag in FULL_CLAY_FALSE_FLAGS)
    return all(all(record.get(flag) is False for flag in FULL_CLAY_FALSE_FLAGS) for record in records)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = {row["row_id"] for row in rows}
    expected_row_ids = {
        "local_defect_energy_D_r",
        "sign_hypothesis",
        "pressure_hypothesis",
        "alignment_hypothesis",
        "symmetric_machinery_support",
        "general_3d_open_gap",
    }
    open_gap_rows = [row for row in rows if row["status"].endswith("FAIL_CLOSED")]
    support_rows = [row for row in rows if row["category"] == "support_boundary" and row["closed"]]
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "row_count": len(rows),
        "expected_rows_present": row_ids == expected_row_ids,
        "local_defect_energy_D_r": LOCAL_DEFECT_ENERGY,
        "sign_hypothesis_closed": False,
        "pressure_hypothesis_closed": False,
        "alignment_hypothesis_closed": False,
        "symmetric_machinery_supports_scoped_rows": len(support_rows) == 1,
        "general_3d_defect_monotonicity_gap_open": True,
        "DefectMonotonicityForGeneral3D": False,
        "defect_monotonicity_for_general_3d": False,
        "General3DDefectMonotonicityGapOpen": True,
        "SymmetricHouLuoMachinerySupportsScopedRows": len(support_rows) == 1,
        "open_fail_closed_row_count": len(open_gap_rows),
        "fail_closed": True,
        "fail_closed_summary_flags": {
            "sign_hypothesis_missing": True,
            "pressure_hypothesis_missing": True,
            "alignment_hypothesis_missing": True,
            "general_3d_monotonicity_unproved": True,
            "symmetric_support_is_scoped_only": True,
            "full_clay_promotion_blocked": True,
        },
        "why_general_3d_remains_open": (
            "The current symmetric machinery does not provide a sign-definite "
            "D_r inequality, a critical-scale nonlocal pressure closure, or "
            "persistent vortex-stretching alignment for arbitrary smooth "
            "finite-energy 3D data."
        ),
        "control_card": CONTROL_CARD,
        **full_clay_false_flags(),
    }
    summary["row_full_clay_flags_false"] = full_clay_flags_false(rows)
    summary["summary_full_clay_flags_false"] = full_clay_flags_false(summary)
    summary["validation_passed"] = validate_summary_shape(summary, rows)
    summary["summary_hash"] = stable_hash({k: v for k, v in summary.items() if k != "summary_hash"})
    return summary


def validate_summary_shape(summary: dict[str, Any], rows: list[dict[str, Any]]) -> bool:
    flags = summary["fail_closed_summary_flags"]
    return (
        summary["expected_rows_present"]
        and summary["row_count"] == 6
        and summary["open_fail_closed_row_count"] == 5
        and summary["fail_closed"] is True
        and summary["sign_hypothesis_closed"] is False
        and summary["pressure_hypothesis_closed"] is False
        and summary["alignment_hypothesis_closed"] is False
        and summary["symmetric_machinery_supports_scoped_rows"] is True
        and summary["general_3d_defect_monotonicity_gap_open"] is True
        and summary["DefectMonotonicityForGeneral3D"] is False
        and summary["row_full_clay_flags_false"] is True
        and summary["summary_full_clay_flags_false"] is True
        and all(flags.values())
        and all(row["promotion_allowed"] is False for row in rows)
        and all(row["General3DDefectMonotonicityGapOpen"] is True for row in rows)
        and all(row["DefectMonotonicityForGeneral3D"] is False for row in rows)
    )


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 161 Defect Monotonicity Gap",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Fail closed: `{summary['fail_closed']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        f"- DefectMonotonicityForGeneral3D: `{summary['DefectMonotonicityForGeneral3D']}`",
        f"- SymmetricHouLuoMachinerySupportsScopedRows: `{summary['SymmetricHouLuoMachinerySupportsScopedRows']}`",
        f"- General3DDefectMonotonicityGapOpen: `{summary['General3DDefectMonotonicityGapOpen']}`",
        "",
        "## Local Defect Energy",
        "",
        LOCAL_DEFECT_ENERGY,
        "",
        "## Rows",
        "",
        "| row_id | category | status | closed | sign | pressure | alignment | general_3d_gap |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(
            "| {row_id} | {category} | {status} | {closed} | {sign} | {pressure} | {alignment} | {gap} |".format(
                row_id=row["row_id"],
                category=row["category"],
                status=row["status"],
                closed=row["closed"],
                sign=row["needed_sign_hypothesis"],
                pressure=row["needed_pressure_hypothesis"],
                alignment=row["needed_alignment_hypothesis"],
                gap=row["general_3d_gap"],
            )
        )
    lines.extend(
        [
            "",
            "## Symmetric Machinery Boundary",
            "",
            (
                "The symmetric Hou-Luo packet supports scoped axisymmetric-with-swirl "
                "regularity rows. It does not close the sign, pressure, or "
                "alignment hypotheses needed for arbitrary 3D D_r monotonicity."
            ),
            "",
            "## Fail-Closed Summary Flags",
            "",
        ]
    )
    for key, value in summary["fail_closed_summary_flags"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / SUMMARY_NAME,
        "rows_json": out_dir / ROWS_JSON_NAME,
        "rows_csv": out_dir / ROWS_CSV_NAME,
        "markdown": out_dir / REPORT_NAME,
        "manifest": out_dir / MANIFEST_NAME,
    }
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "decision": DECISION,
        "validation_passed": summary["validation_passed"],
        "fail_closed": summary["fail_closed"],
        "files": {
            key: {
                "path": str(path),
                "exists": path.exists(),
                "sha256": file_sha256(path),
            }
            for key, path in files.items()
        },
    }
    manifest["manifest_hash"] = stable_hash({k: v for k, v in manifest.items() if k != "manifest_hash"})
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> Path:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / ROWS_JSON_NAME, rows)
        write_csv(temp_dir / ROWS_CSV_NAME, rows)
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / REPORT_NAME).write_text(render_markdown(summary, rows), encoding="utf-8")
        write_json(temp_dir / MANIFEST_NAME, build_manifest(temp_dir, summary))
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        write_json(final_out / MANIFEST_NAME, build_manifest(final_out, summary))
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise
    return final_out


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    rows = build_rows()
    summary = build_summary(rows)
    out_dir = write_outputs(repo_root, args.out_dir, rows, summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "decision": DECISION,
                "fail_closed": summary["fail_closed"],
                "validation_passed": summary["validation_passed"],
                "out_dir": str(out_dir),
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
