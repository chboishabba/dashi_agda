#!/usr/bin/env python3
"""Emit the NS projection/pressure commutator lemma-chain ledger.

This deterministic artifact records the corrected Navier-Stokes pressure
commutator route from StrainEigenprojectionSymbolLemma through
FullLocalDefectMonotonicity.  It is a fail-closed ledger: scalar Fourier
cutoffs are recorded as commuting with Riesz multipliers, so the only
nontrivial commutator target is the matrix/eigenbundle projection acting on the
vorticity-strain state space.
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
from pathlib import Path
from typing import Any


CONTRACT = "ns_projection_pressure_commutator_chain"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 166
WORKER = 3
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

FALSE_FLAGS = (
    "StrainEigenprojectionSymbolLemma",
    "ScalarCutoffPressureCommutatorNontrivial",
    "ScalarFourierCutoffRieszNoncommutation",
    "MatrixEigenbundleProjectionCommutatorClosed",
    "PressureCommutatorGain",
    "BranchSpreadClosure",
    "WedgeCollapseExclusion",
    "NoDegeneracyRidingPressureCoherentCascade",
    "PressureCoherentCascadeExclusion",
    "FullLocalDefectMonotonicity",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "GeneralSmoothFiniteEnergyNSRegularity",
    "ClayNavierStokesPromoted",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
)

COMMUTATION_CORRECTION = (
    "For scalar radial or dyadic Fourier cutoffs chi(D) and Riesz multipliers "
    "R_i R_j, both are scalar Fourier multipliers, hence [chi(D), R_i R_j] = 0. "
    "A claimed pressure commutator gain cannot come from scalar cutoff versus "
    "Riesz noncommutation."
)

NONTRIVIAL_COMMUTATOR = (
    "The nontrivial commutator must use a matrix/eigenbundle projection "
    "Pi_strain(omega,S;x,t,D) on the vorticity-strain state space.  Its symbol "
    "depends on the evolving strain eigenframe/eigenvalue gaps, so "
    "[Pi_strain, R_i R_j] and transport derivatives may carry curvature, gap, "
    "and bundle-connection error terms."
)

FORK_STATEMENT = (
    "branch-spread vs wedge-collapse fork: either the projected state spreads "
    "across strain branches and loses coherent pressure sign, or a collapsing "
    "wedge/eigenvalue-gap channel must be excluded by a separate no-degeneracy "
    "principle."
)

CONTROL_CARD = {
    "O": "Worker 3 owns only the NS projection/pressure commutator-chain emitter and output bundle.",
    "R": "Normalize the corrected lemma chain from StrainEigenprojectionSymbolLemma through FullLocalDefectMonotonicity.",
    "C": "One deterministic Python stdlib script emits JSON, CSV, Markdown, and manifest artifacts.",
    "S": "Scalar Fourier cutoffs commute with Riesz multipliers; the live gap is a matrix/eigenbundle commutator on vorticity-strain state space.",
    "L": "Strain symbol -> scalar commutation correction -> matrix eigenbundle commutator -> branch-spread/wedge-collapse fork -> no-degeneracy cascade target -> local defect monotonicity gap.",
    "P": "Use the ledger as a fail-closed dependency surface for later formalization, not as a closure certificate.",
    "G": "Validation requires exact ordered chain coverage, explicit scalar-cutoff correction, explicit matrix/eigenbundle commutator target, fork row, no-degeneracy row, and all closure flags false.",
    "F": "The remaining gap is proving NoDegeneracyRidingPressureCoherentCascade strongly enough to imply FullLocalDefectMonotonicity.",
}

LEMMA_CHAIN = (
    {
        "lemma_name": "StrainEigenprojectionSymbolLemma",
        "surface": "strain_eigenprojection_symbol",
        "role": "define the projected strain eigenframe symbol used to split vorticity-stretching states",
        "normalized_statement": "Pi_strain is a matrix-valued state-space projection tied to the local symmetric strain tensor S and vorticity omega.",
        "correction": "This is not a scalar Fourier cutoff and cannot be replaced by chi(D).",
        "requires": (),
        "yields": ("VorticityStrainStateSpaceProjection",),
        "status": "OPEN_FAIL_CLOSED",
    },
    {
        "lemma_name": "ScalarFourierCutoffRieszCommutationCorrection",
        "surface": "scalar_cutoff_pressure_commutator_correction",
        "role": "remove the false scalar pressure commutator source from the route",
        "normalized_statement": COMMUTATION_CORRECTION,
        "correction": "The scalar cutoff/Riesz commutator is zero at the Fourier multiplier level.",
        "requires": ("scalar Fourier multiplier calculus", "Riesz multiplier calculus"),
        "yields": ("ScalarCutoffPressureCommutatorNontrivialIsFalse",),
        "status": "CORRECTION_RECORDED_FAIL_CLOSED",
    },
    {
        "lemma_name": "VorticityStrainStateSpaceProjection",
        "surface": "vorticity_strain_state_space",
        "role": "place omega and S in the coupled state bundle where eigenprojections can vary",
        "normalized_statement": "The projection acts on a coupled vorticity-strain state, not merely on scalar frequency shells.",
        "correction": "State dependence is required before any nontrivial pressure commutator can exist.",
        "requires": ("StrainEigenprojectionSymbolLemma",),
        "yields": ("MatrixEigenbundleProjectionPressureCommutatorTarget",),
        "status": "OPEN_FAIL_CLOSED",
    },
    {
        "lemma_name": "MatrixEigenbundleProjectionPressureCommutatorTarget",
        "surface": "matrix_eigenbundle_pressure_commutator",
        "role": "isolate the actual commutator target with Riesz pressure multipliers",
        "normalized_statement": NONTRIVIAL_COMMUTATOR,
        "correction": "The commutator is bundle/eigenframe-driven, not scalar-cutoff-driven.",
        "requires": ("VorticityStrainStateSpaceProjection", "pressure Riesz representation"),
        "yields": ("PressureCommutatorGainTarget",),
        "status": "OPEN_FAIL_CLOSED",
    },
    {
        "lemma_name": "PressureCommutatorGainTarget",
        "surface": "pressure_commutator_gain",
        "role": "state the desired alpha-positive pressure-flux gain after matrix projection",
        "normalized_statement": "A gain would bound projected pressure flux by a subcritical bundle-curvature/error budget with positive slack.",
        "correction": "No gain is recorded as proved; this row only names the target inequality.",
        "requires": ("MatrixEigenbundleProjectionPressureCommutatorTarget",),
        "yields": ("BranchSpreadVsWedgeCollapseFork",),
        "status": "OPEN_FAIL_CLOSED",
    },
    {
        "lemma_name": "BranchSpreadVsWedgeCollapseFork",
        "surface": "branch_spread_vs_wedge_collapse",
        "role": "split the escape analysis after the projected pressure commutator target",
        "normalized_statement": FORK_STATEMENT,
        "correction": "Both branches remain open; neither branch supplies monotonicity closure.",
        "requires": ("PressureCommutatorGainTarget",),
        "yields": ("NoDegeneracyRidingPressureCoherentCascade",),
        "status": "FORK_OPEN_FAIL_CLOSED",
    },
    {
        "lemma_name": "NoDegeneracyRidingPressureCoherentCascade",
        "surface": "no_degeneracy_riding_pressure_coherent_cascade",
        "role": "block a coherent cascade that rides eigenvalue degeneracy while preserving pressure sign",
        "normalized_statement": "A pressure-coherent cascade cannot persist by tracking collapsing strain eigenvalue gaps or a narrowing angular wedge.",
        "correction": "This no-degeneracy principle is required but not proved.",
        "requires": ("BranchSpreadVsWedgeCollapseFork", "matrix eigenbundle gap control"),
        "yields": ("PressureCoherentCascadeExclusion",),
        "status": "OPEN_FAIL_CLOSED",
    },
    {
        "lemma_name": "PressureCoherentCascadeExclusion",
        "surface": "pressure_coherent_cascade_exclusion",
        "role": "turn no-degeneracy into exclusion of persistent positive pressure-stretching residual",
        "normalized_statement": "Projected pressure coherence must fail across arbitrarily small scales before local defect monotonicity can close.",
        "correction": "The exclusion is downstream of the no-degeneracy target and remains open.",
        "requires": ("NoDegeneracyRidingPressureCoherentCascade",),
        "yields": ("FullLocalDefectMonotonicity",),
        "status": "OPEN_FAIL_CLOSED",
    },
    {
        "lemma_name": "FullLocalDefectMonotonicity",
        "surface": "full_local_defect_monotonicity",
        "role": "promote pressure-cascade exclusion into a general local defect monotonicity principle",
        "normalized_statement": "Local defect must decay monotonically for general 3D Navier-Stokes profiles after all projected pressure escape channels are exhausted.",
        "correction": "This is the terminal open target of the chain, not an established theorem.",
        "requires": ("PressureCoherentCascadeExclusion",),
        "yields": (),
        "status": "OPEN_FAIL_CLOSED",
    },
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", "--output-dir", dest="out_dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--generated-at", default=DEFAULT_GENERATED_AT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def bool_flags(names: tuple[str, ...], value: bool) -> dict[str, bool]:
    return {name: value for name in names}


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rows_named_flags_have_value(rows: list[dict[str, Any]], names: tuple[str, ...], value: bool) -> bool:
    return all(all(row.get(name) is value for name in names) for row in rows)


def named_flags_have_value(record: dict[str, Any], names: tuple[str, ...], value: bool) -> bool:
    return all(record.get(name) is value for name in names)


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, spec in enumerate(LEMMA_CHAIN, start=1):
        next_lemma = LEMMA_CHAIN[index]["lemma_name"] if index < len(LEMMA_CHAIN) else None
        row: dict[str, Any] = {
            "sprint": SPRINT,
            "worker": WORKER,
            "contract": CONTRACT,
            "chain_index": index,
            "lemma_name": spec["lemma_name"],
            "surface": spec["surface"],
            "role": spec["role"],
            "normalized_statement": spec["normalized_statement"],
            "correction": spec["correction"],
            "requires": list(spec["requires"]),
            "yields": list(spec["yields"]),
            "next_lemma": next_lemma,
            "status": spec["status"],
            "scalar_fourier_cutoffs_commute_with_riesz": True,
            "scalar_cutoff_riesz_commutator_zero": True,
            "nontrivial_commutator_requires_matrix_eigenbundle_projection": True,
            "state_space": "vorticity-strain",
            "fork_surface_included": spec["lemma_name"] == "BranchSpreadVsWedgeCollapseFork",
            "no_degeneracy_surface_included": spec["lemma_name"] == "NoDegeneracyRidingPressureCoherentCascade",
            "target_recorded": True,
            "closed": False,
            "proved": False,
            "proven": False,
            "claim_closed": False,
            "claim_proved": False,
            "claim_proven": False,
            **bool_flags(FALSE_FLAGS, False),
        }
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_rows()
    expected_names = [spec["lemma_name"] for spec in LEMMA_CHAIN]
    actual_names = [row["lemma_name"] for row in rows]
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "worker": WORKER,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "NSProjectionPressureCommutatorChain",
        "decision": "projection_pressure_commutator_chain_recorded_fail_closed",
        "lemma_chain_rows": rows,
        "lemma_chain_row_count": len(rows),
        "lemma_chain_names": actual_names,
        "exact_chain_present": actual_names == expected_names,
        "starts_at": actual_names[0] if actual_names else None,
        "ends_at": actual_names[-1] if actual_names else None,
        "commutation_correction": COMMUTATION_CORRECTION,
        "scalar_cutoff_correction": COMMUTATION_CORRECTION,
        "nontrivial_commutator": NONTRIVIAL_COMMUTATOR,
        "fork_statement": FORK_STATEMENT,
        "scalar_fourier_cutoffs_commute_with_riesz": True,
        "scalar_cutoff_riesz_commutator_zero": True,
        "nontrivial_commutator_requires_matrix_eigenbundle_projection": True,
        "matrix_eigenbundle_projection_state_space": "vorticity-strain",
        "branch_spread_vs_wedge_collapse_fork_included": "BranchSpreadVsWedgeCollapseFork" in actual_names,
        "NoDegeneracyRidingPressureCoherentCascade_included": (
            "NoDegeneracyRidingPressureCoherentCascade" in actual_names
        ),
        "control_card": CONTROL_CARD,
        **bool_flags(FALSE_FLAGS, False),
    }
    summary["row_false_flags_false"] = rows_named_flags_have_value(rows, FALSE_FLAGS, False)
    summary["summary_false_flags_false"] = named_flags_have_value(summary, FALSE_FLAGS, False)
    summary["validation_passed"] = (
        summary["exact_chain_present"]
        and summary["starts_at"] == "StrainEigenprojectionSymbolLemma"
        and summary["ends_at"] == "FullLocalDefectMonotonicity"
        and summary["scalar_fourier_cutoffs_commute_with_riesz"] is True
        and summary["scalar_cutoff_riesz_commutator_zero"] is True
        and summary["nontrivial_commutator_requires_matrix_eigenbundle_projection"] is True
        and summary["branch_spread_vs_wedge_collapse_fork_included"] is True
        and summary["NoDegeneracyRidingPressureCoherentCascade_included"] is True
        and summary["row_false_flags_false"] is True
        and summary["summary_false_flags_false"] is True
    )
    summary["summary_hash"] = stable_hash({key: value for key, value in summary.items() if key != "summary_hash"})
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def csv_value(value: Any) -> Any:
    if isinstance(value, (list, dict)):
        return json.dumps(value, sort_keys=True, separators=(",", ":"))
    return value


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow({key: csv_value(value) for key, value in row.items()})


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# NS Projection Pressure Commutator Chain",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        f"- Starts at: `{summary['starts_at']}`",
        f"- Ends at: `{summary['ends_at']}`",
        f"- Scalar cutoff/Riesz commutator zero: `{summary['scalar_cutoff_riesz_commutator_zero']}`",
        f"- Matrix/eigenbundle state space: `{summary['matrix_eigenbundle_projection_state_space']}`",
        f"- Closure flags false: `{summary['summary_false_flags_false'] and summary['row_false_flags_false']}`",
        "",
        "## Correction",
        "",
        summary["commutation_correction"],
        "",
        "## Nontrivial Commutator Target",
        "",
        summary["nontrivial_commutator"],
        "",
        "## Lemma Chain",
        "",
        "| index | lemma | status | role | correction |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["lemma_chain_rows"]:
        lines.append(
            "| {chain_index} | {lemma_name} | {status} | {role} | {correction} |".format(**row)
        )
    lines.extend(["", "## Fork", "", summary["fork_statement"], "", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / SUMMARY_NAME,
        "rows_json": out_dir / ROWS_JSON_NAME,
        "rows_csv": out_dir / ROWS_CSV_NAME,
        "markdown": out_dir / MARKDOWN_NAME,
        "manifest": out_dir / MANIFEST_NAME,
    }
    manifest = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "worker": WORKER,
        "generated_at": summary["generated_at"],
        "validation_passed": summary["validation_passed"],
        "files": {
            key: {
                "path": str(path),
                "exists": path.exists(),
                "sha256": file_sha256(path),
            }
            for key, path in files.items()
        },
    }
    manifest["manifest_hash"] = stable_hash({key: value for key, value in manifest.items() if key != "manifest_hash"})
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / ROWS_JSON_NAME, summary["lemma_chain_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["lemma_chain_rows"])
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / MARKDOWN_NAME).write_text(render_markdown(summary), encoding="utf-8")
        write_json(temp_dir / MANIFEST_NAME, build_manifest(temp_dir, summary))
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        write_json(final_out / MANIFEST_NAME, build_manifest(final_out, summary))
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    summary = build_summary(repo_root=repo_root, out_dir=out_dir, generated_at=args.generated_at)
    write_outputs(repo_root=repo_root, out_dir=out_dir, summary=summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "out_dir": str(out_dir),
                "validation_passed": summary["validation_passed"],
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
