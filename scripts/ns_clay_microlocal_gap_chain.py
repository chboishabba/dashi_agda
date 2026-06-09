#!/usr/bin/env python3
"""Emit the normalized Clay NS microlocal gap-chain ledger."""

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


CONTRACT = "ns_clay_microlocal_gap_chain"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

CURRENT_NS_STATE = {
    "SymmetricHouLuoBKMFinite": True,
    "SymmetricHouLuoBKMFinite_scope": "scoped_to_symmetric_hou_luo_axisymmetric_with_swirl_class",
    "full_clay_ns_solved": False,
}

FALSE_FLAGS = (
    "CriticalProfileExtraction",
    "MicrolocalVorticityDefectMeasure",
    "AlignmentConcentration",
    "SanniSigmaPDELift",
    "TopologicalStretchingLeakage",
    "WedgeCollapseExclusion",
    "PressureCommutatorGain",
    "NoPersistentPositiveNSCriticalResidual",
    "FullLocalDefectMonotonicity",
    "CKNBKMGeneralContinuation",
    "MechanismExhaustionForFullClayNS",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "GeneralSmoothFiniteEnergyNSRegularity",
    "ClayNavierStokesPromoted",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
)

SUPPORT_SPRINTS = (
    {
        "sprint": "157/158",
        "contracts": (
            "ns_sprint157_bkm_integral_estimate",
            "ns_sprint158_theorem_statement_closure",
            "ns_sprint158_assumption_scope_matrix",
        ),
        "support": (
            "Symmetric Hou-Luo BKM finiteness and theorem statement closure are recorded "
            "only inside the scoped symmetric class."
        ),
    },
    {
        "sprint": "159",
        "contracts": (
            "ns_sprint159_local_defect_monotonicity_gap",
            "ns_sprint159_critical_residual_gap",
        ),
        "support": "Local defect monotonicity and critical residual closure remain gap surfaces.",
    },
    {
        "sprint": "160",
        "contracts": (
            "ns_sprint160_ckn_bkm_bridge_gap",
            "ns_sprint160_profile_extraction_gap",
        ),
        "support": "General CKN/BKM continuation and profile extraction are not promoted to Clay closure.",
    },
    {
        "sprint": "162",
        "contracts": ("ns_sprint162_residual_positive_profile_fork",),
        "support": "Residual-positive ancient profile branch remains the fork that the microlocal chain must exhaust.",
    },
    {
        "sprint": "163",
        "contracts": (
            "ns_sprint163_critical_alignment_topological_exhaustion_target",
            "ns_sprint163_sigma_local_analysis_gap",
            "ns_sprint163_sanni_symbol_obstruction_source",
        ),
        "support": "Critical-alignment concentration and Sanni/Sigma obstruction are recorded as targets, not proofs.",
    },
    {
        "sprint": "164",
        "contracts": (
            "ns_sprint164_microlocal_alignment_bridge_target",
            "ns_sprint164_pressure_commutator_gain_target",
            "ns_sprint164_topological_stretching_leakage_target",
        ),
        "support": "Alignment bridge, pressure commutator gain, and stretching leakage remain open mechanism targets.",
    },
)

GAP_CHAIN = (
    {
        "chain_letter": "A",
        "gap_name": "critical profile extraction",
        "formal_surface": "CriticalProfileExtraction",
        "role": "extract a genuine critical ancient profile from a putative Clay blowup sequence",
        "required_closure": "compactness plus nontriviality at the Navier-Stokes critical scale",
        "in_repo_support": "Sprint160 profile extraction gap; Sprint162 residual-positive profile fork",
    },
    {
        "chain_letter": "B",
        "gap_name": "microlocal vorticity defect measure",
        "formal_surface": "MicrolocalVorticityDefectMeasure",
        "role": "lift the critical profile into a scale-local vorticity defect measure",
        "required_closure": "measure-valued localization that preserves vorticity stretching information",
        "in_repo_support": "Sprint163/164 microlocal alignment bridge targets",
    },
    {
        "chain_letter": "C",
        "gap_name": "alignment concentration",
        "formal_surface": "AlignmentConcentration",
        "role": "force residual-positive profiles to concentrate on alignment-degeneracy geometry",
        "required_closure": "positive critical residual implies concentration rather than dispersion",
        "in_repo_support": "Sprint163 critical-alignment topological exhaustion target",
    },
    {
        "chain_letter": "D",
        "gap_name": "Sanni/Sigma PDE lift",
        "formal_surface": "SanniSigmaPDELift",
        "role": "convert the Sanni/Sigma symbolic obstruction into a PDE-level exclusion",
        "required_closure": "symbolic Sigma obstruction becomes an analytic vorticity-stretching theorem",
        "in_repo_support": "Sprint163 Sanni symbol obstruction source and Sigma local analysis gap",
    },
    {
        "chain_letter": "E",
        "gap_name": "topological stretching leakage",
        "formal_surface": "TopologicalStretchingLeakage",
        "role": "prove that topological degeneracy leaks enough stretching to reduce the critical residual",
        "required_closure": "leakage estimate strong enough to defeat persistent critical concentration",
        "in_repo_support": "Sprint164 topological stretching leakage target",
    },
    {
        "chain_letter": "F",
        "gap_name": "wedge-collapse exclusion",
        "formal_surface": "WedgeCollapseExclusion",
        "role": "exclude collapse of the angular wedge that would hide stretching concentration",
        "required_closure": "no wedge-collapse escape channel near Sigma",
        "in_repo_support": "Sprint163 Sigma local analysis gap; Sprint164 alignment bridge target",
    },
    {
        "chain_letter": "G",
        "gap_name": "pressure commutator gain",
        "formal_surface": "PressureCommutatorGain",
        "role": "obtain an alpha-positive pressure-flux gain from angular/projector commutators",
        "required_closure": "critical Calderon-Zygmund pressure control improves to a subcritical gain",
        "in_repo_support": "Sprint164 pressure commutator gain target",
    },
    {
        "chain_letter": "H",
        "gap_name": "no persistent positive NSCriticalResidual",
        "formal_surface": "NoPersistentPositiveNSCriticalResidual",
        "role": "rule out residual-positive critical profiles across arbitrarily small scales",
        "required_closure": "NSCriticalResidual cannot remain positive along r_n -> 0",
        "in_repo_support": "Sprint162 residual-positive profile fork",
    },
    {
        "chain_letter": "I",
        "gap_name": "FullLocalDefectMonotonicity",
        "formal_surface": "FullLocalDefectMonotonicity",
        "role": "promote local defect decay to a full monotonicity principle for general profiles",
        "required_closure": "defect monotonicity applies outside the symmetric Hou-Luo route",
        "in_repo_support": "Sprint159 local defect monotonicity gap; Sprint161 defect monotonicity gap",
    },
    {
        "chain_letter": "J",
        "gap_name": "CKN/BKM general continuation",
        "formal_surface": "CKNBKMGeneralContinuation",
        "role": "bridge critical-scale defect control to general smooth finite-energy continuation",
        "required_closure": "CKN partial regularity plus BKM continuation covers arbitrary 3D data",
        "in_repo_support": "Sprint157/158 scoped BKM closure; Sprint160 general CKN/BKM bridge gap",
    },
    {
        "chain_letter": "K",
        "gap_name": "MechanismExhaustionForFullClayNS",
        "formal_surface": "MechanismExhaustionForFullClayNS",
        "role": "exhaust every blowup mechanism needed for the full Clay Navier-Stokes problem",
        "required_closure": "A-J all close without scope restriction or hidden escape channel",
        "in_repo_support": "Sprint157/158 scoped state plus Sprint159/160/162/163/164 open microlocal chain",
    },
)

CONTROL_CARD = {
    "O": "Worker 3 owns only the Clay NS microlocal gap-chain emitter and its output bundle.",
    "R": "Record the current scoped NS state and the exact A-K chain needed before any full Clay promotion.",
    "C": "One deterministic Python stdlib script emits normalized JSON, CSV, Markdown, and manifest artifacts.",
    "S": "The in-repo state supports SymmetricHouLuoBKMFinite only in scope; full_clay_ns_solved remains false.",
    "L": "Scoped BKM closure -> residual-positive profile fork -> microlocal/Sigma/pressure gaps -> no mechanism exhaustion.",
    "P": "Use this ledger as a fail-closed dependency chain, not as a proof or promotion certificate.",
    "G": "Validation requires A-K in exact order, Sprint157/158,159,160,162,163,164 support, scoped BKM true, and Clay false.",
    "F": "The remaining gap is full mechanism exhaustion for arbitrary smooth finite-energy 3D Navier-Stokes.",
}


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


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, spec in enumerate(GAP_CHAIN, start=1):
        row: dict[str, Any] = {
            "contract": CONTRACT,
            "chain_index": index,
            "chain_letter": spec["chain_letter"],
            "gap_name": spec["gap_name"],
            "formal_surface": spec["formal_surface"],
            "role": spec["role"],
            "required_closure": spec["required_closure"],
            "in_repo_support": spec["in_repo_support"],
            "current_status": "OPEN_FAIL_CLOSED",
            "closed": False,
            "target_recorded": True,
            "SymmetricHouLuoBKMFinite": CURRENT_NS_STATE["SymmetricHouLuoBKMFinite"],
            "SymmetricHouLuoBKMFinite_scope": CURRENT_NS_STATE["SymmetricHouLuoBKMFinite_scope"],
            **bool_flags(FALSE_FLAGS, False),
        }
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def build_support_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, spec in enumerate(SUPPORT_SPRINTS, start=1):
        row = {
            "contract": CONTRACT,
            "support_index": index,
            "support_sprint": spec["sprint"],
            "source_contracts": ";".join(spec["contracts"]),
            "support_statement": spec["support"],
            "support_recorded": True,
            "promotes_full_clay_ns": False,
        }
        row["support_hash"] = stable_hash({key: value for key, value in row.items() if key != "support_hash"})
        rows.append(row)
    return rows


def named_flags_have_value(record: dict[str, Any], names: tuple[str, ...], value: bool) -> bool:
    return all(record.get(name) is value for name in names)


def rows_named_flags_have_value(rows: list[dict[str, Any]], names: tuple[str, ...], value: bool) -> bool:
    return all(named_flags_have_value(row, names, value) for row in rows)


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_rows()
    support_rows = build_support_rows()
    expected_letters = [spec["chain_letter"] for spec in GAP_CHAIN]
    expected_names = [spec["gap_name"] for spec in GAP_CHAIN]
    actual_letters = [row["chain_letter"] for row in rows]
    actual_names = [row["gap_name"] for row in rows]
    support_sprints = [row["support_sprint"] for row in support_rows]
    required_support_present = support_sprints == ["157/158", "159", "160", "162", "163", "164"]

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "ClayNSMicrolocalGapChain",
        "decision": "microlocal_gap_chain_recorded_fail_closed",
        "current_ns_state": CURRENT_NS_STATE,
        "SymmetricHouLuoBKMFinite": True,
        "SymmetricHouLuoBKMFinite_scope": CURRENT_NS_STATE["SymmetricHouLuoBKMFinite_scope"],
        "full_clay_ns_solved": False,
        "gap_chain_rows": rows,
        "gap_chain_row_count": len(rows),
        "gap_chain_letters": actual_letters,
        "gap_chain_names": actual_names,
        "support_rows": support_rows,
        "support_row_count": len(support_rows),
        "support_sprints": support_sprints,
        "required_support_present": required_support_present,
        "exact_a_to_k_chain_present": actual_letters == expected_letters and actual_names == expected_names,
        "control_card": CONTROL_CARD,
        **bool_flags(FALSE_FLAGS, False),
    }
    summary["SymmetricHouLuoBKMFinite"] = True
    summary["row_false_flags_false"] = rows_named_flags_have_value(rows, FALSE_FLAGS, False)
    summary["summary_false_flags_false"] = named_flags_have_value(summary, FALSE_FLAGS, False)
    summary["validation_passed"] = (
        summary["SymmetricHouLuoBKMFinite"] is True
        and summary["SymmetricHouLuoBKMFinite_scope"] == CURRENT_NS_STATE["SymmetricHouLuoBKMFinite_scope"]
        and summary["full_clay_ns_solved"] is False
        and summary["gap_chain_row_count"] == 11
        and summary["exact_a_to_k_chain_present"]
        and required_support_present
        and summary["row_false_flags_false"]
        and summary["summary_false_flags_false"]
    )
    summary["summary_hash"] = stable_hash({key: value for key, value in summary.items() if key != "summary_hash"})
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# Clay NS Microlocal Gap Chain",
        "",
        f"- SymmetricHouLuoBKMFinite: `{summary['SymmetricHouLuoBKMFinite']}`",
        f"- Scope: `{summary['SymmetricHouLuoBKMFinite_scope']}`",
        f"- full_clay_ns_solved: `{summary['full_clay_ns_solved']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "## A-K Gap Chain",
        "",
        "| letter | gap | formal surface | status | in-repo support |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["gap_chain_rows"]:
        lines.append(
            "| {chain_letter} | {gap_name} | {formal_surface} | {current_status} | {in_repo_support} |".format(
                **row
            )
        )
    lines.extend(
        [
            "",
            "## Sprint Support",
            "",
            "| sprint | source contracts | support |",
            "| --- | --- | --- |",
        ]
    )
    for row in summary["support_rows"]:
        lines.append(f"| {row['support_sprint']} | {row['source_contracts']} | {row['support_statement']} |")
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


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
        write_json(temp_dir / ROWS_JSON_NAME, summary["gap_chain_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["gap_chain_rows"])
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
