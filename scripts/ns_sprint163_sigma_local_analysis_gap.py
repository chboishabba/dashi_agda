#!/usr/bin/env python3
"""Sprint 163 lane 4 Sigma local-analysis gap emitter."""

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


CONTRACT = "ns_sprint163_sigma_local_analysis_gap"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 163
LANE = 4
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

CLAY_FALSE_FLAGS = (
    "CriticalAlignmentTopologicalExhaustion",
    "BlowupImpliesSigmaConcentration",
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
    "ClayNavierStokesPromoted",
    "ClaySubmissionReady",
    "ClaySubmissionPromotionPacket",
    "promotion_allowed",
    "promotionAllowed",
)

REQUIRED_TRUE_FLAGS = (
    "AngularStrainSymbolDegeneracyOpen",
    "TransverseDegeneracyOpen",
    "PressureFluxSubcriticalGainOpen",
    "SigmaLocalAnalysisOpen",
    "SigmaConcentrationImpossibilityOpen",
)

REQUIRED_FALSE_FLAGS = (
    "SigmaConcentrationImpossible",
)

GAP_ROWS = (
    {
        "row_id": "G01",
        "gap": "angular_strain_symbol_degeneracy",
        "symbol_surface": "M(theta0)=0",
        "status": "OPEN",
        "precise_gap": (
            "Behavior near angular strain symbol degeneracy M(theta0)=0 is not "
            "resolved by the current local Sigma analysis."
        ),
        "needed_closure": (
            "A uniform expansion, normal form, or replacement coercivity estimate "
            "near zeros of the angular strain multiplier M."
        ),
        "flag": "AngularStrainSymbolDegeneracyOpen",
    },
    {
        "row_id": "G02",
        "gap": "transverse_degeneracy",
        "symbol_surface": "Sigma transverse directions",
        "status": "OPEN",
        "precise_gap": (
            "Transverse degeneracy to the Sigma locus is not excluded or absorbed "
            "by a local coercive estimate."
        ),
        "needed_closure": (
            "A transverse nondegeneracy lemma or a proof that transverse flat "
            "directions cannot sustain the critical residual."
        ),
        "flag": "TransverseDegeneracyOpen",
    },
    {
        "row_id": "G03",
        "gap": "pressure_flux_subcritical_gain_near_sigma",
        "symbol_surface": "PressureFlux near Sigma",
        "status": "OPEN",
        "precise_gap": (
            "Pressure flux subcritical gain near Sigma remains unproved; Calderon-"
            "Zygmund-scale control does not supply the needed positive gain."
        ),
        "needed_closure": (
            "A pressure-flux estimate near Sigma with an alpha-positive "
            "subcritical gain independent of the candidate profile."
        ),
        "flag": "PressureFluxSubcriticalGainOpen",
    },
    {
        "row_id": "G04",
        "gap": "impossibility_of_sigma_concentration",
        "symbol_surface": "Sigma concentration",
        "status": "OPEN_NOT_PROVED_IMPOSSIBLE",
        "precise_gap": (
            "Impossibility of Sigma concentration is still open; the artifact "
            "does not assert that Sigma concentration is impossible."
        ),
        "needed_closure": (
            "A concentration exclusion theorem ruling out persistent critical "
            "mass on Sigma under the full 3D Navier-Stokes dynamics."
        ),
        "flag": "SigmaConcentrationImpossibilityOpen",
    },
)

CONTROL_CARD = {
    "O": "Sprint163 lane 4 owns the Sigma local-analysis gap ledger.",
    "R": (
        "Record the precise remaining Sigma-local gaps without promoting a Clay "
        "Navier-Stokes result or concentration exclusion theorem."
    ),
    "C": "One stdlib Python emitter writes summary, rows JSON/CSV, Markdown, and manifest artifacts.",
    "S": (
        "The local Sigma surface is blocked by angular symbol zeros, transverse "
        "degeneracy, missing pressure-flux gain, and no concentration-impossibility proof."
    ),
    "L": (
        "M(theta0)=0 + transverse degeneracy + pressure flux at critical scale "
        "-> Sigma local analysis remains open."
    ),
    "P": "Use this artifact as a fail-closed gap record for Sprint163 lane 4.",
    "G": (
        "Validation passes only with PressureFluxSubcriticalGainOpen=true, "
        "SigmaLocalAnalysisOpen=true, SigmaConcentrationImpossible=false, and all Clay flags false."
    ),
    "F": "No full Clay NS, Sigma concentration impossibility, or subcritical pressure gain is promoted.",
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


def false_flags(names: tuple[str, ...]) -> dict[str, bool]:
    return {name: False for name in names}


def true_flags(names: tuple[str, ...]) -> dict[str, bool]:
    return {name: True for name in names}


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row in GAP_ROWS:
        item: dict[str, Any] = {
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "surface_name": "SigmaLocalAnalysisGap",
            "closed": False,
            "fail_closed": True,
            "external_boundary_only": True,
            **row,
            **true_flags(REQUIRED_TRUE_FLAGS),
            **false_flags(REQUIRED_FALSE_FLAGS),
            **false_flags(CLAY_FALSE_FLAGS),
        }
        item["row_hash"] = stable_hash({key: value for key, value in item.items() if key != "row_hash"})
        rows.append(item)
    return rows


def named_flags_have_value(record: dict[str, Any], names: tuple[str, ...], value: bool) -> bool:
    return all(record.get(name) is value for name in names)


def rows_named_flags_have_value(rows: list[dict[str, Any]], names: tuple[str, ...], value: bool) -> bool:
    return all(named_flags_have_value(row, names, value) for row in rows)


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_rows()
    row_gap_names = [row["gap"] for row in rows]
    required_gaps_present = row_gap_names == [row["gap"] for row in GAP_ROWS]

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "SigmaLocalAnalysisGap",
        "decision": "sigma_local_analysis_gap_fail_closed",
        "precise_gap": (
            "Behavior near angular strain symbol degeneracy M(theta0)=0, "
            "transverse degeneracy, pressure flux subcritical gain near Sigma, "
            "and impossibility of Sigma concentration all remain open."
        ),
        "gap_rows": rows,
        "row_count": len(rows),
        "gap_names": row_gap_names,
        "required_gaps_present": required_gaps_present,
        "control_card": CONTROL_CARD,
        **true_flags(REQUIRED_TRUE_FLAGS),
        **false_flags(REQUIRED_FALSE_FLAGS),
        **false_flags(CLAY_FALSE_FLAGS),
    }
    summary["row_required_true_flags_true"] = rows_named_flags_have_value(rows, REQUIRED_TRUE_FLAGS, True)
    summary["row_required_false_flags_false"] = rows_named_flags_have_value(rows, REQUIRED_FALSE_FLAGS, False)
    summary["row_authority_flags_false"] = rows_named_flags_have_value(rows, CLAY_FALSE_FLAGS, False)
    summary["summary_required_true_flags_true"] = named_flags_have_value(summary, REQUIRED_TRUE_FLAGS, True)
    summary["summary_required_false_flags_false"] = named_flags_have_value(summary, REQUIRED_FALSE_FLAGS, False)
    summary["summary_authority_flags_false"] = named_flags_have_value(summary, CLAY_FALSE_FLAGS, False)
    summary["validation_passed"] = (
        required_gaps_present
        and summary["PressureFluxSubcriticalGainOpen"] is True
        and summary["SigmaLocalAnalysisOpen"] is True
        and summary["SigmaConcentrationImpossible"] is False
        and summary["row_required_true_flags_true"]
        and summary["row_required_false_flags_false"]
        and summary["row_authority_flags_false"]
        and summary["summary_required_true_flags_true"]
        and summary["summary_required_false_flags_false"]
        and summary["summary_authority_flags_false"]
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
        "# Sprint 163 Sigma Local Analysis Gap",
        "",
        f"- Surface: `{summary['surface_name']}`",
        f"- Decision: `{summary['decision']}`",
        f"- PressureFluxSubcriticalGainOpen: `{summary['PressureFluxSubcriticalGainOpen']}`",
        f"- SigmaLocalAnalysisOpen: `{summary['SigmaLocalAnalysisOpen']}`",
        f"- SigmaConcentrationImpossible: `{summary['SigmaConcentrationImpossible']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "## Precise Gap",
        "",
        summary["precise_gap"],
        "",
        "| row | gap | symbol_surface | status | flag |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["gap_rows"]:
        lines.append(
            f"| {row['row_id']} | {row['gap']} | {row['symbol_surface']} | {row['status']} | {row['flag']} |"
        )
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
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": summary["generated_at"],
        "validation_passed": summary["validation_passed"],
        "files": {
            key: {"path": str(path), "exists": path.exists(), "sha256": file_sha256(path)}
            for key, path in files.items()
        },
    }
    manifest["manifest_hash"] = stable_hash({key: value for key, value in manifest.items() if key != "manifest_hash"})
    return manifest


def resolve_path(path: Path, repo_root: Path) -> Path:
    return path if path.is_absolute() else repo_root / path


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = resolve_path(args.out_dir, repo_root)
    summary = build_summary(repo_root, out_dir, args.generated_at)

    out_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f".{CONTRACT}.", dir=out_dir.parent) as temp_name:
        temp_dir = Path(temp_name)
        write_json(temp_dir / ROWS_JSON_NAME, summary["gap_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["gap_rows"])
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / MARKDOWN_NAME).write_text(render_markdown(summary), encoding="utf-8")
        write_json(temp_dir / MANIFEST_NAME, build_manifest(temp_dir, summary))
        if out_dir.exists():
            shutil.rmtree(out_dir)
        os.replace(temp_dir, out_dir)
        write_json(out_dir / MANIFEST_NAME, build_manifest(out_dir, summary))

    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "summary": str(out_dir / SUMMARY_NAME),
                "validation_passed": summary["validation_passed"],
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
