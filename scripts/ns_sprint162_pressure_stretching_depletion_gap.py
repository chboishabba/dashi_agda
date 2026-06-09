#!/usr/bin/env python3
"""Sprint 162 pressure/stretching depletion gap emitter."""

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


CONTRACT = "ns_sprint162_pressure_stretching_depletion_gap"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 162
LANE = 2
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

FALSE_FLAGS = (
    "PressureStretchingDepletionLemma",
    "NoPersistentPositiveNSCriticalResidual",
    "MechanismExhaustionForFullClayNS",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "fullNavierStokesSolutionConstructed",
    "clayNavierStokesPromoted",
    "promotion_allowed",
)

VARIABLE_ROWS = (
    {
        "symbol": "u",
        "name": "velocity",
        "role": "3D incompressible Navier-Stokes velocity field",
        "scale_status": "critical_input",
    },
    {
        "symbol": "p",
        "name": "pressure",
        "role": "nonlocal Riesz-transform pressure p = R_i R_j(u_i u_j)",
        "scale_status": "critical_not_depleting",
    },
    {
        "symbol": "omega",
        "name": "vorticity",
        "role": "curl u, source carrier for vortex stretching",
        "scale_status": "critical_concentration_carrier",
    },
    {
        "symbol": "S",
        "name": "strain tensor",
        "role": "symmetric part of grad u controlling omega dot S omega",
        "scale_status": "alignment_sensitive",
    },
    {
        "symbol": "e_max",
        "name": "maximal strain eigenvector",
        "role": "direction of strongest stretching",
        "scale_status": "alignment_sensitive",
    },
    {
        "symbol": "A_r",
        "name": "alignment defect",
        "role": "localized integral of |omega|^2 positive alignment with e_max(S)",
        "scale_status": "missing_depletion",
    },
    {
        "symbol": "D_r",
        "name": "local defect",
        "role": "scale-critical local |u|^3 + |p|^(3/2) defect",
        "scale_status": "critical_quantity",
    },
    {
        "symbol": "Phi_r",
        "name": "pressure flux",
        "role": "localized pressure flux integral p u dot grad phi_r",
        "scale_status": "critical_not_depleting",
    },
    {
        "symbol": "E_r",
        "name": "dissipation",
        "role": "localized viscous control term",
        "scale_status": "absorbing_term_if_gain_exists",
    },
)

CONTROL_CARD = {
    "O": "Sprint162 lane 2 owns the pressure/stretching depletion gap ledger.",
    "R": "Name the exact missing alpha-positive estimate blocking local defect monotonicity.",
    "C": "One deterministic JSON summary with variables, invariants, and false theorem flags.",
    "S": "Calderon-Zygmund controls pressure at the critical scale but supplies no alpha gain.",
    "L": "critical control -> alpha-zero wall -> alpha-positive depletion lemma -> Clay route if supplied.",
    "P": "Keep the lemma false while preserving a concrete theorem target.",
    "G": "Validation requires all Clay and depletion flags false.",
    "F": "The missing object is a pressure/stretching depletion inequality with alpha > 0.",
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


def false_flags() -> dict[str, bool]:
    return {name: False for name in FALSE_FLAGS}


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    variables = []
    for index, row in enumerate(VARIABLE_ROWS, start=1):
        item = {
            "row_id": f"V{index:02d}",
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            **row,
            "included_in_missing_estimate": True,
        }
        item["row_hash"] = stable_hash(item)
        variables.append(item)

    missing_estimate = {
        "name": "PressureStretchingDepletionLemma",
        "informal_statement": (
            "PressureFlux_r + StretchingAlignment_r <= epsilon Dissipation_r "
            "+ C_epsilon D_r^(1+alpha) for some alpha > 0 independent of the solution."
        ),
        "alpha_required": True,
        "alpha_value_known": False,
        "alpha_positive_established": False,
        "calderon_zygmund_status": "bounded_at_critical_scale_only",
        "why_current_tools_fail": (
            "Riesz-transform pressure estimates give L^(3/2) control matching the "
            "critical local defect scale; they do not create a D_r^(1+alpha) gain."
        ),
    }

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "PressureStretchingDepletionGap",
        "decision": "pressure_stretching_depletion_gap_fail_closed",
        "variables_and_invariants": variables,
        "variable_count": len(variables),
        "missing_estimate": missing_estimate,
        "required_names_present": all(
            name in {row["symbol"] for row in variables}
            for name in ("u", "p", "omega", "S", "e_max", "A_r", "D_r", "Phi_r", "E_r")
        ),
        "critical_not_depleting_rows": [
            row["symbol"] for row in variables if row["scale_status"] == "critical_not_depleting"
        ],
        "control_card": CONTROL_CARD,
    }
    summary.update(false_flags())
    summary["all_fail_closed_flags_false"] = all(summary[name] is False for name in FALSE_FLAGS)
    summary["validation_passed"] = (
        summary["required_names_present"]
        and missing_estimate["alpha_required"]
        and not missing_estimate["alpha_positive_established"]
        and summary["all_fail_closed_flags_false"]
    )
    summary["summary_hash"] = stable_hash({k: v for k, v in summary.items() if k != "summary_hash"})
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
        "# Sprint 162 Pressure Stretching Depletion Gap",
        "",
        f"- Surface: `{summary['surface_name']}`",
        f"- Decision: `{summary['decision']}`",
        f"- PressureStretchingDepletionLemma: `{summary['PressureStretchingDepletionLemma']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "| symbol | name | scale_status | role |",
        "| --- | --- | --- | --- |",
    ]
    for row in summary["variables_and_invariants"]:
        lines.append(f"| {row['symbol']} | {row['name']} | {row['scale_status']} | {row['role']} |")
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
        write_json(temp_dir / ROWS_JSON_NAME, summary["variables_and_invariants"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["variables_and_invariants"])
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / MARKDOWN_NAME).write_text(render_markdown(summary), encoding="utf-8")
        write_json(temp_dir / MANIFEST_NAME, build_manifest(temp_dir, summary))
        if out_dir.exists():
            shutil.rmtree(out_dir)
        os.replace(temp_dir, out_dir)
        write_json(out_dir / MANIFEST_NAME, build_manifest(out_dir, summary))

    print(json.dumps({"contract": CONTRACT, "summary": str(out_dir / SUMMARY_NAME), "validation_passed": summary["validation_passed"]}, sort_keys=True))
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
