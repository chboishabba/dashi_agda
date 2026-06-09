#!/usr/bin/env python3
"""Sprint 164 lane 4 pressure-commutator gain target emitter."""

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


CONTRACT = "ns_sprint164_pressure_commutator_gain_target"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 164
LANE = 4
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

TRUE_FLAGS = (
    "AngularDegeneracyPressureCommutatorGainTargetRecorded",
    "CalderonZygmundCriticalBarrierRecorded",
    "PressureFluxSubcriticalGainOpen",
)

FALSE_FLAGS = (
    "AngularDegeneracyPressureCommutatorGain",
    "PressureStretchingDepletionLemma",
    "FullLocalDefectMonotonicity",
    "MechanismExhaustionForFullClayNS",
    "full_clay_ns_solved",
    "clayNavierStokesPromoted",
)

TARGET_ROWS = (
    {
        "row_id": "P01",
        "surface": "pressure_representation",
        "object": "p = R_i R_j(u_i u_j)",
        "status": "RECORDED",
        "target_role": "nonlocal pressure input",
        "statement": "Pressure is represented by second-order Riesz transforms applied to the quadratic velocity tensor.",
    },
    {
        "row_id": "P02",
        "surface": "angular_projector",
        "object": "Pi_plus(theta) near Sigma",
        "status": "RECORDED",
        "target_role": "maximal-strain branch selector",
        "statement": "Pi_plus is the angular projector onto the local maximal-stretching eigenbranch near the degeneracy set Sigma.",
    },
    {
        "row_id": "P03",
        "surface": "pressure_commutator",
        "object": "[Pi_plus, R_i R_j]",
        "status": "TARGET_RECORDED_NOT_PROVED",
        "target_role": "candidate incoherence mechanism",
        "statement": "The commutator between the singular angular projector and the smooth Riesz multiplier is the proposed source of pressure-coherence loss near Sigma.",
    },
    {
        "row_id": "P04",
        "surface": "calderon_zygmund_barrier",
        "object": "alpha = 0",
        "status": "CRITICAL_BARRIER_RECORDED",
        "target_role": "known insufficient estimate",
        "statement": "Calderon-Zygmund boundedness controls pressure at the critical scale but gives no alpha-positive subcritical gain.",
    },
    {
        "row_id": "P05",
        "surface": "required_subcritical_gain",
        "object": "alpha > 0",
        "status": "OPEN",
        "target_role": "missing Clay-relevant pressure gain",
        "statement": "A usable pressure-flux estimate must improve critical control to a D_r^(1+alpha) type gain for some alpha > 0.",
    },
)

CONTROL_CARD = {
    "O": "Sprint164 lane 4 owns only the pressure-commutator gain target emitter.",
    "R": "Record p=RiRj(uiuj), Pi_plus near Sigma, the commutator target, CZ alpha-zero barrier, and alpha-positive gain requirement.",
    "C": "One stdlib Python script emits normalized JSON, CSV, Markdown, and manifest outputs.",
    "S": "The pressure commutator is a theorem target; no depletion, local defect monotonicity, or Clay promotion is established.",
    "L": "Riesz pressure + angular projector near Sigma -> commutator target -> CZ alpha=0 wall -> required alpha>0 gain.",
    "P": "Fail-close AngularDegeneracyPressureCommutatorGain while recording the target and open pressure-flux gain.",
    "G": "Promotion requires the three requested recorded/open flags true and all theorem/Clay flags false.",
    "F": "The missing estimate is an alpha-positive pressure coherence loss near the angular-strain degeneracy set Sigma.",
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
    for index, spec in enumerate(TARGET_ROWS, start=1):
        row: dict[str, Any] = {
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "chain_index": index,
            "closed": False,
            "fail_closed": True,
            "external_boundary_only": True,
            **spec,
            **bool_flags(TRUE_FLAGS, True),
            **bool_flags(FALSE_FLAGS, False),
        }
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def named_flags_have_value(record: dict[str, Any], names: tuple[str, ...], value: bool) -> bool:
    return all(record.get(name) is value for name in names)


def rows_named_flags_have_value(rows: list[dict[str, Any]], names: tuple[str, ...], value: bool) -> bool:
    return all(named_flags_have_value(row, names, value) for row in rows)


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_rows()
    surfaces = [row["surface"] for row in rows]
    required_surfaces_present = surfaces == [row["surface"] for row in TARGET_ROWS]
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "PressureCommutatorGainTarget",
        "decision": "pressure_commutator_gain_target_recorded_fail_closed",
        "pressure_representation": "p = R_i R_j(u_i u_j)",
        "angular_projector": "Pi_plus(theta) near Sigma",
        "commutator": "[Pi_plus, R_i R_j]",
        "calderon_zygmund_barrier": "alpha = 0 critical-scale boundedness only",
        "required_gain": "alpha > 0 subcritical pressure-flux gain",
        "target_inequality_shape": (
            "|PressureFlux_r| <= C D_r - c_Sigma AngVar_Sigma(mu_r) D_r + o(D_r), "
            "or equivalently a usable D_r^(1+alpha) gain for alpha > 0."
        ),
        "precise_gap": (
            "The angular pressure commutator target is recorded, but no theorem proves "
            "that [Pi_plus, R_i R_j] supplies pressure-flux subcritical gain near Sigma."
        ),
        "target_rows": rows,
        "row_count": len(rows),
        "surfaces": surfaces,
        "required_surfaces_present": required_surfaces_present,
        "control_card": CONTROL_CARD,
        **bool_flags(TRUE_FLAGS, True),
        **bool_flags(FALSE_FLAGS, False),
    }
    summary["row_true_flags_true"] = rows_named_flags_have_value(rows, TRUE_FLAGS, True)
    summary["row_false_flags_false"] = rows_named_flags_have_value(rows, FALSE_FLAGS, False)
    summary["summary_true_flags_true"] = named_flags_have_value(summary, TRUE_FLAGS, True)
    summary["summary_false_flags_false"] = named_flags_have_value(summary, FALSE_FLAGS, False)
    summary["validation_passed"] = (
        required_surfaces_present
        and summary["AngularDegeneracyPressureCommutatorGainTargetRecorded"] is True
        and summary["CalderonZygmundCriticalBarrierRecorded"] is True
        and summary["PressureFluxSubcriticalGainOpen"] is True
        and summary["AngularDegeneracyPressureCommutatorGain"] is False
        and summary["PressureStretchingDepletionLemma"] is False
        and summary["FullLocalDefectMonotonicity"] is False
        and summary["MechanismExhaustionForFullClayNS"] is False
        and summary["full_clay_ns_solved"] is False
        and summary["clayNavierStokesPromoted"] is False
        and summary["row_true_flags_true"]
        and summary["row_false_flags_false"]
        and summary["summary_true_flags_true"]
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
        "# Sprint 164 Pressure Commutator Gain Target",
        "",
        f"- Surface: `{summary['surface_name']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Pressure representation: `{summary['pressure_representation']}`",
        f"- Angular projector: `{summary['angular_projector']}`",
        f"- Commutator: `{summary['commutator']}`",
        f"- CZ barrier: `{summary['calderon_zygmund_barrier']}`",
        f"- Required gain: `{summary['required_gain']}`",
        f"- AngularDegeneracyPressureCommutatorGain: `{summary['AngularDegeneracyPressureCommutatorGain']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "## Target Rows",
        "",
        "| row | surface | object | status | target_role |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["target_rows"]:
        lines.append(
            f"| {row['row_id']} | {row['surface']} | {row['object']} | {row['status']} | {row['target_role']} |"
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
        write_json(temp_dir / ROWS_JSON_NAME, summary["target_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["target_rows"])
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
