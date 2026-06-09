#!/usr/bin/env python3
"""Emit the projection nonlocality leakage principle artifacts."""

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


CONTRACT = "projection_nonlocality_leakage_principle"
SPRINT = 166
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

FALSE_FLAGS = (
    "ProjectionNonlocalityLeakagePrinciple",
    "NSCriticalResidualNonPositive",
    "BTFiniteHodgeVariationTheorem",
    "clay_yang_mills_promoted",
    "clay_nav_stokes_promoted",
    "clay_navier_stokes_promoted",
    "clay_YM_promotion",
    "clay_NS_promotion",
    "YM_promotion",
    "NS_promotion",
    "YM_promoted",
    "NS_promoted",
    "clay_promotions",
    "promotion_allowed",
)

PRINCIPLE_ROWS: tuple[dict[str, Any], ...] = (
    {
        "row_id": "shared_theorem_target",
        "domain": "shared",
        "operator": "[Pi,N]",
        "projection": "Pi is a genuine projection carrier, not a scalar cutoff placeholder.",
        "instantiation": (
            "If the commutator [Pi,N] is nonzero, the projected channel cannot be "
            "closed as a local invariant subproblem without a leakage or gain term."
        ),
        "leakage_or_gain": "nonzero_projection_commutator_forces_leakage_gain_term",
        "status": "target_recorded_fail_closed",
    },
    {
        "row_id": "ns_matrix_eigenbundle_projection",
        "domain": "Navier-Stokes",
        "operator": "N = R_i R_j pressure/Hessian Calderon-Zygmund channel",
        "projection": (
            "Pi = Pi_+(theta), a matrix/eigenbundle projection onto the positive "
            "angular strain-pressure branch; this is not a scalar cutoff."
        ),
        "instantiation": (
            "The NS lane asks whether [Pi_+(theta), R_i R_j] produces a positive "
            "critical-scale pressure commutator gain capable of lowering a residual."
        ),
        "leakage_or_gain": "candidate_pressure_commutator_gain_only",
        "status": "open_target_no_ns_promotion",
    },
    {
        "row_id": "bt_ym_finite_hodge_gauge_defect",
        "domain": "Bruhat-Tits/Yang-Mills",
        "operator": "[d_A,*]F_A",
        "projection": (
            "Finite Hodge star and finite gauge differential compatibility surface "
            "over the selected BT cochain carrier."
        ),
        "instantiation": (
            "The YM/BT lane records [d_A,*]F_A as a finite Hodge/gauge "
            "compatibility defect measuring failure of the selected finite star "
            "to commute with the gauge-covariant differential on curvature."
        ),
        "leakage_or_gain": "finite_hodge_gauge_compatibility_defect_only",
        "status": "open_target_no_ym_promotion",
    },
)

CONTROL_CARD = {
    "O": "Worker 2 owns only the projection nonlocality leakage principle emitter and its output bundle.",
    "R": "Record the shared target [Pi,N] nonzero implies leakage/gain, with NS and YM/BT instantiations kept unpromoted.",
    "C": "One deterministic Python stdlib script emits normalized JSON, CSV, Markdown, and manifest artifacts.",
    "S": "The theorem is a target surface only; NSCriticalResidualNonPositive, BTFiniteHodgeVariationTheorem, and Clay promotions remain false.",
    "L": "Shared commutator target -> NS eigenbundle projection Pi_+(theta) against R_iR_j -> YM/BT finite [d_A,*]F_A compatibility defect.",
    "P": "Use this artifact as a fail-closed dependency ledger for future proof work, not as a promoted theorem.",
    "G": "Validation requires exactly three rows, explicit non-scalar NS projection language, finite Hodge/gauge defect language, and all fail-closed flags false.",
    "F": "The remaining gap is a real theorem proving a quantitative leakage/gain estimate from a nonzero projection commutator.",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", "--output-dir", dest="out_dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--generated-at", default=DEFAULT_GENERATED_AT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def repo_relative(repo_root: Path, path: Path) -> str:
    return path.resolve().relative_to(repo_root.resolve()).as_posix()


def bool_flags(names: tuple[str, ...], value: bool) -> dict[str, bool]:
    return {name: value for name in names}


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, spec in enumerate(PRINCIPLE_ROWS, start=1):
        row = {
            "contract": CONTRACT,
            "sprint": SPRINT,
            "row_index": index,
            "row_id": spec["row_id"],
            "domain": spec["domain"],
            "operator": spec["operator"],
            "projection": spec["projection"],
            "instantiation": spec["instantiation"],
            "leakage_or_gain": spec["leakage_or_gain"],
            "current_status": spec["status"],
            "target_recorded": True,
            "promoted": False,
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
    combined_text = json.dumps(rows, sort_keys=True)
    ns_row = next(row for row in rows if row["domain"] == "Navier-Stokes")
    ym_row = next(row for row in rows if row["domain"] == "Bruhat-Tits/Yang-Mills")
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "artifact_id": CONTRACT,
        "sprint": SPRINT,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "ProjectionNonlocalityLeakagePrinciple",
        "decision": "projection_nonlocality_leakage_principle_recorded_fail_closed",
        "shared_theorem_target": "[Pi,N] nonzero -> leakage/gain",
        "nonzero_commutator_target_recorded": True,
        "principle_rows": rows,
        "principle_row_count": len(rows),
        "control_card": CONTROL_CARD,
        "ns_instantiation": {
            "N": "R_iR_j",
            "Pi": "Pi_+(theta)",
            "Pi_kind": "matrix/eigenbundle projection",
            "not_scalar_cutoff": True,
            "critical_residual_non_positive": False,
            "status": ns_row["current_status"],
        },
        "ym_bt_instantiation": {
            "defect": "[d_A,*]F_A",
            "defect_kind": "finite Hodge/gauge compatibility defect",
            "finite_hodge_variation_theorem": False,
            "status": ym_row["current_status"],
        },
        "promotion_claims": {
            "clay_yang_mills_promoted": False,
            "clay_navier_stokes_promoted": False,
            "yang_mills_promoted": False,
            "navier_stokes_promoted": False,
            "promotion_allowed": False,
        },
        **bool_flags(FALSE_FLAGS, False),
    }
    summary["row_false_flags_false"] = rows_named_flags_have_value(rows, FALSE_FLAGS, False)
    summary["summary_false_flags_false"] = named_flags_have_value(summary, FALSE_FLAGS, False)
    summary["validation_passed"] = (
        len(rows) == 3
        and "[Pi,N] nonzero -> leakage/gain" == summary["shared_theorem_target"]
        and "Pi_+(theta)" in combined_text
        and "matrix/eigenbundle projection" in combined_text
        and "not a scalar cutoff" in combined_text
        and "[d_A,*]F_A" in combined_text
        and "finite Hodge/gauge compatibility defect" in combined_text
        and summary["row_false_flags_false"]
        and summary["summary_false_flags_false"]
        and summary["promotion_claims"]["promotion_allowed"] is False
    )
    summary["summary_hash"] = stable_hash({key: value for key, value in summary.items() if key != "summary_hash"})
    return summary


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# Projection Nonlocality Leakage Principle",
        "",
        f"- generated_at: `{summary['generated_at']}`",
        f"- decision: `{summary['decision']}`",
        f"- shared theorem target: `{summary['shared_theorem_target']}`",
        f"- ProjectionNonlocalityLeakagePrinciple: `{summary['ProjectionNonlocalityLeakagePrinciple']}`",
        f"- NSCriticalResidualNonPositive: `{summary['NSCriticalResidualNonPositive']}`",
        f"- BTFiniteHodgeVariationTheorem: `{summary['BTFiniteHodgeVariationTheorem']}`",
        f"- promotion_allowed: `{summary['promotion_allowed']}`",
        "",
        "## Instantiations",
        "",
        "| index | domain | operator | projection/defect surface | status |",
        "| ---: | --- | --- | --- | --- |",
    ]
    for row in summary["principle_rows"]:
        lines.append(
            "| {row_index} | {domain} | {operator} | {projection} | {current_status} |".format(**row)
        )
    lines.extend(
        [
            "",
            "## Notes",
            "",
            "- The NS instantiation fixes `N=R_iR_j` and `Pi=Pi_+(theta)` as a matrix/eigenbundle projection, not a scalar cutoff.",
            "- The YM/BT instantiation records `[d_A,*]F_A` as a finite Hodge/gauge compatibility defect.",
            "- These artifacts do not promote the projection principle, NS residual closure, BT finite Hodge variation theorem, YM, NS, or Clay claims.",
            "",
            "## O/R/C/S/L/P/G/F",
            "",
        ]
    )
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(repo_root: Path, out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / SUMMARY_NAME,
        "rows_json": out_dir / ROWS_JSON_NAME,
        "rows_csv": out_dir / ROWS_CSV_NAME,
        "markdown": out_dir / MARKDOWN_NAME,
    }
    manifest = {
        "contract": CONTRACT,
        "artifact_id": CONTRACT,
        "sprint": SPRINT,
        "generated_at": summary["generated_at"],
        "output_dir": repo_relative(repo_root, out_dir),
        "validation_passed": summary["validation_passed"],
        "files": {
            key: {
                "path": repo_relative(repo_root, path),
                "exists": path.exists(),
                "size_bytes": path.stat().st_size if path.exists() else 0,
                "sha256": file_sha256(path) if path.exists() else None,
            }
            for key, path in files.items()
        },
        "artifacts": [
            {
                "path": repo_relative(repo_root, path),
                "size_bytes": path.stat().st_size,
                "sha256": file_sha256(path),
            }
            for path in files.values()
            if path.exists()
        ],
    }
    manifest["manifest_hash"] = stable_hash({key: value for key, value in manifest.items() if key != "manifest_hash"})
    return manifest


def write_outputs(repo_root: Path, out_dir: Path, summary: dict[str, Any]) -> None:
    final_out = out_dir if out_dir.is_absolute() else repo_root / out_dir
    final_out = final_out.resolve()
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / ROWS_JSON_NAME, summary["principle_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["principle_rows"])
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / MARKDOWN_NAME).write_text(render_markdown(summary), encoding="utf-8")
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
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
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
