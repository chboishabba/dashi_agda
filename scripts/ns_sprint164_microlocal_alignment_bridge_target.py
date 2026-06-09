#!/usr/bin/env python3
"""Sprint 164 lane 2 microlocal-alignment bridge target emitter."""

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


CONTRACT = "ns_sprint164_microlocal_alignment_bridge_target"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 164
LANE = 2
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

REQUIRED_TRUE_FLAGS = (
    "MicrolocalAlignmentConcentrationTargetRecorded",
)

AUTHORITY_FALSE_FLAGS = (
    "MicrolocalAlignmentConcentrationLemma",
    "BlowupImpliesSigmaConcentration",
    "MechanismExhaustionForFullClayNS",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "fullNavierStokesSolutionConstructed",
    "clayNavierStokesPromoted",
    "ClayNavierStokesPromoted",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
    "promotionAllowed",
)

CHAIN_ROWS = (
    {
        "row_id": "M01",
        "chain_step": "persistent_alignment_ratio",
        "chain_role": "hypothesis",
        "statement": "The physical-space alignment defect has persistent positive limsup A_r/D_r.",
        "status": "TARGET_HYPOTHESIS_RECORDED",
        "mathematical_surface": "limsup_r_to_0 A_r(z0) / D_r(z0) > 0",
        "bridge_obligation": "Convert persistent stretching into microlocal angular information.",
    },
    {
        "row_id": "M02",
        "chain_step": "semiclassical_defect_measure",
        "chain_role": "microlocal_object",
        "statement": "A blowup-rescaled Littlewood-Paley sequence should yield a semiclassical defect measure mu on Q1 x S2.",
        "status": "TARGET_OBJECT_RECORDED_NOT_CONSTRUCTED",
        "mathematical_surface": "mu on Q1 x S2",
        "bridge_obligation": "Construct mu from the critical ancient profile without assuming a Clay-closing compactness theorem.",
    },
    {
        "row_id": "M03",
        "chain_step": "positive_mass_on_graph_lmax",
        "chain_role": "alignment_transfer",
        "statement": "Persistent A_r/D_r positivity should force positive mu-mass on the graph of the maximal-stretching eigenbundle Lmax.",
        "status": "THEOREM_TARGET_RECORDED_NOT_PROVED",
        "mathematical_surface": "mu({(x,t,theta): omega_hat parallel Lmax(theta)}) > 0",
        "bridge_obligation": "Prove that physical stretching concentration cannot be an artifact of physical-space averaging alone.",
    },
    {
        "row_id": "M04",
        "chain_step": "local_orientable_chart",
        "chain_role": "fork_case",
        "statement": "If the microlocal mass stays in one orientable angular chart, the bridge must record this as a local-chart escape case.",
        "status": "OPEN_FORK_CASE",
        "mathematical_surface": "support(mu) contained in orientable patch of S2 minus Sigma",
        "bridge_obligation": "Determine whether local chart support can persist across a critical cascade.",
    },
    {
        "row_id": "M05",
        "chain_step": "monodromy_jump",
        "chain_role": "fork_case",
        "statement": "If support winds around a transverse degeneracy, nonorientable monodromy forces a jump or sign reversal in Lmax.",
        "status": "OPEN_FORK_CASE",
        "mathematical_surface": "Möbius monodromy of Lmax around Sigma",
        "bridge_obligation": "Translate monodromy into an analytic stretching-loss or branch-switching estimate.",
    },
    {
        "row_id": "M06",
        "chain_step": "sigma_concentration",
        "chain_role": "fork_case",
        "statement": "If alignment persists despite monodromy, the remaining target is concentration of mu near Sigma.",
        "status": "TARGET_RECORDED_NOT_PROVED",
        "mathematical_surface": "limsup_r_to_0 mu_r(N_delta(Sigma)) >= c for every delta > 0",
        "bridge_obligation": "Prove BlowupImpliesSigmaConcentration or isolate the exact failure.",
    },
    {
        "row_id": "M07",
        "chain_step": "alignment_loss",
        "chain_role": "fork_case",
        "statement": "If none of the preceding cases sustains positive graph mass, alignment depletes and the residual route may close conditionally.",
        "status": "CONDITIONAL_REGULARITY_FORK_NOT_GENERAL_PROOF",
        "mathematical_surface": "A_r / D_r -> 0",
        "bridge_obligation": "Feed alignment loss back into NSCriticalResidual without promoting full Clay.",
    },
)

CONTROL_CARD = {
    "O": "Sprint164 lane 2 owns only the microlocal-alignment bridge target emitter.",
    "R": "Emit the target chain from persistent A_r/D_r positivity to the four microlocal fork cases.",
    "C": "One Python stdlib script writes normalized JSON, CSV, Markdown, and manifest artifacts.",
    "S": "Sprint163 recorded a symbol-level obstruction; the missing bridge is physical-space alignment to microlocal defect measure support.",
    "L": "A_r/D_r positive -> mu on Q1 x S2 -> graph Lmax mass -> orientable chart / monodromy jump / Sigma concentration / alignment loss.",
    "P": "Record a target ledger only; keep the lemma, Sigma concentration, and Clay flags false.",
    "G": "Validation passes only when the target-recorded flag is true and all theorem/authority flags remain false.",
    "F": "Microlocal bridge, blowup-to-Sigma concentration, and mechanism exhaustion remain unproved.",
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


def true_flags() -> dict[str, bool]:
    return {name: True for name in REQUIRED_TRUE_FLAGS}


def false_flags() -> dict[str, bool]:
    return {name: False for name in AUTHORITY_FALSE_FLAGS}


def named_flags_have_value(record: dict[str, Any], names: tuple[str, ...], value: bool) -> bool:
    return all(record.get(name) is value for name in names)


def rows_named_flags_have_value(rows: list[dict[str, Any]], names: tuple[str, ...], value: bool) -> bool:
    return all(named_flags_have_value(row, names, value) for row in rows)


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, spec in enumerate(CHAIN_ROWS, start=1):
        row: dict[str, Any] = {
            "sprint": SPRINT,
            "lane": LANE,
            "contract": CONTRACT,
            "surface_name": "MicrolocalAlignmentBridgeTarget",
            "chain_index": index,
            "target_recorded": True,
            "proved": False,
            "closed": False,
            "fail_closed": True,
            **spec,
            **true_flags(),
            **false_flags(),
        }
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_rows()
    expected_steps = [row["chain_step"] for row in CHAIN_ROWS]
    actual_steps = [row["chain_step"] for row in rows]
    fork_cases = [
        "local_orientable_chart",
        "monodromy_jump",
        "sigma_concentration",
        "alignment_loss",
    ]

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "MicrolocalAlignmentBridgeTarget",
        "decision": "microlocal_alignment_concentration_target_recorded_fail_closed",
        "target_chain": (
            "persistent A_r/D_r positive -> semiclassical defect measure mu on Q1 x S2 "
            "-> positive mass on graph Lmax -> local orientable chart / monodromy jump / "
            "Sigma concentration / alignment loss"
        ),
        "chain_rows": rows,
        "row_count": len(rows),
        "chain_steps": actual_steps,
        "expected_chain_steps_present": actual_steps == expected_steps,
        "fork_cases": fork_cases,
        "all_fork_cases_present": set(fork_cases).issubset(set(actual_steps)),
        "microlocal_measure_surface": "mu on Q1 x S2",
        "alignment_graph_surface": "graph Lmax",
        "sigma_surface": "Sigma",
        "control_card": CONTROL_CARD,
        **true_flags(),
        **false_flags(),
    }
    summary["row_target_flags_true"] = rows_named_flags_have_value(rows, REQUIRED_TRUE_FLAGS, True)
    summary["row_authority_flags_false"] = rows_named_flags_have_value(rows, AUTHORITY_FALSE_FLAGS, False)
    summary["summary_target_flags_true"] = named_flags_have_value(summary, REQUIRED_TRUE_FLAGS, True)
    summary["summary_authority_flags_false"] = named_flags_have_value(summary, AUTHORITY_FALSE_FLAGS, False)
    summary["validation_passed"] = (
        summary["MicrolocalAlignmentConcentrationTargetRecorded"] is True
        and summary["MicrolocalAlignmentConcentrationLemma"] is False
        and summary["BlowupImpliesSigmaConcentration"] is False
        and summary["MechanismExhaustionForFullClayNS"] is False
        and summary["full_clay_ns_solved"] is False
        and summary["clayNavierStokesPromoted"] is False
        and summary["expected_chain_steps_present"]
        and summary["all_fork_cases_present"]
        and summary["row_target_flags_true"]
        and summary["row_authority_flags_false"]
        and summary["summary_target_flags_true"]
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
        "# Sprint 164 Microlocal Alignment Bridge Target",
        "",
        f"- Surface: `{summary['surface_name']}`",
        f"- Decision: `{summary['decision']}`",
        f"- Target recorded: `{summary['MicrolocalAlignmentConcentrationTargetRecorded']}`",
        f"- MicrolocalAlignmentConcentrationLemma: `{summary['MicrolocalAlignmentConcentrationLemma']}`",
        f"- BlowupImpliesSigmaConcentration: `{summary['BlowupImpliesSigmaConcentration']}`",
        f"- MechanismExhaustionForFullClayNS: `{summary['MechanismExhaustionForFullClayNS']}`",
        f"- full_clay_ns_solved: `{summary['full_clay_ns_solved']}`",
        f"- clayNavierStokesPromoted: `{summary['clayNavierStokesPromoted']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "## Target Chain",
        "",
        summary["target_chain"],
        "",
        "| index | step | role | status | surface |",
        "| ---: | --- | --- | --- | --- |",
    ]
    for row in summary["chain_rows"]:
        lines.append(
            f"| {row['chain_index']} | {row['chain_step']} | "
            f"{row['chain_role']} | {row['status']} | {row['mathematical_surface']} |"
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
        write_json(temp_dir / ROWS_JSON_NAME, summary["chain_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["chain_rows"])
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
