#!/usr/bin/env python3
"""P0 Clay finite-Hodge and NS stack priority emitter."""

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


CONTRACT = "p0_clay_finite_hodge_ns_stack"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 165
WORKER = 2
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

EXACT_NEXT_PROOF_OVERALL = "BTFiniteHodgeVariationTheorem"
EXACT_NEXT_PROOF_NS_ONLY = "AngularDegeneracyPressureCommutatorGain"

TRUE_FLAGS = (
    "P0ClayFiniteHodgeNSStackRecorded",
    "BTFiniteHodgeVariationTheoremNextProofTarget",
    "AngularDegeneracyPressureCommutatorGainNextProofTarget",
    "FailClosedPromotionFlagsRecorded",
)

FALSE_FLAGS = (
    "BTFiniteHodgeVariationTheorem",
    "BTFiniteHodgeVariationTheoremCalculated",
    "AngularDegeneracyPressureCommutatorGain",
    "MicrolocalAlignmentConcentrationLemma",
    "TopologicalStretchingLeakageLemma",
    "FullLocalDefectMonotonicity",
    "MechanismExhaustionForFullClayNS",
    "MaxwellFieldEquationPromoted",
    "YangMillsMassGapPromoted",
    "NavierStokesClayPromoted",
    "StandardModelEmpiricalPromotion",
    "PAdicPhysicalOntologyPromoted",
    "ContinuumTransferPromoted",
    "full_clay_ns_solved",
    "fullClayNSSolved",
    "clayNavierStokesPromoted",
    "ClayNavierStokesPromoted",
    "clay_navier_stokes_promoted",
    "terminalUnificationPromoted",
    "promotion_allowed",
    "promotionAllowed",
)

PRIORITY_ROWS = (
    {
        "row_id": "P0-01",
        "stack_lane": "overall",
        "priority_rank": 1,
        "priority": EXACT_NEXT_PROOF_OVERALL,
        "status": "EXACT_NEXT_PROOF_TO_CALCULATE",
        "proof_target": EXACT_NEXT_PROOF_OVERALL,
        "scope": "P0 Clay-facing finite-Hodge stack",
        "statement": "Calculate the finite-Hodge variation theorem before any broader Clay, YM, Maxwell, Standard Model, ontology, continuum, or terminal promotion.",
        "acceptance_gate": "A checked BTFiniteHodgeVariationTheorem calculation exists and consumes the finite-depth Hodge variation obligations without changing promotion flags.",
    },
    {
        "row_id": "P0-02",
        "stack_lane": "finite_hodge_support",
        "priority_rank": 2,
        "priority": "BT finite Hodge-star and effective-action obligations",
        "status": "SUPPORTING_OBLIGATIONS_ONLY",
        "proof_target": EXACT_NEXT_PROOF_OVERALL,
        "scope": "BTFiniteHodgeStarObligation and BTFiniteHodgeEffectiveActionTheoremBoundary support",
        "statement": "Use the existing finite-depth Hodge-star and effective-action boundary surfaces as the substrate for the variation theorem calculation.",
        "acceptance_gate": "Support rows stay boundary/theorem-target rows until the variation theorem is calculated.",
    },
    {
        "row_id": "P0-03",
        "stack_lane": "ns_only",
        "priority_rank": 1,
        "priority": EXACT_NEXT_PROOF_NS_ONLY,
        "status": "EXACT_NS_ONLY_NEXT_PROOF_TO_CALCULATE",
        "proof_target": EXACT_NEXT_PROOF_NS_ONLY,
        "scope": "Navier-Stokes-only Sprint164 pressure-commutator lane",
        "statement": "For the NS-only track, calculate AngularDegeneracyPressureCommutatorGain next; the target is currently recorded but unproved.",
        "acceptance_gate": "Prove an alpha-positive pressure coherence loss near Sigma without asserting full local defect monotonicity or full Clay NS.",
    },
    {
        "row_id": "P0-04",
        "stack_lane": "ns_prerequisite_targets",
        "priority_rank": 2,
        "priority": "microlocal alignment and topological stretching bridge targets",
        "status": "RECORDED_TARGETS_NOT_PROVED",
        "proof_target": EXACT_NEXT_PROOF_NS_ONLY,
        "scope": "NS microlocal/topological bridge",
        "statement": "MicrolocalAlignmentConcentration and TopologicalStretchingLeakage remain recorded bridge targets feeding the pressure-commutator proof, not promoted lemmas.",
        "acceptance_gate": "Any bridge progress must remain fail-closed unless the named lemmas are actually proved.",
    },
    {
        "row_id": "P0-05",
        "stack_lane": "promotion_governance",
        "priority_rank": 3,
        "priority": "fail-closed promotion flags",
        "status": "PROMOTION_CLOSED",
        "proof_target": "none",
        "scope": "all P0 stack lanes",
        "statement": "All Clay, NS, YM, Maxwell, Standard Model, p-adic ontology, continuum, and terminal promotion flags stay false while the exact next proof targets are only queued.",
        "acceptance_gate": "Validation passes only when target-recorded flags are true and every promotion/theorem-completion flag is false.",
    },
)

CONTROL_CARD = {
    "O": "Worker 2 owns only the Sprint165 P0 Clay finite-Hodge and NS stack priority emitter.",
    "R": "Record the P0 stack priorities with exact next proof targets: BTFiniteHodgeVariationTheorem overall and AngularDegeneracyPressureCommutatorGain for NS-only.",
    "C": "One Python stdlib script emits normalized JSON, CSV, Markdown, and manifest artifacts under outputs/p0_clay_finite_hodge_ns_stack/.",
    "S": "The repo has finite-depth BT/Hodge boundary surfaces and Sprint164 NS pressure-commutator targets; this artifact queues proof calculation without adding proof content.",
    "L": "overall P0 -> BTFiniteHodgeVariationTheorem; NS-only P0 -> AngularDegeneracyPressureCommutatorGain; all promotions remain closed.",
    "P": "Use this as a deterministic Sprint165 priority stack ledger and fail-closed promotion guard.",
    "G": "Validation passes only when the two exact next proof targets are recorded and every theorem-completion or promotion flag remains false.",
    "F": "No Clay, NS, YM, Maxwell, Standard Model, p-adic ontology, continuum, or terminal unification promotion is established by this stack ledger.",
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


def named_flags_have_value(record: dict[str, Any], names: tuple[str, ...], value: bool) -> bool:
    return all(record.get(name) is value for name in names)


def rows_named_flags_have_value(rows: list[dict[str, Any]], names: tuple[str, ...], value: bool) -> bool:
    return all(named_flags_have_value(row, names, value) for row in rows)


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, spec in enumerate(PRIORITY_ROWS, start=1):
        row: dict[str, Any] = {
            "sprint": SPRINT,
            "worker": WORKER,
            "contract": CONTRACT,
            "chain_index": index,
            "target_recorded": True,
            "proved": False,
            "closed": False,
            "fail_closed": True,
            **spec,
            **bool_flags(TRUE_FLAGS, True),
            **bool_flags(FALSE_FLAGS, False),
        }
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def build_summary(repo_root: Path, out_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = build_rows()
    row_ids = [row["row_id"] for row in rows]
    overall_rows = [row for row in rows if row["stack_lane"] == "overall"]
    ns_rows = [row for row in rows if row["stack_lane"] == "ns_only"]
    expected_row_ids = [row["row_id"] for row in PRIORITY_ROWS]

    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "worker": WORKER,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "summary_path": str(out_dir / SUMMARY_NAME),
        "surface_name": "P0ClayFiniteHodgeNSStack",
        "decision": "p0_priority_stack_recorded_fail_closed",
        "exact_next_proof_to_calculate_overall": EXACT_NEXT_PROOF_OVERALL,
        "exact_next_proof_to_calculate_ns_only": EXACT_NEXT_PROOF_NS_ONLY,
        "priority_rows": rows,
        "row_count": len(rows),
        "row_ids": row_ids,
        "expected_row_ids_present": row_ids == expected_row_ids,
        "overall_next_proof_exact": len(overall_rows) == 1 and overall_rows[0]["proof_target"] == EXACT_NEXT_PROOF_OVERALL,
        "ns_only_next_proof_exact": len(ns_rows) == 1 and ns_rows[0]["proof_target"] == EXACT_NEXT_PROOF_NS_ONLY,
        "promotion_policy": "fail_closed",
        "control_card": CONTROL_CARD,
        **bool_flags(TRUE_FLAGS, True),
        **bool_flags(FALSE_FLAGS, False),
    }
    summary["row_true_flags_true"] = rows_named_flags_have_value(rows, TRUE_FLAGS, True)
    summary["row_false_flags_false"] = rows_named_flags_have_value(rows, FALSE_FLAGS, False)
    summary["summary_true_flags_true"] = named_flags_have_value(summary, TRUE_FLAGS, True)
    summary["summary_false_flags_false"] = named_flags_have_value(summary, FALSE_FLAGS, False)
    summary["all_rows_fail_closed"] = all(row["fail_closed"] is True and row["proved"] is False for row in rows)
    summary["validation_passed"] = (
        summary["P0ClayFiniteHodgeNSStackRecorded"] is True
        and summary["BTFiniteHodgeVariationTheoremNextProofTarget"] is True
        and summary["AngularDegeneracyPressureCommutatorGainNextProofTarget"] is True
        and summary["BTFiniteHodgeVariationTheorem"] is False
        and summary["BTFiniteHodgeVariationTheoremCalculated"] is False
        and summary["AngularDegeneracyPressureCommutatorGain"] is False
        and summary["MechanismExhaustionForFullClayNS"] is False
        and summary["full_clay_ns_solved"] is False
        and summary["clayNavierStokesPromoted"] is False
        and summary["terminalUnificationPromoted"] is False
        and summary["expected_row_ids_present"]
        and summary["overall_next_proof_exact"]
        and summary["ns_only_next_proof_exact"]
        and summary["all_rows_fail_closed"]
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
        "# P0 Clay Finite-Hodge / NS Stack",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Exact next proof overall: `{summary['exact_next_proof_to_calculate_overall']}`",
        f"- Exact next proof NS-only: `{summary['exact_next_proof_to_calculate_ns_only']}`",
        f"- Promotion policy: `{summary['promotion_policy']}`",
        f"- BTFiniteHodgeVariationTheorem: `{summary['BTFiniteHodgeVariationTheorem']}`",
        f"- AngularDegeneracyPressureCommutatorGain: `{summary['AngularDegeneracyPressureCommutatorGain']}`",
        f"- MechanismExhaustionForFullClayNS: `{summary['MechanismExhaustionForFullClayNS']}`",
        f"- clayNavierStokesPromoted: `{summary['clayNavierStokesPromoted']}`",
        f"- terminalUnificationPromoted: `{summary['terminalUnificationPromoted']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "## Priority Rows",
        "",
        "| row | lane | rank | priority | status | proof target |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in summary["priority_rows"]:
        lines.append(
            f"| {row['row_id']} | {row['stack_lane']} | {row['priority_rank']} | "
            f"{row['priority']} | {row['status']} | {row['proof_target']} |"
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
        "worker": WORKER,
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
        write_json(temp_dir / ROWS_JSON_NAME, summary["priority_rows"])
        write_csv(temp_dir / ROWS_CSV_NAME, summary["priority_rows"])
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
