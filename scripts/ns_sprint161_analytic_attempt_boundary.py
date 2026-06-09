#!/usr/bin/env python3
"""Sprint 161 analytic attempt boundary emitter."""

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


CONTRACT = "ns_sprint161_analytic_attempt_boundary"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SPRINT = 161
LANE = 2
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

FAIL_CLOSED = "FAIL_CLOSED_ANALYTIC_BOUNDARY"
ATTEMPT_OPEN = "ATTEMPT_OPEN_STRUCTURAL_GAP"
ATTEMPT_PARTIAL = "ATTEMPT_PARTIAL_LOCAL_WITNESS"

CLAY_FLAGS = (
    "MechanismExhaustionForFullClayNS",
    "FullClayMechanismExhaustion",
    "GeneralSmoothFiniteEnergyNSRegularity",
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

REQUIRED_FALSE_TERMS = (
    "MechanismExhaustionForFullClayNS",
    "NonAxisymmetricVortexStretchingDepletion",
    "PressureNonlocalityClosureForGeneralData",
    "FiniteCriticalProfileTaxonomy",
)

CONTROL_CARD = {
    "O": "Worker 2 owns the Sprint161 analytic attempt boundary emitter.",
    "R": "Emit a normalized boundary ledger for the four-stage ancient-solution route.",
    "C": "Python stdlib script writes rows, summary, Markdown, and manifest deterministically.",
    "S": "Sprint160 governance keeps local Clay promotion stopped without new PDE math.",
    "L": "critical rescaling -> ancient compactness -> local defect monotonicity -> continuation and taxonomy boundary.",
    "P": "Use this artifact to record the analytic attempt without promoting full Clay Navier-Stokes.",
    "G": "Validation requires four ordered stages, all summary guards false where claimed, and Clay promotion false.",
    "F": "The route remains an attempt boundary, not a proof of full general-data regularity.",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--output-dir", "--out-dir", dest="output_dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--generated-at", default=DEFAULT_GENERATED_AT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def file_sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def false_flags() -> dict[str, bool]:
    flags = {flag: False for flag in CLAY_FLAGS}
    flags.update(
        {
            "MechanismExhaustionForFullClayNS": False,
            "NonAxisymmetricVortexStretchingDepletion": False,
            "PressureNonlocalityClosureForGeneralData": False,
            "FiniteCriticalProfileTaxonomy": False,
        }
    )
    return flags


def build_rows(generated_at: str) -> list[dict[str, Any]]:
    specs = [
        {
            "stage": 1,
            "row_id": "stage_1_critical_rescaling",
            "route_stage": "critical_rescaling_and_normalization",
            "analytic_claim": "Normalize a hypothetical critical sequence into candidate ancient-solution data.",
            "attempt_boundary": "No general-data reduction to a finite critical profile taxonomy is established.",
            "status": ATTEMPT_OPEN,
            "LocalDefectMonotonicityAttempt": False,
        },
        {
            "stage": 2,
            "row_id": "stage_2_ancient_solution_compactness",
            "route_stage": "ancient_solution_compactness",
            "analytic_claim": "Extract an ancient-solution route from critical-scale concentration.",
            "attempt_boundary": "Compactness is not closed for arbitrary smooth finite-energy 3D data.",
            "status": ATTEMPT_OPEN,
            "LocalDefectMonotonicityAttempt": False,
        },
        {
            "stage": 3,
            "row_id": "stage_3_local_defect_monotonicity_attempt",
            "route_stage": "local_defect_monotonicity",
            "analytic_claim": "Test whether a local defect monotonicity quantity can deplete the route.",
            "attempt_boundary": "LocalDefectMonotonicityAttempt is only an attempted witness and does not close nonaxisymmetric stretching.",
            "status": ATTEMPT_PARTIAL,
            "LocalDefectMonotonicityAttempt": True,
        },
        {
            "stage": 4,
            "row_id": "stage_4_continuation_and_promotion_boundary",
            "route_stage": "continuation_and_clay_promotion_boundary",
            "analytic_claim": "Connect route depletion to continuation only if all structural closures are supplied.",
            "attempt_boundary": "Pressure nonlocality, taxonomy, mechanism exhaustion, and Clay promotion remain false.",
            "status": FAIL_CLOSED,
            "LocalDefectMonotonicityAttempt": False,
        },
    ]
    rows: list[dict[str, Any]] = []
    for spec in specs:
        row: dict[str, Any] = {
            **spec,
            "contract": CONTRACT,
            "sprint": SPRINT,
            "lane": LANE,
            "generated_at": generated_at,
            "route": "four_stage_ancient_solution_route",
            "clay_promotion_allowed": False,
            "normalized": True,
            "summary_flag": spec["stage"] == 4,
        }
        row.update(false_flags())
        row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
        rows.append(row)
    return rows


def all_false(records: list[dict[str, Any]] | dict[str, Any], keys: tuple[str, ...]) -> bool:
    if isinstance(records, dict):
        return all(records.get(key) is False for key in keys)
    return all(all(record.get(key) is False for key in keys) for record in records)


def build_summary(rows: list[dict[str, Any]], generated_at: str) -> dict[str, Any]:
    ordered_four_stage_route = [row["stage"] for row in rows] == [1, 2, 3, 4]
    summary = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "generated_at": generated_at,
        "row_count": len(rows),
        "decision": "analytic_attempt_boundary_fail_closed",
        "route": "four_stage_ancient_solution_route",
        "ordered_four_stage_route": ordered_four_stage_route,
        "stage_ids": [row["row_id"] for row in rows],
        "LocalDefectMonotonicityAttempt": any(row["LocalDefectMonotonicityAttempt"] for row in rows),
        "MechanismExhaustionForFullClayNS": False,
        "NonAxisymmetricVortexStretchingDepletion": False,
        "PressureNonlocalityClosureForGeneralData": False,
        "FiniteCriticalProfileTaxonomy": False,
        "clay_promotion_allowed": False,
        "promotion_allowed": False,
        "ClaySubmissionReady": False,
        "ClaySubmissionPromotionPacket": False,
        "summary_flags": {
            "MechanismExhaustionForFullClayNS": False,
            "LocalDefectMonotonicityAttempt": True,
            "NonAxisymmetricVortexStretchingDepletion": False,
            "PressureNonlocalityClosureForGeneralData": False,
            "FiniteCriticalProfileTaxonomy": False,
            "clay_promotion_allowed": False,
        },
        "control_card": CONTROL_CARD,
    }
    summary.update(false_flags())
    summary["LocalDefectMonotonicityAttempt"] = True
    summary["row_required_false_terms_false"] = all_false(rows, REQUIRED_FALSE_TERMS)
    summary["summary_required_false_terms_false"] = all_false(summary, REQUIRED_FALSE_TERMS)
    summary["row_clay_flags_false"] = all_false(rows, CLAY_FLAGS)
    summary["summary_clay_flags_false"] = all_false(summary, CLAY_FLAGS)
    summary["validation_passed"] = (
        len(rows) == 4
        and ordered_four_stage_route
        and summary["LocalDefectMonotonicityAttempt"] is True
        and summary["row_required_false_terms_false"]
        and summary["summary_required_false_terms_false"]
        and summary["row_clay_flags_false"]
        and summary["summary_clay_flags_false"]
        and summary["clay_promotion_allowed"] is False
    )
    summary["summary_hash"] = stable_hash({k: v for k, v in summary.items() if k != "summary_hash"})
    return summary


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    assert summary["validation_passed"] is True
    assert len(rows) == 4
    assert [row["stage"] for row in rows] == [1, 2, 3, 4]
    assert any(row["LocalDefectMonotonicityAttempt"] is True for row in rows)
    assert all_false(rows, REQUIRED_FALSE_TERMS)
    assert all_false(rows, CLAY_FLAGS)
    assert all_false(summary, REQUIRED_FALSE_TERMS)
    assert all_false(summary, CLAY_FLAGS)
    assert summary["summary_flags"]["LocalDefectMonotonicityAttempt"] is True
    assert summary["summary_flags"]["MechanismExhaustionForFullClayNS"] is False
    assert summary["summary_flags"]["NonAxisymmetricVortexStretchingDepletion"] is False
    assert summary["summary_flags"]["PressureNonlocalityClosureForGeneralData"] is False
    assert summary["summary_flags"]["FiniteCriticalProfileTaxonomy"] is False


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def render_markdown(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    lines = [
        "# Sprint 161 Analytic Attempt Boundary",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Generated at: `{summary['generated_at']}`",
        f"- Ordered four-stage route: `{summary['ordered_four_stage_route']}`",
        f"- MechanismExhaustionForFullClayNS=false",
        f"- LocalDefectMonotonicityAttempt: `{summary['LocalDefectMonotonicityAttempt']}`",
        f"- NonAxisymmetricVortexStretchingDepletion=false",
        f"- PressureNonlocalityClosureForGeneralData=false",
        f"- FiniteCriticalProfileTaxonomy=false",
        f"- Clay promotion allowed: `{summary['clay_promotion_allowed']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        "",
        "| stage | row_id | route_stage | status | LocalDefectMonotonicityAttempt |",
        "| ---: | --- | --- | --- | ---: |",
    ]
    for row in rows:
        lines.append(
            "| {stage} | {row_id} | {route_stage} | {status} | {ldm} |".format(
                stage=row["stage"],
                row_id=row["row_id"],
                route_stage=row["route_stage"],
                status=row["status"],
                ldm=row["LocalDefectMonotonicityAttempt"],
            )
        )
    lines.extend(["", "## O/R/C/S/L/P/G/F", ""])
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        lines.append(f"- {key}: {CONTROL_CARD[key]}")
    lines.append("")
    return "\n".join(lines)


def build_manifest(out_dir: Path, summary: dict[str, Any]) -> dict[str, Any]:
    files = {
        "summary": out_dir / f"{CONTRACT}_summary.json",
        "rows_json": out_dir / f"{CONTRACT}_rows.json",
        "rows_csv": out_dir / f"{CONTRACT}_rows.csv",
        "markdown": out_dir / f"{CONTRACT}.md",
        "manifest": out_dir / f"{CONTRACT}_manifest.json",
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
    manifest["manifest_hash"] = stable_hash({k: v for k, v in manifest.items() if k != "manifest_hash"})
    return manifest


def write_outputs(out_dir: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    final_out = out_dir.resolve()
    final_out.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=final_out.parent))
    try:
        write_json(temp_dir / f"{CONTRACT}_rows.json", rows)
        write_csv(temp_dir / f"{CONTRACT}_rows.csv", rows)
        write_json(temp_dir / f"{CONTRACT}_summary.json", summary)
        (temp_dir / f"{CONTRACT}.md").write_text(render_markdown(summary, rows), encoding="utf-8")
        write_json(temp_dir / f"{CONTRACT}_manifest.json", build_manifest(temp_dir, summary))
        if final_out.exists():
            shutil.rmtree(final_out)
        os.replace(temp_dir, final_out)
        write_json(final_out / f"{CONTRACT}_manifest.json", build_manifest(final_out, summary))
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise


def main() -> int:
    args = parse_args()
    rows = build_rows(args.generated_at)
    summary = build_summary(rows, args.generated_at)
    validate(rows, summary)
    output_dir = args.output_dir if args.output_dir.is_absolute() else args.repo_root / args.output_dir
    write_outputs(output_dir, rows, summary)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "out_dir": str(output_dir),
                "validation_passed": summary["validation_passed"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
