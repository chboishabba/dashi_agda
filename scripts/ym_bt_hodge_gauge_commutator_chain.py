#!/usr/bin/env python3
"""Emit the YM/BT finite Hodge gauge-commutator compatibility chain."""

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


CONTRACT = "ym_bt_hodge_gauge_commutator_chain"
OUT_DIR_DEFAULT = Path("outputs") / CONTRACT
SUMMARY_NAME = f"{CONTRACT}_summary.json"
ROWS_JSON_NAME = f"{CONTRACT}_rows.json"
ROWS_CSV_NAME = f"{CONTRACT}_rows.csv"
MARKDOWN_NAME = f"{CONTRACT}.md"
MANIFEST_NAME = f"{CONTRACT}_manifest.json"
SPRINT = 166
WORKER = 4
DEFAULT_GENERATED_AT = "1970-01-01T00:00:00Z"

DEFECT = "[d_A,*]F_A = d_A(*F_A) - *(d_A F_A)"

THEOREM_AND_PROMOTION_FALSE_FLAGS = (
    "FiniteYMHodgeVariationTheoremProvedHere",
    "BTHodgeGaugeCompatibilityTheoremProvedHere",
    "BTMetricDefectVanishingTheoremProvedHere",
    "FiniteYangMillsEquationDerivedHere",
    "FiniteHamiltonianConstructedHere",
    "SpectralGapProvedHere",
    "UniformLowerBoundProvedHere",
    "ContinuumTransferProvedHere",
    "ClayYangMillsPromoted",
    "clayYangMillsPromoted",
    "ClaySubmissionReady",
    "promotion_allowed",
    "promotionAllowed",
    "theorem_promotion_allowed",
)

OPEN_PATH_FLAGS = (
    "FiniteYMEquationPathOpen",
    "HamiltonianPathOpen",
    "SpectralGapPathOpen",
    "UniformLowerBoundPathOpen",
    "ContinuumTransferPathOpen",
)

CONTROL_CARD = {
    "O": "Worker 4 owns the Sprint166 YM/BT finite Hodge gauge-commutator chain emitter.",
    "R": (
        "Normalize the finite Hodge variation chain and isolate [d_A,*]F_A as "
        "the compatibility defect/leakage term before any YM promotion."
    ),
    "C": "One stdlib Python script writes normalized JSON, CSV, Markdown, and manifest outputs.",
    "S": (
        "Finite Hodge/IBP gives a clean variational surface; Yang-Mills needs "
        "gauge-Hodge compatibility, not just Maxwell-style d dagger equals star-d-star."
    ),
    "L": (
        "BT metric selected so star is covariantly constant on admissible fields "
        "implies [d_A,*]F_A vanishes; outside that lane the commutator is leakage."
    ),
    "P": "Use the artifact as a fail-closed compatibility chain and obligation ledger.",
    "G": (
        "Promotion stays blocked until finite YM equation, Hamiltonian, spectral "
        "gap, uniform lower bound, and continuum transfer are closed."
    ),
    "F": "No theorem, Clay promotion, spectral gap, or continuum transfer is asserted here.",
}

CHAIN_ROWS: tuple[dict[str, Any], ...] = (
    {
        "row_id": "R01",
        "stage": "finite_hodge_variation",
        "object": "FiniteHodgeStarAndInnerProduct",
        "status": "NORMALIZED_SURFACE",
        "claim": (
            "A finite cell/cochain Hodge star and inner product make variation "
            "of the curvature energy meaningful after finite integration by parts."
        ),
        "compatibility_defect": DEFECT,
        "defect_role": "not yet evaluated",
        "bt_metric_condition": "Choose a positive finite BT metric and star on the selected admissible complex.",
        "vanishing_condition": "No vanishing claim at this stage.",
        "remaining_path": "Prove the selected star is compatible with gauge transport on admissible fields.",
        "maxwell_special_case": "",
    },
    {
        "row_id": "R02",
        "stage": "finite_hodge_ibp",
        "object": "FiniteAdjointAfterIBP",
        "status": "NORMALIZED_SURFACE",
        "claim": (
            "Finite IBP identifies the adjoint surface d dagger through the "
            "chosen finite star and boundary convention."
        ),
        "compatibility_defect": DEFECT,
        "defect_role": "boundary and Hodge-choice leakage is visible before gauge covariance is imposed",
        "bt_metric_condition": "Boundary pairings and cell weights must match the BT metric selection.",
        "vanishing_condition": "Boundary leakage vanishes only under the selected closed/admissible boundary lane.",
        "remaining_path": "Separate ordinary finite adjointness from gauge-covariant adjointness.",
        "maxwell_special_case": "For abelian Maxwell, after finite Hodge/IBP, d dagger = +/- * d * up to the chosen degree/sign convention.",
    },
    {
        "row_id": "R03",
        "stage": "gauge_commutator_defect",
        "object": "GaugeHodgeCommutatorLeakage",
        "status": "COMPATIBILITY_DEFECT_ISOLATED",
        "claim": (
            "For nonabelian YM, the finite variational chain contains the "
            "extra compatibility defect [d_A,*]F_A; it measures failure of "
            "the Hodge star to commute with covariant differentiation on curvature."
        ),
        "compatibility_defect": DEFECT,
        "defect_role": "leakage term in the attempted finite YM Euler-Lagrange reduction",
        "bt_metric_condition": (
            "The BT metric must be selected so the discrete star is parallel "
            "with respect to admissible gauge transport on the curvature support."
        ),
        "vanishing_condition": "If d_A F_A = 0 and d_A(*F_A) = *(d_A F_A) on admissible fields, then [d_A,*]F_A = 0.",
        "remaining_path": "Prove the commutator estimate or exact vanishing in the finite BT model.",
        "maxwell_special_case": "In abelian Maxwell, d_A=d and the clean d dagger = +/- * d * route has no nonabelian commutator leakage.",
    },
    {
        "row_id": "R04",
        "stage": "bt_metric_admissibility",
        "object": "SelectedBTMetricCompatibilityLane",
        "status": "CONDITIONAL_VANISHING_CRITERION",
        "claim": (
            "A selected BT metric can make the defect vanish for admissible "
            "fields when cell weights, orientations, gauge parallel transport, "
            "and boundary conditions make star covariantly constant on F_A."
        ),
        "compatibility_defect": DEFECT,
        "defect_role": "zero only inside the selected admissible compatibility lane",
        "bt_metric_condition": (
            "Metric weights are gauge-invariant on stabilizers, the star maps "
            "admissible curvature cochains to admissible dual cochains, and "
            "parallel transport preserves the star pairing."
        ),
        "vanishing_condition": (
            "For admissible A and F_A satisfying finite Bianchi d_A F_A = 0, "
            "covariant-star compatibility gives [d_A,*]F_A = 0."
        ),
        "remaining_path": "Formalize admissibility and prove the BT metric compatibility lemma without hidden continuum assumptions.",
        "maxwell_special_case": "",
    },
    {
        "row_id": "R05",
        "stage": "finite_ym_equation_path",
        "object": "FiniteYangMillsEquationObligation",
        "status": "OPEN_FAIL_CLOSED",
        "claim": (
            "Once the defect vanishes or is absorbed, the finite YM equation "
            "must still be derived as the exact finite Euler-Lagrange equation."
        ),
        "compatibility_defect": DEFECT,
        "defect_role": "unclosed leakage blocks promotion from variational surface to finite YM equation",
        "bt_metric_condition": "The selected BT metric must support a closed adjoint and admissible variation class.",
        "vanishing_condition": "Not promoted; conditional vanishing is only an input obligation.",
        "remaining_path": "Close finite YM equation, Hamiltonian construction, spectral gap, uniform lower bound, and continuum transfer.",
        "maxwell_special_case": "",
    },
    {
        "row_id": "R06",
        "stage": "downstream_gap_transfer_path",
        "object": "HamiltonianSpectralGapLowerBoundContinuumTransfer",
        "status": "OPEN_FAIL_CLOSED",
        "claim": (
            "The compatibility chain is upstream of the Clay-scale route; it "
            "does not by itself construct the Hamiltonian, prove a spectral gap, "
            "supply a uniform lower bound, or transfer to the continuum."
        ),
        "compatibility_defect": DEFECT,
        "defect_role": "resolved defect is necessary but not sufficient for downstream gap transfer",
        "bt_metric_condition": "Uniformity in the finite BT metric family must survive refinement and gauge quotienting.",
        "vanishing_condition": "No global theorem here.",
        "remaining_path": (
            "Build the finite Hamiltonian, prove positivity and nonzero uniform "
            "lower bound, establish spectral convergence, then transfer to the continuum YM measure/theory."
        ),
        "maxwell_special_case": "",
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


def false_flags() -> dict[str, bool]:
    return {name: False for name in THEOREM_AND_PROMOTION_FALSE_FLAGS}


def true_open_flags() -> dict[str, bool]:
    return {name: True for name in OPEN_PATH_FLAGS}


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in CHAIN_ROWS:
        row = {
            "contract": CONTRACT,
            "sprint": SPRINT,
            "worker": WORKER,
            "closed": item["status"] in {"NORMALIZED_SURFACE", "COMPATIBILITY_DEFECT_ISOLATED", "CONDITIONAL_VANISHING_CRITERION"},
            "fail_closed": item["status"].endswith("FAIL_CLOSED"),
            "closure_flags_fail_closed": True,
            "authority_flags_fail_closed": True,
            **item,
            **true_open_flags(),
            **false_flags(),
        }
        row["row_hash"] = stable_hash({key: value for key, value in row.items() if key != "row_hash"})
        rows.append(row)
    return rows


def named_flags_have_value(record: dict[str, Any], names: tuple[str, ...], value: bool) -> bool:
    return all(record.get(name) is value for name in names)


def rows_named_flags_have_value(rows: list[dict[str, Any]], names: tuple[str, ...], value: bool) -> bool:
    return all(named_flags_have_value(row, names, value) for row in rows)


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> bool:
    return (
        summary["row_count"] == len(CHAIN_ROWS)
        and summary["expected_rows_present"] is True
        and summary["compatibility_defect"] == DEFECT
        and summary["commutator_leakage_isolated"] is True
        and summary["bt_metric_conditional_vanishing_recorded"] is True
        and summary["maxwell_special_case_recorded"] is True
        and summary["row_closure_guards_fail_closed"] is True
        and summary["summary_closure_guards_fail_closed"] is True
        and summary["open_path_flags_true"] is True
        and all(row["promotion_allowed"] is False for row in rows)
    )


def build_summary(repo_root: Path, out_dir: Path, generated_at: str, rows: list[dict[str, Any]]) -> dict[str, Any]:
    row_ids = [row["row_id"] for row in rows]
    expected_row_ids = [row["row_id"] for row in CHAIN_ROWS]
    summary: dict[str, Any] = {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "worker": WORKER,
        "generated_at": generated_at,
        "repo_root": str(repo_root),
        "out_dir": str(out_dir),
        "decision": "fail_closed_compatibility_chain_no_promotion",
        "row_count": len(rows),
        "row_ids": row_ids,
        "expected_rows_present": row_ids == expected_row_ids,
        "compatibility_defect": DEFECT,
        "commutator_leakage_isolated": True,
        "bt_metric_conditional_vanishing_recorded": True,
        "maxwell_special_case_recorded": any("d dagger = +/- * d *" in row["maxwell_special_case"] for row in rows),
        "finite_hodge_variation_chain": [
            "finite_hodge_variation",
            "finite_hodge_ibp",
            "gauge_commutator_defect",
            "bt_metric_admissibility",
            "finite_ym_equation_path",
            "downstream_gap_transfer_path",
        ],
        "selected_bt_metric_defect_vanishes_when": (
            "The finite BT metric/star is covariantly constant on admissible "
            "curvature cochains, preserves boundary/admissibility conditions, "
            "and the finite Bianchi identity d_A F_A = 0 is available."
        ),
        "remaining_path": (
            "Close the finite YM equation, construct the finite Hamiltonian, "
            "prove a spectral gap, prove a uniform lower bound across the finite "
            "BT family, and transfer the lower bound to the continuum."
        ),
        "rows": rows,
        "control_card": CONTROL_CARD,
        **true_open_flags(),
        **false_flags(),
    }
    summary["row_closure_guards_fail_closed"] = rows_named_flags_have_value(
        rows, THEOREM_AND_PROMOTION_FALSE_FLAGS, False
    )
    summary["summary_closure_guards_fail_closed"] = named_flags_have_value(
        summary, THEOREM_AND_PROMOTION_FALSE_FLAGS, False
    )
    summary["open_path_flags_true"] = named_flags_have_value(summary, OPEN_PATH_FLAGS, True) and rows_named_flags_have_value(
        rows, OPEN_PATH_FLAGS, True
    )
    summary["validation_passed"] = validate(summary, rows)
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
        "# YM/BT Hodge Gauge Commutator Chain",
        "",
        f"- Decision: `{summary['decision']}`",
        f"- Compatibility defect: `{summary['compatibility_defect']}`",
        f"- Validation passed: `{summary['validation_passed']}`",
        f"- Closure guards fail closed: `{summary['summary_closure_guards_fail_closed']}`",
        "",
        "## Chain",
        "",
        "| row | stage | status | defect role | remaining path |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in summary["rows"]:
        lines.append(
            f"| {row['row_id']} | {row['stage']} | {row['status']} | {row['defect_role']} | {row['remaining_path']} |"
        )
    lines.extend(
        [
            "",
            "## BT Metric Vanishing Criterion",
            "",
            summary["selected_bt_metric_defect_vanishes_when"],
            "",
            "## Maxwell Special Case",
            "",
            (
                "After finite Hodge/IBP, abelian Maxwell has the clean adjoint "
                "identity `d dagger = +/- * d *` up to the selected degree/sign "
                "convention. The nonabelian YM route must separately account "
                "for `[d_A,*]F_A`."
            ),
            "",
            "## Remaining Path",
            "",
            summary["remaining_path"],
            "",
            "## O/R/C/S/L/P/G/F",
            "",
        ]
    )
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
        "repo_root": summary["repo_root"],
        "decision": summary["decision"],
        "validation_passed": summary["validation_passed"],
        "closure_guards_fail_closed": summary["summary_closure_guards_fail_closed"],
        "files": {
            key: {"path": str(path), "exists": path.exists(), "sha256": file_sha256(path)}
            for key, path in files.items()
        },
    }
    manifest["manifest_hash"] = stable_hash({key: value for key, value in manifest.items() if key != "manifest_hash"})
    return manifest


def resolve_path(path: Path, repo_root: Path) -> Path:
    return path if path.is_absolute() else repo_root / path


def write_outputs(repo_root: Path, out_dir_arg: Path, generated_at: str) -> tuple[Path, dict[str, Any]]:
    out_dir = resolve_path(out_dir_arg, repo_root)
    rows = build_rows()
    summary = build_summary(repo_root, out_dir, generated_at, rows)
    out_dir.parent.mkdir(parents=True, exist_ok=True)
    temp_dir = Path(tempfile.mkdtemp(prefix=f".{CONTRACT}.", dir=out_dir.parent))
    try:
        write_json(temp_dir / ROWS_JSON_NAME, rows)
        write_csv(temp_dir / ROWS_CSV_NAME, rows)
        write_json(temp_dir / SUMMARY_NAME, summary)
        (temp_dir / MARKDOWN_NAME).write_text(render_markdown(summary), encoding="utf-8")
        write_json(temp_dir / MANIFEST_NAME, build_manifest(temp_dir, summary))
        if out_dir.exists():
            shutil.rmtree(out_dir)
        os.replace(temp_dir, out_dir)
        write_json(out_dir / MANIFEST_NAME, build_manifest(out_dir, summary))
    except Exception:
        shutil.rmtree(temp_dir, ignore_errors=True)
        raise
    return out_dir, summary


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir, summary = write_outputs(repo_root, args.out_dir, args.generated_at)
    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "out_dir": str(out_dir),
                "summary": str(out_dir / SUMMARY_NAME),
                "closure_guards_fail_closed": summary["summary_closure_guards_fail_closed"],
                "validation_passed": summary["validation_passed"],
            },
            sort_keys=True,
        )
    )
    return 0 if summary["validation_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
