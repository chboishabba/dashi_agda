#!/usr/bin/env python3
"""Sprint 133 no-log axisymmetric Biot-Savart scope classifier.

This emitter records exactly what the proposed
NoLogAxisymmetricBiotSavartUniform lemma would and would not promote.  It is
deliberately conservative: even if the lemma is true, the script keeps all
Clay Navier-Stokes promotion flags false because the result closes only a
route-specific axisymmetric subcase, not the universal regularity problem.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint133_no_log_biot_savart_scope"
LEMMA = "NoLogAxisymmetricBiotSavartUniform"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint133_no_log_biot_savart_scope")
SUMMARY_NAME = CONTRACT + "_summary.json"
SUMMARY_CSV_NAME = CONTRACT + "_summary.csv"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"


@dataclass(frozen=True)
class ScopeRow:
    row_id: str
    route_class: str
    regime: str
    before_no_log: str
    after_no_log_if_true: str
    closed_by_no_log_alone: bool
    no_log_relevance: str
    still_open_after_no_log: bool
    remaining_required_lemma: str | None
    remaining_required_proof: str | None
    clay_progress_estimate_percent: int
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    rationale: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        ScopeRow(
            row_id="axs_beta_gt_0_moderate_re",
            route_class="CLASS_AXS",
            regime="AXS beta>0 moderate-Re",
            before_no_log="conditional_obstruction",
            after_no_log_if_true="unconditional_route_obstruction",
            closed_by_no_log_alone=True,
            no_log_relevance="load_bearing_auxiliary_hypothesis",
            still_open_after_no_log=False,
            remaining_required_lemma=None,
            remaining_required_proof=None,
            clay_progress_estimate_percent=0,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "The Sprint130/131 viscous-dominance argument for beta>0 "
                "moderate-Re axisymmetric Hou-Luo data is conditional on the "
                "uniform no-log axisymmetric Biot-Savart bound; proving the "
                "lemma promotes this subcase only."
            ),
        ),
        ScopeRow(
            row_id="axs_beta_eq_0_marginal",
            route_class="CLASS_AXS",
            regime="AXS beta=0 marginal",
            before_no_log="open",
            after_no_log_if_true="still_open",
            closed_by_no_log_alone=False,
            no_log_relevance="insufficient_boundary_regime_input",
            still_open_after_no_log=True,
            remaining_required_lemma="MarginalScalingCaseAnalysis",
            remaining_required_proof="control large-scale shear without concentration",
            clay_progress_estimate_percent=0,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "The viscous/source ratio argument degenerates at beta=0.  "
                "A no-log Biot-Savart estimate does not decide whether "
                "large-scale shear can drive the marginal route."
            ),
        ),
        ScopeRow(
            row_id="axs_beta_gt_0_large_re",
            route_class="CLASS_AXS",
            regime="AXS beta>0 large-Re",
            before_no_log="open_transient_gap",
            after_no_log_if_true="still_open_until_transient_control",
            closed_by_no_log_alone=False,
            no_log_relevance="necessary_but_not_sufficient",
            still_open_after_no_log=True,
            remaining_required_lemma="LargeReAxisymmetricTransientPDEControl",
            remaining_required_proof=(
                "prove full-PDE viscous dominance catches the large-Re "
                "transient before BKM divergence"
            ),
            clay_progress_estimate_percent=0,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "Large-Re ODE models permit fast transient growth before "
                "viscous dominance.  The no-log lemma improves strain control "
                "but does not itself rule out the transient PDE window."
            ),
        ),
        ScopeRow(
            row_id="wbf_v_vortex_stretching",
            route_class="CLASS_WBF",
            regime="WBF-V vortex-stretching",
            before_no_log="conditional_on_separate_regular_input",
            after_no_log_if_true="not_automatically_closed",
            closed_by_no_log_alone=False,
            no_log_relevance="axisymmetric_specific_not_general_wbf",
            still_open_after_no_log=True,
            remaining_required_lemma="UnconditionalBKMWithoutH1Input",
            remaining_required_proof=(
                "remove the H1 or equivalent regularity input in the WBF-V "
                "log-gap obstruction"
            ),
            clay_progress_estimate_percent=0,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "The proposed no-log lemma is an axisymmetric Biot-Savart "
                "statement.  It does not automatically transfer to the WBF-V "
                "vortex-stretching branch, whose named gap is a separate "
                "regularity/criterion issue."
            ),
        ),
        ScopeRow(
            row_id="outside_axs_wbf",
            route_class="OUTSIDE_CLASS_AXS_WBF",
            regime="mechanisms outside AXS/WBF",
            before_no_log="untouched",
            after_no_log_if_true="untouched",
            closed_by_no_log_alone=False,
            no_log_relevance="none",
            still_open_after_no_log=True,
            remaining_required_lemma="MechanismExhaustionTheorem",
            remaining_required_proof=(
                "replace route enumeration with a universal regularity "
                "argument or an exhaustion theorem"
            ),
            clay_progress_estimate_percent=0,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "A route-specific axisymmetric kernel estimate says nothing "
                "about non-axisymmetric, non-WBF, multiscale, or unclassified "
                "BKM-divergent scenarios."
            ),
        ),
        ScopeRow(
            row_id="full_clay_ns",
            route_class="UNIVERSAL_CLAY_NS",
            regime="full Clay Navier-Stokes",
            before_no_log="unsolved",
            after_no_log_if_true="unsolved",
            closed_by_no_log_alone=False,
            no_log_relevance="route_specific_only",
            still_open_after_no_log=True,
            remaining_required_lemma="UniversalRegularityArgument",
            remaining_required_proof=(
                "prove a global continuation estimate, monotone quantity, "
                "or genuine mechanism exhaustion theorem for every smooth "
                "finite-energy datum"
            ),
            clay_progress_estimate_percent=0,
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
            rationale=(
                "The Clay problem is universally quantified over all smooth "
                "finite-energy initial data.  Closing one axisymmetric "
                "subcase does not promote the global theorem."
            ),
        ),
    ]
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    closed = [row for row in rows if row["closed_by_no_log_alone"]]
    still_open = [row for row in rows if row["still_open_after_no_log"]]
    necessary_not_sufficient = [
        row for row in rows if row["no_log_relevance"] == "necessary_but_not_sufficient"
    ]
    untouched = [
        row for row in rows if row["after_no_log_if_true"] == "untouched"
    ]
    return {
        "contract": CONTRACT,
        "lemma_under_scope": LEMMA,
        "row_count": len(rows),
        "closed_by_no_log_alone_count": len(closed),
        "closed_by_no_log_alone": [row["regime"] for row in closed],
        "still_open_after_no_log_count": len(still_open),
        "still_open_after_no_log": [row["regime"] for row in still_open],
        "necessary_but_not_sufficient": [
            row["regime"] for row in necessary_not_sufficient
        ],
        "untouched_by_no_log": [row["regime"] for row in untouched],
        "axs_beta_gt_0_moderate_re_promotes_to_unconditional_if_true": True,
        "axs_beta_eq_0_still_open": True,
        "axs_beta_gt_0_large_re_still_needs_transient_pde_control": True,
        "wbf_v_not_automatically_closed": True,
        "mechanisms_outside_axs_wbf_untouched": True,
        "full_clay_unchanged": True,
        "clay_progress_estimate_percent": 0,
        "full_clay_ns_solved": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "complete Sprint133 no-log Biot-Savart scope emitted; lemma would "
            "promote only the AXS beta>0 moderate-Re subcase and does not "
            "change full Clay status"
        ),
        "control_card": {
            "O": "Worker 3 owns only scripts/ns_sprint133_no_log_biot_savart_scope.py and outputs/ns_sprint133_no_log_biot_savart_scope/",
            "R": "distinguish the exact proof scope of NoLogAxisymmetricBiotSavartUniform",
            "C": "deterministic Python emitter writes JSON and CSV scope artifacts",
            "S": "one AXS moderate-Re subcase promotes if the lemma is true; marginal, large-Re, WBF-V, outside-class, and full Clay surfaces remain open",
            "L": "subcase conditional -> subcase unconditional is strictly below global NS promotion",
            "P": "record zero Clay progress estimate and retain all Clay flags false",
            "G": "exit code 0 requires complete artifacts and no full-Clay promotion",
            "F": "remaining deficit is transient PDE control plus marginal analysis plus universal regularity/exhaustion",
        },
    }


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def csv_scalar(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, (list, dict)):
        return json.dumps(value, sort_keys=True)
    return str(value)


def write_rows_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = list(rows[0].keys()) if rows else []
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({key: csv_scalar(value) for key, value in row.items()})


def write_summary_csv(path: Path, summary: dict[str, Any]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=("key", "value"))
        writer.writeheader()
        for key in sorted(summary):
            writer.writerow({"key": key, "value": csv_scalar(summary[key])})


def assert_summary_invariants(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    if summary["clay_progress_estimate_percent"] != 0:
        raise AssertionError("Clay progress estimate must remain exactly zero")
    if summary["full_clay_ns_solved"] or summary["clay_navier_stokes_promoted"]:
        raise AssertionError("Clay promotion flags must remain false")
    if not summary["complete"] or summary["exit_code"] != 0:
        raise AssertionError("completed scope classifier must exit 0")
    if len([row for row in rows if row["closed_by_no_log_alone"]]) != 1:
        raise AssertionError("No-log lemma must close exactly one listed subcase")
    for row in rows:
        if row["clay_progress_estimate_percent"] != 0:
            raise AssertionError(f"row {row['row_id']} promoted Clay progress")
        if row["full_clay_ns_solved"] or row["clay_navier_stokes_promoted"]:
            raise AssertionError(f"row {row['row_id']} promoted Clay")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    assert_summary_invariants(summary, rows)

    write_json(out_dir / SUMMARY_NAME, summary)
    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_summary_csv(out_dir / SUMMARY_CSV_NAME, summary)
    write_rows_csv(out_dir / ROWS_CSV_NAME, rows)

    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "lemma_under_scope": LEMMA,
                "clay_progress_estimate_percent": summary[
                    "clay_progress_estimate_percent"
                ],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "clay_navier_stokes_promoted": summary[
                    "clay_navier_stokes_promoted"
                ],
                "complete": summary["complete"],
                "exit_code": summary["exit_code"],
            },
            sort_keys=True,
        )
    )
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
