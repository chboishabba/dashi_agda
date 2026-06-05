from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/ym_sprint86_blocked_action_transfer_kernel_audit.py")


def run_audit(tmp_path: Path) -> tuple[Path, dict]:
    out_dir = tmp_path / "ym_sprint86"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )
    summary = json.loads(
        (out_dir / "ym_sprint86_blocked_action_transfer_kernel_summary.json").read_text()
    )
    return out_dir, summary


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def test_ym_sprint86_outputs_and_schema(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "ym_sprint86_blocked_action_transfer_kernel_audit"
    assert (
        out_dir / "ym_sprint86_blocked_action_transfer_kernel_source_surface_table.csv"
    ).exists()
    assert (
        out_dir / "ym_sprint86_blocked_action_transfer_kernel_gate_table.csv"
    ).exists()
    assert (
        out_dir / "ym_sprint86_blocked_action_transfer_kernel_summary.json"
    ).exists()

    source_rows = read_csv(
        out_dir / "ym_sprint86_blocked_action_transfer_kernel_source_surface_table.csv"
    )
    gate_rows = read_csv(
        out_dir / "ym_sprint86_blocked_action_transfer_kernel_gate_table.csv"
    )

    assert {row["surface_name"] for row in source_rows} == {
        "Sprint86BlockedActionTransferKernel",
        "Sprint87ExactBlockedActionTransferResidualSum",
        "Sprint85TemporalTransferSpatialBlocking",
        "StrongGateBCarriers",
        "TemporalTermsAbsorbedReceipt",
        "SpatialOnlyBlockingTemporalLinks",
    }
    assert {row["gate_name"] for row in gate_rows} >= {
        "ActionTermSectorTagComplete",
        "MixedPlaquettesAbsorbedIntoTransfer",
        "StrongTransferResidualDisjointness",
        "SpatialBlockingCreatesNoNewCrossTerms",
        "ExactBlockedActionTransferResidualSum",
        "BlockedActionSeparatesTransferKernel",
        "ClayYangMillsPromoted",
    }


def test_ym_sprint86_records_open_blocked_action_route(tmp_path: Path) -> None:
    _out_dir, summary = run_audit(tmp_path)

    assert summary["complete"] is False
    assert (
        summary["route_decision"]
        == "YM_SPRINT86_BLOCKED_ACTION_TRANSFER_KERNEL_OPEN"
    )
    assert summary["next_required_gate"] == "ExactBlockedActionTransferResidualSum"
    assert summary["blocked_action_transfer_kernel_required_inputs"] == [
        "ActionTermSectorTagComplete",
        "MixedPlaquettesAbsorbedIntoTransfer",
        "StrongTransferResidualDisjointness",
        "SpatialBlockingCreatesNoNewCrossTerms",
        "ExactBlockedActionTransferResidualSum",
    ]
    assert summary["exact_blocked_action_transfer_residual_sum_required_inputs"] == [
        "BlockedActionTermEnumeration",
        "TransferKernelActionTermProjection",
        "SpatialResidualActionTermProjection",
        "TransferResidualProjectionDisjoint",
        "ProjectionUnionCoversBlockedAction",
        "ActionSumRespectsProjectionUnion",
    ]


def test_ym_sprint86_surfaces_present_and_flags_fail_closed(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    rows = read_csv(
        out_dir / "ym_sprint86_blocked_action_transfer_kernel_source_surface_table.csv"
    )

    assert summary["sprint86_blocked_action_transfer_kernel_surface"] is True
    assert summary["sprint87_exact_blocked_action_transfer_residual_sum_surface"] is True
    assert summary["temporal_transfer_spatial_blocking_surface"] is True
    assert summary["strong_gate_b_carrier_surface"] is True
    assert summary["temporal_terms_absorbed_surface"] is True
    assert summary["spatial_only_blocking_temporal_links_surface"] is True
    assert summary["all_required_source_surfaces_present"] is True
    assert all(row["present_in_repo"] == "True" for row in rows)

    assert summary["action_term_sector_tag_complete_derived_in_repo"] is True
    assert summary["mixed_plaquettes_absorbed_into_transfer_surface_available"] is True
    assert summary["strong_transfer_residual_disjointness_derived_in_repo"] is True
    assert summary["spatial_blocking_creates_no_new_cross_terms_derived_in_repo"] is True
    assert summary["exact_blocked_action_transfer_residual_sum_derived_in_repo"] is False
    assert summary["blocked_action_separates_transfer_kernel_derived_in_repo"] is False
    assert (
        summary[
            "full_temporal_transfer_matrix_spatial_blocking_compatibility_derived_in_repo"
        ]
        is False
    )
    assert summary["clay_yang_mills_promoted"] is False
    assert summary["clay_promotion_recorded_false"] is True


def test_ym_sprint86_gate_rows_preserve_no_promotion(tmp_path: Path) -> None:
    out_dir, _summary = run_audit(tmp_path)
    gate_rows = read_csv(
        out_dir / "ym_sprint86_blocked_action_transfer_kernel_gate_table.csv"
    )

    assert all(row["clay_promotion"] == "False" for row in gate_rows)
    clay_gate = next(row for row in gate_rows if row["gate_name"] == "ClayYangMillsPromoted")
    assert clay_gate["status"] == "FALSE_NO_PROMOTION"
