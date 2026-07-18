from __future__ import annotations

from pathlib import Path
import sys

import pytest


SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_shell_angle_weighted_schur_audit import (  # noqa: E402
    audit_receipt,
    build_coarse_kernel,
    minimax_summary,
    weighted_schur_constants,
)


def _groups() -> list[dict[str, float | int]]:
    return [
        {
            "p_shell_offset": 0,
            "q_shell_offset": 0,
            "angle_bin": 0,
            "gross_activity": 0.50,
            "gross_activity_fraction": 0.50,
        },
        {
            "p_shell_offset": 1,
            "q_shell_offset": 0,
            "angle_bin": 0,
            "gross_activity": 0.25,
            "gross_activity_fraction": 0.25,
        },
        {
            "p_shell_offset": 1,
            "q_shell_offset": 1,
            "angle_bin": 1,
            "gross_activity": 0.25,
            "gross_activity_fraction": 0.25,
        },
    ]


def test_unweighted_constants_match_finite_matrix() -> None:
    rows, columns, kernel = build_coarse_kernel(_groups())
    result = weighted_schur_constants(rows, columns, kernel, 0.0, 0.0)
    assert result["row_constant"] == pytest.approx(0.5)
    assert result["column_constant"] == pytest.approx(0.75)
    assert result["product_constant"] == pytest.approx(0.375)
    assert result["operator_constant_sqrt_product"] == pytest.approx(0.375 ** 0.5)


def test_receipt_and_minimax_remain_fail_closed() -> None:
    receipt = {
        "source_state": "synthetic.npz",
        "target_shell": 2,
        "full_packet_signed_rate": -0.1,
        "full_packet_gross_activity": 1.0,
        "coarse_shell_angle_groups": _groups(),
    }
    audit = audit_receipt(receipt, (0.0, 1.0), (0.0, 1.0))
    assert audit["formal_pair_incidence_kernel_match_proved"] is False
    assert audit["c_err_determined"] is False
    assert audit["promoted"] is False

    summary = minimax_summary([audit])
    assert "best_minimax_weight" in summary
    assert summary["best_minimax_weight"]["worst_product_constant"] >= 0.0
