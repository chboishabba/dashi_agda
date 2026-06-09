from __future__ import annotations

import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ym_sprint78_floor_entropy_audit.py"


def run_audit(out_dir: Path) -> dict[str, Any]:
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads(
        (out_dir / "ym_sprint78_floor_entropy_summary.json").read_text()
    )


def test_spacetime_floor_crosses_at_k_start_9(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "floor")

    assert math.isclose(summary["source_floor"], 3.079)
    assert math.isclose(summary["p0_at_k8"], 3.057)
    assert math.isclose(summary["p0_at_k9"], 3.124)
    assert summary["p0_k8_below_source_floor"] is True
    assert summary["p0_k9_above_source_floor"] is True
    assert summary["k_start_spacetime_floor"] == 9
    assert summary["k_start_spacetime_floor_is_not_one"] is True
    assert summary["k_start_spacetime_floor_is_not_fifty"] is True
    assert summary["finite_prefix_gap"] == "k=0..8"
    assert summary["nc_absorption_floor_authority_cited"] is True
    assert summary["nc_absorption_floor_authority_assumed"] is True
    assert summary["nc_absorption_floor_authority_proved"] is False
    assert (
        summary["nc_absorption_floor_authority_formal_derivation_in_repo"]
        is False
    )
    assert summary["k_start_under_nc_absorption_floor_authority"] == 0
    assert summary["nc_absorption_floor_authority_gives_k_start_zero"] is True


def test_eta_four_uses_l2_blocking_orientation_convention(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "entropy")

    assert summary["blocking_factor"] == 2
    assert summary["spatial_dimension"] == 3
    assert summary["max_spatial_block_faces"] == 6
    assert summary["temporal_faces_absorbed_into_Tk"] == 2
    assert summary["residual_faces"] == 4
    assert summary["entropy_convention"] == "L2_BLOCKING_ORIENTATIONS"
    assert summary["hypercubic_nearest_neighbour_3d_count"] == 6
    assert summary["hypercubic_nearest_neighbour_3d_accepted_for_eta4"] is False
    assert summary["seiler_2d_minus_2_3d_count"] == 4
    assert summary["seiler_2d_minus_2_matches_repo_generic_4d_eta8"] is False


def test_sprint78_kp_arithmetic_and_promotion_flags(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "kp")

    assert summary["eta_generic_4d"] == 8
    assert summary["fine_lattice_spatial_eta"] == 6
    assert summary["eta_spatial_transfer"] == 4
    assert summary["blocked_l2_spatial_eta"] == 4
    assert math.isclose(summary["q_current"], 0.23178189475262734)
    assert math.isclose(
        summary["fine_lattice_spatial_eta_q"], 1.390691368515764
    )
    assert summary["fine_lattice_spatial_kp_arithmetic_closes"] is False
    assert summary["fine_lattice_eta6_formally_excluded"] is True
    assert math.isclose(summary["eta6_q_threshold"], 1 / 6)
    assert math.isclose(
        summary["q_reduction_needed_for_eta6_percent"], 28.093319435263
    )
    assert math.isclose(summary["spatial_transfer_eta_q"], 0.9271275790105094)
    assert math.isclose(
        summary["blocked_l2_spatial_eta_q"], 0.9271275790105094
    )
    assert math.isclose(summary["generic_4d_eta_q"], 1.8542551580210187)
    assert summary["anisotropic_kp_arithmetic_closes"] is True
    assert summary["blocked_l2_kp_arithmetic_closes"] is True
    assert summary["generic_4d_kp_arithmetic_fails"] is True
    assert summary["effective_action_polymers_spatial_only_proved"] is False
    assert summary["kp_entropy_from_l2_blocking_orientations_proved"] is False
    assert summary["kp_entropy_at_blocked_scale_l2_proved"] is False
    assert summary["polymer_defined_on_blocked_lattice_proved"] is False
    assert (
        summary["temporal_entropy_quotient_halves_generic_4d_count_proved"]
        is False
    )
    assert summary["clay_yang_mills_promoted"] is False
