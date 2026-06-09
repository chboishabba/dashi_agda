from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "scripts"
    / "ym_sprint103_continuum_mass_gap_obligation7_audit.py"
)


def run_script(tmp_path: Path) -> dict:
    out_dir = tmp_path / "ym_sprint103_continuum_mass_gap_obligation7"
    subprocess.run(
        ["python", str(SCRIPT), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=True,
    )
    summary = out_dir / "ym_sprint103_continuum_mass_gap_obligation7_summary.json"
    return json.loads(summary.read_text())


def test_sprint103_closes_only_continuum_mass_gap_obligation7(
    tmp_path: Path,
) -> None:
    summary = run_script(tmp_path)

    assert summary["implemented_obligation"] == 7
    assert summary["implemented_obligation_name"] == "ContinuumLimitMassGap"
    assert summary["continuum_mass_gap_obligation7_closed_in_repo"] is True
    assert summary["only_continuum_mass_gap_obligation7_closed"] is True
    assert (
        summary["nontrivial_4d_su3_yang_mills_measure_derived_in_repo"]
        is False
    )
    assert summary["clay_statement_boundary_discharged"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint103_uses_user_provided_rg_transfer_scale_argument(
    tmp_path: Path,
) -> None:
    summary = run_script(tmp_path)

    assert summary["rg_generated_mass_term"] is True
    assert summary["transfer_gap_tracks_effective_mass"] is True
    assert summary["rg_invariant_physical_scale"] is True
    assert "RGGeneratedMassTerm" in summary["proof_argument"]
    assert "TransferGapTracksEffectiveMass" in summary["proof_argument"]
    assert "RGInvariantPhysicalScale" in summary["proof_argument"]
    assert "=>" in summary["proof_argument"]


def test_sprint103_derives_positive_scaled_gap_limit(tmp_path: Path) -> None:
    summary = run_script(tmp_path)

    statement = summary["continuum_mass_gap_limit_statement"]
    assert summary["positive_continuum_mass_gap_limit"] is True
    assert "lim_{a->0}" in statement
    assert "gap(T(a))*block_size(a)" in statement
    assert "m_phys > 0" in statement
    assert summary["empty_data_skeletons_introduced"] is False
    assert (
        summary["route_decision"]
        == "SPRINT103_CLOSES_CONTINUUM_MASS_GAP_OBLIGATION7_ONLY_NO_CLAY_PROMOTION"
    )
