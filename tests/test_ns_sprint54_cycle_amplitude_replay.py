from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_sprint54_cycle_amplitude_replay_writes_manifest_and_checks(tmp_path: Path) -> None:
    source_dir = tmp_path / "gpu_sprint54"
    source_dir.mkdir()
    source = source_dir / "ns_sprint54_cycle_amplitude_summary.json"
    (source_dir / "ns_stretch_cycle_physical_amplitude.csv").write_text(
        "run,cadence,resolution_N,K,t,cycle_id,packet_mass_amplitude,stretching_amplitude,weighted_stretching_amplitude,signed_stretching_imbalance,physical_small_by_stretch,physical_small_by_mass,sigma_stretching_amplitude_fit,sigma_mass_amplitude_fit,direct_stretch_status,direct_stretch_boundary\n"
        "run0,10,64,4,0.2,cycle_1,1,unavailable,unavailable,unavailable,unavailable,false,unavailable,-1.0,stretch_packet_mask_join_unavailable,boundary\n",
        encoding="utf-8",
    )
    (source_dir / "ns_no2cycle_cadence_comparison.csv").write_text(
        "run,N,cadence,save_every,dt,shell_convention,large_cycle_count,physical_small_cycle_fraction,sigma_packet_cycle,sigma_direct_stretch_cycle,weighted_packet_cycle_amplitude,weighted_stretch_cycle_amplitude,shell_boundary_sensitivity,direct_stretch_status,route_decision\n"
        "run0,64,10,10,0.001,integer,1,0,-1,unavailable,4,unavailable,not_tested_v1,stretch_packet_mask_join_unavailable,NO2CYCLE_UNRESOLVED_NEEDS_HIGHER_N\n",
        encoding="utf-8",
    )
    source.write_text(
        json.dumps(
            {
                "contract": "ns_sprint54_cycle_amplitude_artifact",
                "diagnostic_mode": "sprint54_no2cycle_resolution_cadence_from_material_residue",
                "cycle_amplitude_row_count": 1,
                "cadence_comparison_row_count": 1,
                "no2cycle_candidate_count": 1,
                "no2cycle_proxy_failure_count": 1,
                "physical_large_cycle_count": 1,
                "physical_small_by_mass_count": 0,
                "physical_small_by_mass_fraction": 0.0,
                "physical_amplitude_small_majority": 0.9,
                "small_fraction_by_stretch": 0.0,
                "small_fraction_by_mass": 0.0,
                "sigma_stretching_amplitude": "unavailable",
                "sigma_mass_amplitude": -1.0,
                "cadence_sensitivity": "single_cadence_unresolved",
                "resolution_sensitivity": "single_resolution_unresolved",
                "direct_stretch_status": "stretch_packet_mask_join_unavailable",
                "direct_stretch_boundary": "diagnostic boundary",
                "shell_boundary_sensitivity": "not_tested_v1",
                "does_no2cycle_cadence_gate_close": False,
                "does_no2cycle_resolution_gate_close": False,
                "does_direct_stretch_gate_close": False,
                "does_mass_proxy_gate_close": False,
                "route_decision": "NO2CYCLE_UNRESOLVED_NEEDS_HIGHER_N",
                "no2cycle_aliasing_proved": False,
                "no2cycle_shell_boundary_artifact_proved": False,
                "no2cycle_proxy_overconservative_proved": False,
                "no2cycle_physical_obstruction_proved": False,
                "clay_promotion": False,
                "navier_stokes_promotion": False,
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    out_dir = tmp_path / "replay"
    subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts/ns_diagnostic_harness.py"),
            "--replay-sprint54-cycle-amplitude-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    manifest = json.loads((out_dir / "ns_diagnostic_manifest.json").read_text(encoding="utf-8"))

    assert checks["route_decision"] == "NO2CYCLE_UNRESOLVED_NEEDS_HIGHER_N"
    assert checks["material_parent_lineage_recomputed"] is False
    assert checks["sprint54_cycle_amplitude_replay_promotes"] is False
    assert checks["clay_promotion"] is False
    assert checks["navier_stokes_promotion"] is False
    assert checks["pass"] is False
    assert manifest["receipt_alignment"] == "DASHI.Physics.Closure.ClaySprintFiftyFourNo2CycleResolutionCadenceAuditReceipt"
    assert manifest["outputs"]["stretch_cycle_physical_amplitude_csv"] is not None
    assert manifest["outputs"]["no2cycle_cadence_comparison_csv"] is not None
