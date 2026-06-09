from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_sprint56_packet_local_action_replay_writes_manifest_and_checks(tmp_path: Path) -> None:
    source_dir = tmp_path / "gpu_sprint56"
    source_dir.mkdir()
    source = source_dir / "ns_sprint56_packet_local_action_summary.json"
    (source_dir / "ns_packet_local_lagrangian_action.csv").write_text(
        "run,material_lineage_id,packet_id,K,t_start,t_end,step_count,A_signed,A_positive,A_negative,A_net,direction_change_integral,sign_flip_count,weighted_A_positive,mass_cycle_amplitude,direct_stretch_cycle_amplitude,packet_local_mask_available,lagrangian_trit_after_integration,is_dangerous,action_small,cadence,N,packet_confidence_min,packet_confidence_mean,packet_local_status,action_boundary\n"
        "run0,lineage0,K4_cell1,4,0.1,0.2,2,0.01,0.02,0.01,0.01,0.3,1,0.08,10,2,true,green,false,true,10,64,0.5,0.5,packet_local_mask_reconstructed_from_sprint49_packet_id_geometry,boundary\n",
        encoding="utf-8",
    )
    (source_dir / "ns_packet_local_action_hysteresis.csv").write_text(
        "run,material_lineage_id,time,dt,K,packet_id,instant_state,packet_local_alpha,increment_signed_action,cumulative_signed_action,cumulative_positive_action,cumulative_negative_action,direction_change_increment,direction_change_integral,instant_color_flip_count,hysteresis_color_state,packet_local_mask_available,packet_local_status\n"
        "run0,lineage0,0.1,0.01,4,K4_cell1,plus,1,0.01,0.01,0.01,0,0,0,0,green,true,packet_local_mask_reconstructed_from_sprint49_packet_id_geometry\n",
        encoding="utf-8",
    )
    (source_dir / "ns_direction_change_separation.csv").write_text(
        "run,material_lineage_id,K,t_start,t_end,sign_flip_count,direction_change_integral,A_positive,weighted_A_positive,redirection_without_overwhelm,packet_local_mask_available\n"
        "run0,lineage0,4,0.1,0.2,1,0.3,0.02,0.08,true,true\n",
        encoding="utf-8",
    )
    (source_dir / "ns_packet_local_action_by_shell.csv").write_text(
        "K,lineage_count,A_positive_total,weighted_A_positive_total,direction_change_integral_total,dangerous_lineage_count,action_small_fraction\n"
        "4,1,0.02,0.08,0.3,0,1\n",
        encoding="utf-8",
    )
    source.write_text(
        json.dumps(
            {
                "contract": "ns_sprint56_packet_local_action_artifact",
                "diagnostic_mode": "sprint56_packet_local_accumulated_stretch_action",
                "packet_local_action_row_count": 1,
                "packet_local_hysteresis_row_count": 1,
                "direction_change_row_count": 1,
                "action_summary_row_count": 1,
                "packet_local_available_lineage_count": 1,
                "packet_local_available_fraction": 1.0,
                "action_threshold": 0.05,
                "action_small_majority": 0.9,
                "redirection_threshold": 0.25,
                "A_positive_total": 0.02,
                "weighted_A_positive_total": 0.08,
                "direction_change_integral_total": 0.3,
                "redirection_without_overwhelm_count": 1,
                "action_small_fraction": 1.0,
                "dangerous_lineage_count": 0,
                "sigma_packet_local_action_fit": 0.0,
                "does_packet_local_action_gate_close": True,
                "does_packet_local_action_summability_gate_close": False,
                "packet_local_mask_reconstruction_available": True,
                "packet_local_action_gate_proved": False,
                "weighted_packet_local_action_summability_proved": False,
                "direction_change_separation_proved": False,
                "physical_bridge_proved": False,
                "stretch_absorption_proved": False,
                "no_finite_time_blowup_proved": False,
                "route_decision": "PACKET_LOCAL_REDIRECTION_WITHOUT_OVERWHELM_DIAGNOSTIC",
                "packet_local_boundary": "diagnostic boundary",
                "packet_local_status": "packet_local_mask_reconstructed_from_sprint49_packet_id_geometry",
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
            "--replay-sprint56-packet-local-action-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    manifest = json.loads((out_dir / "ns_diagnostic_manifest.json").read_text(encoding="utf-8"))

    assert checks["route_decision"] == "PACKET_LOCAL_REDIRECTION_WITHOUT_OVERWHELM_DIAGNOSTIC"
    assert checks["sprint56_packet_local_action_replay_promotes"] is False
    assert checks["packet_local_masks_loaded"] is False
    assert checks["clay_promotion"] is False
    assert checks["navier_stokes_promotion"] is False
    assert checks["pass"] is False
    assert manifest["receipt_alignment"] == "DASHI.Physics.Closure.ClaySprintFiftySixPacketLocalStretchActionAuditReceipt"
    assert manifest["outputs"]["packet_local_lagrangian_action_csv"] is not None
    assert manifest["outputs"]["direction_change_separation_csv"] is not None
    assert manifest["clay_promotion"] is False
    assert manifest["navier_stokes_promotion"] is False
