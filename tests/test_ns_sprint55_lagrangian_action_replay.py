from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_sprint55_lagrangian_action_replay_writes_manifest_and_checks(tmp_path: Path) -> None:
    source_dir = tmp_path / "gpu_sprint55"
    source_dir.mkdir()
    source = source_dir / "ns_sprint55_lagrangian_action_summary.json"
    (source_dir / "ns_lagrangian_stretch_action.csv").write_text(
        "run,material_lineage_id,packet_id,K,t_start,t_end,step_count,sign_flip_count,signed_stretch_integral,positive_stretch_integral,negative_stretch_integral,normalized_stretch_action,weighted_A_positive,mass_amplitude_proxy,direct_stretch_amplitude,lagrangian_label,is_dangerous,action_small,cadence,N,packet_confidence_min,packet_confidence_mean,direct_stretch_status,action_boundary\n"
        "run0,lineage0,p,4,0.1,0.2,2,1,0.01,0.02,0.01,0.01,0.08,10,unavailable,green,false,true,10,64,0.5,0.5,source_truth_or_direct_stretch_unavailable,boundary\n",
        encoding="utf-8",
    )
    (source_dir / "ns_packet_action_hysteresis.csv").write_text(
        "run,material_lineage_id,time,dt,K,packet_id,instant_state,instant_alpha,increment_signed_action,cumulative_signed_action,cumulative_positive_action,cumulative_negative_action,instant_color_flip_count,hysteresis_color_state,direct_stretch_status\n"
        "run0,lineage0,0.1,0.01,4,p,plus,unavailable,unavailable,0,0,0,0,green,source_truth_or_direct_stretch_unavailable\n",
        encoding="utf-8",
    )
    (source_dir / "ns_lagrangian_action_by_shell.csv").write_text(
        "K,lineage_count,signed_action_total,positive_action_total,negative_action_total,weighted_positive_action_total,dangerous_lineage_count,action_small_fraction\n"
        "4,1,0.01,0.02,0.01,0.08,0,1\n",
        encoding="utf-8",
    )
    source.write_text(
        json.dumps(
            {
                "contract": "ns_sprint55_lagrangian_action_artifact",
                "diagnostic_mode": "sprint55_lagrangian_accumulated_stretch_action",
                "lagrangian_action_row_count": 1,
                "hysteresis_row_count": 1,
                "action_summary_row_count": 1,
                "material_lineage_count": 1,
                "direct_stretch_available_lineage_count": 0,
                "action_threshold": 0.05,
                "action_small_majority": 0.9,
                "positive_action_total": 0.02,
                "weighted_positive_action_total": 0.08,
                "action_small_fraction": 1.0,
                "dangerous_lineage_count": 0,
                "sigma_action_fit": 0.0,
                "does_lagrangian_action_gate_close": True,
                "does_lagrangian_action_summability_gate_close": False,
                "lagrangian_action_gate_proved": False,
                "weighted_action_summability_proved": False,
                "packet_local_stretch_action_available": False,
                "packet_local_stretch_action_proved": False,
                "color_string_proxy_demoted": True,
                "physical_bridge_proved": False,
                "stretch_absorption_proved": False,
                "no_finite_time_blowup_proved": False,
                "route_decision": "PACKET_MASK_JOIN_INSUFFICIENT",
                "action_boundary": "diagnostic boundary",
                "direct_stretch_status": "source_truth_or_direct_stretch_unavailable",
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
            "--replay-sprint55-lagrangian-action-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    manifest = json.loads((out_dir / "ns_diagnostic_manifest.json").read_text(encoding="utf-8"))

    assert checks["route_decision"] == "PACKET_MASK_JOIN_INSUFFICIENT"
    assert checks["source_truth_loaded"] is False
    assert checks["material_parent_lineage_recomputed"] is False
    assert checks["packet_local_masks_loaded"] is False
    assert checks["sprint55_lagrangian_action_replay_promotes"] is False
    assert checks["clay_promotion"] is False
    assert checks["navier_stokes_promotion"] is False
    assert checks["pass"] is False
    assert manifest["receipt_alignment"] == "DASHI.Physics.Closure.ClaySprintFiftyFiveLagrangianStretchActionAuditReceipt"
    assert manifest["outputs"]["sprint55_lagrangian_action_summary"] is not None
    assert manifest["outputs"]["lagrangian_stretch_action_csv"] is not None
    assert manifest["outputs"]["packet_action_hysteresis_csv"] is not None
    assert manifest["outputs"]["lagrangian_action_by_shell_csv"] is not None
    assert manifest["clay_promotion"] is False
    assert manifest["navier_stokes_promotion"] is False
