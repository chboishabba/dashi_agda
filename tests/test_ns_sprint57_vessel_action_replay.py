from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_sprint57_vessel_action_replay_writes_manifest_and_checks(tmp_path: Path) -> None:
    source_dir = tmp_path / "gpu_sprint57"
    source_dir.mkdir()
    source = source_dir / "ns_sprint57_vessel_action_reconciliation_summary.json"
    (source_dir / "ns_vessel_action_reconciliation_by_time.csv").write_text(
        "run,time,dt,N,save_every,requested_packet_count,available_packet_count,covered_voxel_count,domain_voxel_count,coverage_fraction,double_count_voxel_count,double_count_fraction,global_raw_positive_stretch_action,global_raw_net_stretch_action,covered_raw_positive_stretch_action,covered_raw_net_stretch_action,packet_raw_positive_stretch_action,packet_raw_net_stretch_action,global_normalized_positive_action,global_normalized_net_action,packet_normalized_positive_action,packet_normalized_net_action,epsilon_raw_positive_vs_global,epsilon_raw_net_vs_global,epsilon_raw_positive_vs_covered,epsilon_raw_net_vs_covered,epsilon_normalized_positive_vs_global,epsilon_normalized_net_vs_global,partition_status\n"
        "run0,0.1,0.01,64,10,2,2,10,262144,0.1,0,0,10,2,1,0.5,1,0.5,0.01,0.002,0.01,0.002,-0.9,-0.75,0,0,0,0,packet_union_reconstructed_from_K_cell_geometry\n",
        encoding="utf-8",
    )
    (source_dir / "ns_vessel_action_reconciliation_summary.csv").write_text(
        "assignment_scheme,time_window_count,global_raw_positive_stretch_action_total,global_raw_net_stretch_action_total,covered_raw_positive_stretch_action_total,covered_raw_net_stretch_action_total,packet_raw_positive_stretch_action_total,packet_raw_net_stretch_action_total,global_normalized_positive_action_total,global_normalized_net_action_total,packet_normalized_positive_action_total,packet_normalized_net_action_total,epsilon_raw_positive_vs_global,epsilon_raw_net_vs_global,epsilon_raw_positive_vs_covered,epsilon_raw_net_vs_covered,epsilon_normalized_positive_vs_global,epsilon_normalized_net_vs_global,mean_coverage_fraction,max_double_count_fraction,dangerous_lineage_count,sigma_packet_local_action_fit,route_decision\n"
        "euclidean_K_cell_packet_union,1,10,2,1,0.5,1,0.5,0.01,0.002,0.01,0.002,-0.9,-0.75,0,0,0,0,0.1,0,1,-0.4,PACKET_ACTION_DOES_NOT_COVER_GLOBAL_STRETCH\n",
        encoding="utf-8",
    )
    source.write_text(
        json.dumps(
            {
                "contract": "ns_sprint57_vessel_action_reconciliation_artifact",
                "diagnostic_mode": "sprint57_global_vessel_action_reconciliation",
                "assignment_scheme": "euclidean_K_cell_packet_union",
                "time_window_count": 1,
                "global_raw_positive_stretch_action_total": 10.0,
                "global_raw_net_stretch_action_total": 2.0,
                "covered_raw_positive_stretch_action_total": 1.0,
                "covered_raw_net_stretch_action_total": 0.5,
                "packet_raw_positive_stretch_action_total": 1.0,
                "packet_raw_net_stretch_action_total": 0.5,
                "global_normalized_positive_action_total": 0.01,
                "global_normalized_net_action_total": 0.002,
                "packet_normalized_positive_action_total": 0.01,
                "packet_normalized_net_action_total": 0.002,
                "epsilon_raw_positive_vs_global": -0.9,
                "epsilon_raw_net_vs_global": -0.75,
                "epsilon_raw_positive_vs_covered": 0.0,
                "epsilon_raw_net_vs_covered": 0.0,
                "epsilon_normalized_positive_vs_global": 0.0,
                "epsilon_normalized_net_vs_global": 0.0,
                "mean_coverage_fraction": 0.1,
                "max_double_count_fraction": 0.0,
                "reconstruction_tolerance": 0.25,
                "dangerous_lineage_count": 1,
                "sigma_packet_local_action_fit": -0.4,
                "packet_local_action_gate_proved": False,
                "packet_action_reconstructs_global_stretch_proved": False,
                "ultrametric_reassignment_proved": False,
                "weighted_packet_local_action_summability_proved": False,
                "physical_bridge_proved": False,
                "stretch_absorption_proved": False,
                "no_finite_time_blowup_proved": False,
                "route_decision": "PACKET_ACTION_DOES_NOT_COVER_GLOBAL_STRETCH",
                "promotion_status": "NO_PROMOTION_SPRINT57_VESSEL_ACTION_RECONCILIATION_DIAGNOSTIC",
                "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftySevenVesselActionReconciliationReceipt",
                "boundary": "diagnostic boundary",
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
            "--replay-sprint57-vessel-action-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    manifest = json.loads((out_dir / "ns_diagnostic_manifest.json").read_text(encoding="utf-8"))

    assert checks["route_decision"] == "PACKET_ACTION_DOES_NOT_COVER_GLOBAL_STRETCH"
    assert checks["sprint57_vessel_action_replay_promotes"] is False
    assert checks["source_truth_loaded"] is False
    assert checks["material_parent_lineage_recomputed"] is False
    assert checks["packet_local_masks_loaded"] is False
    assert checks["global_vessel_action_recomputed"] is False
    assert checks["clay_promotion"] is False
    assert checks["navier_stokes_promotion"] is False
    assert checks["pass"] is False
    assert manifest["diagnostic_mode"] == "sprint57_vessel_action_replay_from_gpu_summary"
    assert manifest["receipt_alignment"] == "DASHI.Physics.Closure.ClaySprintFiftySevenVesselActionReconciliationReceipt"
    assert manifest["outputs"]["sprint57_vessel_action_summary"] is not None
    assert manifest["outputs"]["vessel_action_reconciliation_by_time_csv"] is not None
    assert manifest["outputs"]["vessel_action_reconciliation_summary_csv"] is not None
    assert manifest["clay_promotion"] is False
    assert manifest["navier_stokes_promotion"] is False
