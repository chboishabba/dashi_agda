from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_sprint58_normalized_action_inflation_replay(tmp_path: Path) -> None:
    source_dir = tmp_path / "gpu_sprint58"
    source_dir.mkdir()
    source = source_dir / "ns_sprint58_normalized_action_inflation_summary.json"
    (source_dir / "ns_normalized_action_inflation_packets.csv").write_text(
        "run,time,dt,K,packet_id,packet_raw_signed_stretch_action,packet_raw_positive_stretch_action,packet_enstrophy,covered_enstrophy,global_enstrophy,packet_enstrophy_fraction_of_covered,packet_enstrophy_fraction_of_global,packet_normalized_signed_action,packet_normalized_positive_action,covered_ratio_positive_action,global_ratio_positive_action,packet_to_covered_ratio_inflation,packet_to_global_ratio_inflation,low_enstrophy_denominator,inflation_candidate\n"
        "run0,0.1,0.01,4,K4_cell1,1,1,2,10,100,0.2,0.02,0.005,0.005,0.001,0.0001,5,50,false,false\n",
        encoding="utf-8",
    )
    (source_dir / "ns_normalized_action_inflation_by_time.csv").write_text(
        "run,time,dt,requested_packet_count,available_packet_count,packet_raw_positive_stretch_action,covered_raw_positive_stretch_action,global_raw_positive_stretch_action,packet_enstrophy_sum,covered_enstrophy,global_enstrophy,packet_normalized_positive_action_sum,covered_ratio_positive_action,global_ratio_positive_action,sum_ratios_over_ratio_of_sums_covered,sum_ratios_over_ratio_of_sums_global,low_enstrophy_packet_count,inflation_candidate_count,normalization_gap_status\n"
        "run0,0.1,0.01,1,1,1,2,3,2,10,100,0.005,0.001,0.0001,5,50,0,0,NORMALIZATION_GAP_BELOW_THRESHOLD\n",
        encoding="utf-8",
    )
    source.write_text(
        json.dumps(
            {
                "contract": "ns_sprint58_normalized_action_inflation_artifact",
                "diagnostic_mode": "sprint58_normalized_packet_action_inflation",
                "time_window_count": 1,
                "packet_inflation_row_count": 1,
                "packet_normalized_positive_action_total": 0.005,
                "covered_ratio_positive_action_total": 0.001,
                "global_ratio_positive_action_total": 0.0001,
                "sum_ratios_over_ratio_of_sums_covered": 5.0,
                "sum_ratios_over_ratio_of_sums_global": 50.0,
                "packet_raw_positive_stretch_action_total": 1.0,
                "covered_raw_positive_stretch_action_total": 2.0,
                "global_raw_positive_stretch_action_total": 3.0,
                "packet_enstrophy_total": 2.0,
                "covered_enstrophy_total": 10.0,
                "global_enstrophy_total": 100.0,
                "low_enstrophy_denominator_count": 0,
                "low_enstrophy_denominator_fraction": 0.0,
                "inflation_candidate_count": 0,
                "inflation_candidate_fraction": 0.0,
                "max_packet_to_covered_ratio_inflation": 5.0,
                "max_packet_to_global_ratio_inflation": 50.0,
                "low_enstrophy_fraction_threshold": 0.001,
                "inflation_factor_threshold": 10.0,
                "packet_action_reconstruction_proved": False,
                "normalized_action_additivity_proved": False,
                "denominator_inflation_theorem_proved": False,
                "weighted_packet_action_summability_proved": False,
                "physical_bridge_proved": False,
                "stretch_absorption_proved": False,
                "no_finite_time_blowup_proved": False,
                "route_decision": "NORMALIZED_ACTION_INFLATION_BELOW_THRESHOLD",
                "promotion_status": "NO_PROMOTION_SPRINT58_NORMALIZED_ACTION_INFLATION_DIAGNOSTIC",
                "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFiftyEightNormalizedActionInflationReceipt",
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
            "--replay-sprint58-normalized-action-inflation-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    manifest = json.loads((out_dir / "ns_diagnostic_manifest.json").read_text(encoding="utf-8"))

    assert checks["route_decision"] == "NORMALIZED_ACTION_INFLATION_BELOW_THRESHOLD"
    assert checks["sprint58_normalized_action_inflation_replay_promotes"] is False
    assert checks["source_truth_loaded"] is False
    assert checks["packet_local_masks_loaded"] is False
    assert checks["normalized_action_inflation_recomputed"] is False
    assert checks["clay_promotion"] is False
    assert checks["navier_stokes_promotion"] is False
    assert checks["pass"] is False
    assert manifest["diagnostic_mode"] == "sprint58_normalized_action_inflation_replay_from_gpu_summary"
    assert manifest["outputs"]["normalized_action_inflation_packets_csv"] is not None
    assert manifest["outputs"]["normalized_action_inflation_by_time_csv"] is not None
    assert manifest["clay_promotion"] is False
