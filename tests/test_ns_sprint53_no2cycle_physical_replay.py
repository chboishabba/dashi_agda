from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_sprint53_no2cycle_physical_replay_writes_manifest_and_checks(tmp_path: Path) -> None:
    source_dir = tmp_path / "gpu_sprint53"
    source_dir.mkdir()
    source = source_dir / "ns_sprint53_no2cycle_summary.json"
    (source_dir / "ns_no2cycle_physical_amplitude.csv").write_text(
        "run,time,K,cycle_id,Rplus_t,Rminus_t,N_t,Rplus_t_next,Rminus_t_next,N_t_next,delta_N,abs_delta_N,weighted_abs_delta_N,proxy_failed,amplitude_small,physical_amplitude_small,packet_confidence,parent_relation,dt,save_every\n"
        "run0,0.2,4,cycle_1,10,8,2,12,9,3,1,1,4,true,true,true,0.9,cross_shell_parent,0.01,10\n",
        encoding="utf-8",
    )
    (source_dir / "ns_no2cycle_cadence_comparison.csv").write_text(
        "run,dt,save_every,no2cycle_proxy_failure_count,physical_large_cycle_count,physical_small_cycle_fraction,weighted_physical_cycle_amplitude_total,sigma_physical_cycle_fit,does_physical_cycle_gate_close\n"
        "run0,0.01,10,1,0,1,4,0.6,true\n",
        encoding="utf-8",
    )
    (source_dir / "ns_net_residue_physical_lyapunov.csv").write_text(
        "run,K,time,N_t,N_t_next,delta_N,abs_delta_N,weighted_abs_delta_N,q_net_residue_proxy,q_sqrt2,does_net_residue_contract\n"
        "run0,4,0.2,2,3,1,1,4,1.5,2.1,false\n",
        encoding="utf-8",
    )
    source.write_text(
        json.dumps(
            {
                "contract": "ns_sprint53_no2cycle_physical_artifact",
                "diagnostic_mode": "sprint53_no2cycle_physical_amplitude_from_material_residue",
                "physical_no2cycle_row_count": 1,
                "physical_amplitude_row_count": 1,
                "no2cycle_candidate_count": 1,
                "no2cycle_proxy_failure_count": 1,
                "physical_no2cycle_failure_count": 1,
                "physical_large_cycle_count": 0,
                "physical_amplitude_small_failure_count": 1,
                "physical_small_cycle_fraction": 1.0,
                "physical_amplitude_small_failure_fraction": 1.0,
                "weighted_physical_cycle_amplitude_total": 4.0,
                "sigma_physical_cycle_fit": 0.6,
                "does_physical_no2cycle_amplitude_gate_close": True,
                "does_physical_cycle_gate_close": True,
                "does_physical_cycle_summability_gate_close": True,
                "route_decision": "NS_SOURCE_BUDGET_PHYSICAL_NO2CYCLE_ROUTE_ALIVE_DIAGNOSTIC",
                "physical_no2cycle_amplitude_proved": False,
                "weighted_physical_no2cycle_amplitude_summability_proved": False,
                "physical_bridge_proved": False,
                "stretch_absorption_proved": False,
                "no_finite_time_blowup_proved": False,
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
            "--replay-sprint53-no2cycle-physical-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    manifest = json.loads((out_dir / "ns_diagnostic_manifest.json").read_text(encoding="utf-8"))

    assert checks["does_physical_cycle_gate_close"] is True
    assert checks["route_decision"] == "NS_SOURCE_BUDGET_PHYSICAL_NO2CYCLE_ROUTE_ALIVE_DIAGNOSTIC"
    assert checks["material_parent_lineage_recomputed"] is False
    assert checks["sprint53_no2cycle_physical_replay_promotes"] is False
    assert checks["clay_promotion"] is False
    assert checks["navier_stokes_promotion"] is False
    assert checks["pass"] is False
    assert manifest["receipt_alignment"] == "DASHI.Physics.Closure.ClaySprintFiftyThreeNo2CyclePhysicalAmplitudeReceipt"
    assert manifest["outputs"]["no2cycle_physical_amplitude_csv"] is not None
    assert manifest["outputs"]["no2cycle_cadence_comparison_csv"] is not None
    assert manifest["outputs"]["net_residue_physical_lyapunov_csv"] is not None
