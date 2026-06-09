from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_signed_ternary_flip_replay_writes_contract_manifest_and_checks(tmp_path: Path) -> None:
    source_dir = tmp_path / "gpu_sprint51"
    source_dir.mkdir()
    source = source_dir / "ns_signed_ternary_flip_summary.json"
    flip = source_dir / "ns_cross_shell_flip_balance.csv"
    net = source_dir / "ns_net_ternary_lyapunov.csv"
    bt = source_dir / "ns_bt_signed_flip_decay.csv"
    no2cycle = source_dir / "ns_no2cycle_diagnostic.csv"

    with flip.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "K_parent",
                "K_child",
                "delta_K",
                "cross_minus_to_plus",
                "cross_plus_to_minus",
                "cross_minus_to_zero",
                "cross_plus_to_zero",
                "cross_zero_to_plus",
                "cross_zero_to_minus",
                "signed_flip_imbalance",
                "absolute_flip_imbalance",
                "net_residue_N",
                "BT_distance_proxy",
                "parent_confidence_mass_weighted_mean",
                "row_count",
            ],
        )
        writer.writeheader()
        writer.writerow(
            {
                "K_parent": "1",
                "K_child": "4",
                "delta_K": "3",
                "cross_minus_to_plus": "40",
                "cross_plus_to_minus": "38",
                "cross_minus_to_zero": "0",
                "cross_plus_to_zero": "0",
                "cross_zero_to_plus": "0",
                "cross_zero_to_minus": "0",
                "signed_flip_imbalance": "2",
                "absolute_flip_imbalance": "2",
                "net_residue_N": "2",
                "BT_distance_proxy": "3",
                "parent_confidence_mass_weighted_mean": "0.5",
                "row_count": "2",
            }
        )
    net.write_text(
        "time,K,K_next,net_residue_N,net_residue_N_next,N_next_minus_N,q_proxy,source_proxy,weighted_plus,weighted_minus,does_net_residue_decay\n"
        "0.1,4,5,2,1,-1,0.5,0,40,38,true\n",
        encoding="utf-8",
    )
    bt.write_text(
        "BT_distance_proxy,cross_minus_to_plus,cross_plus_to_minus,signed_flip_imbalance,absolute_flip_imbalance,paired_flip_flow,imbalance_fraction_of_paired_flow,eta_signed_flip_by_p,does_signed_flip_decay\n"
        "3,40,38,2,2,78,0.02564102564102564,0.6,true\n",
        encoding="utf-8",
    )
    no2cycle.write_text(
        "first_time,second_time,first_child_packet_id,second_child_packet_id,first_transition,second_transition,first_weighted_mass,second_weighted_mass,cycle_mass_ratio,does_no2cycle_hold\n",
        encoding="utf-8",
    )
    source.write_text(
        json.dumps(
            {
                "contract": "ns_signed_ternary_flip_artifact",
                "diagnostic_mode": "sprint51_signed_ternary_flip_from_material_parent_table",
                "input_table_row_count": 2,
                "cross_shell_flip_balance_row_count": 1,
                "bt_signed_flip_decay_row_count": 1,
                "net_ternary_lyapunov_row_count": 1,
                "no2cycle_diagnostic_row_count": 0,
                "ternary_involution_semantics": "minus and plus are treated as an involutive pair",
                "BT_distance_proxy": "abs(K_child - K_parent)",
                "BT_distance_proxy_boundary": "diagnostic proxy only; not theorem-grade BT metric",
                "classification_field_used_for_source_kind": False,
                "weighted_cross_minus_to_plus": 40.0,
                "weighted_cross_plus_to_minus": 38.0,
                "signed_flip_imbalance": 2.0,
                "absolute_flip_imbalance": 2.0,
                "paired_cross_flip_flow": 78.0,
                "signed_flip_imbalance_fraction_of_paired_flow": 0.02564102564102564,
                "does_signed_flip_balance": True,
                "eta_signed_flip_by_p": 0.6,
                "does_signed_flip_decay": True,
                "q_net_residue_proxy": 0.5,
                "does_net_residue_decay": True,
                "no2cycle_candidate_count": 0,
                "no2cycle_failure_count": 0,
                "does_no2cycle_hold": True,
                "route_decision": "SIGNED_FLIP_BALANCED_ROUTE_ALIVE",
                "signed_source_summability_proved": False,
                "bt_signed_decay_theorem_proved": False,
                "net_residue_lyapunov_proved": False,
                "no_persistent_two_cycle_proved": False,
                "clay_promotion": False,
                "navier_stokes_promotion": False,
                "promotion_status": "NO_PROMOTION_SIGNED_TERNARY_FLIP_DIAGNOSTIC",
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
            "--replay-signed-ternary-flip-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    replay_summary = json.loads((out_dir / "ns_signed_ternary_flip_summary.json").read_text(encoding="utf-8"))
    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    manifest = json.loads((out_dir / "ns_diagnostic_manifest.json").read_text(encoding="utf-8"))
    replay_flip = list(csv.DictReader((out_dir / "ns_cross_shell_flip_balance.csv").open(newline="", encoding="utf-8")))

    assert replay_summary["route_decision"] == "SIGNED_FLIP_BALANCED_ROUTE_ALIVE"
    assert checks["weighted_cross_minus_to_plus"] == 40.0
    assert checks["weighted_cross_plus_to_minus"] == 38.0
    assert checks["signed_flip_imbalance_fraction_of_paired_flow"] == 0.02564102564102564
    assert checks["material_parent_lineage_recomputed"] is False
    assert checks["signed_ternary_flip_replay_promotes"] is False
    assert checks["clay_promotion"] is False
    assert checks["navier_stokes_promotion"] is False
    assert checks["pass"] is False
    assert replay_flip[0]["absolute_flip_imbalance"] == "2"
    assert manifest["receipt_alignment"] == "DASHI.Physics.Closure.ClaySprintFiftyOneSignedTernaryFlipAuditReceipt"
    assert manifest["outputs"]["bt_signed_flip_decay_csv"] is not None
    assert manifest["outputs"]["no2cycle_diagnostic_csv"] is not None
    assert manifest["navier_stokes_promotion"] is False
